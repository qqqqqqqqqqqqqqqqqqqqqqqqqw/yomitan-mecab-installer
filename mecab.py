#!/usr/bin/env -S python3 -u

# Copyright (C) 2019 siikamiika
# Author: siikamiika
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <http://www.gnu.org/licenses/>.

from __future__ import print_function

import csv
import json
import sys
import os
import platform
import re
import shutil
import struct
import subprocess
import threading
import unicodedata
if sys.version_info[0] == 3:
    import queue
    from itertools import zip_longest
elif sys.version_info[0] == 2:
    import Queue as queue
    from itertools import izip_longest as zip_longest

DIR = os.path.realpath(os.path.dirname(__file__))


def read_stdin(length):
    if sys.version_info[0] == 3:
        return sys.stdin.buffer.read(length)
    elif sys.version_info[0] == 2:
        return sys.stdin.read(length)

def write_stdout(data):
    if sys.version_info[0] == 3:
        return sys.stdout.buffer.write(data)
    elif sys.version_info[0] == 2:
        return sys.stdout.write(data)

def flush_stdout():
    if sys.version_info[0] == 3:
        sys.stdout.buffer.flush()
    elif sys.version_info[0] == 2:
        sys.stdout.flush()


def get_message():
    raw_length = read_stdin(4)
    if not raw_length:
        sys.exit(0)
    message_length = struct.unpack('@I', raw_length)[0]
    message = read_stdin(message_length).decode('utf-8')
    return json.loads(message)


def send_message(message_content):
    encoded_content = json.dumps(message_content).encode('utf-8')
    encoded_length = struct.pack('@I', len(encoded_content))
    write_stdout(encoded_length)
    write_stdout(encoded_content)
    flush_stdout()


# Number + counter readings. UniDic reads Arabic numbers one digit per token
# (2人 -> 2/ニ 人/ニン, 10日 -> 1/イチ 0/ゼロ 日/カ). For each digit run followed
# by a counter, re-parse the number as a kanji numeral, where UniDic knows the
# irregular readings (二人 フタリ, 二十歳 ハタチ, 十日 トオカ), repair the
# number/counter allomorphs it still gets wrong (一年 イッネン, 二本 ニポン), and
# merge the run into one token. See dev/counter_readings/PLAN.md.
#
# Only for dictionaries whose `reading` is the kana form (仮名形) and whose POS
# tags are UniDic's; the repair rules don't hold for the lossy `pron` form.
COUNTER_FIX_DICTIONARIES = {'unidic-csj-202512'}
COUNTER_POS = {
    ('接尾辞', '名詞的', '助数詞'),  # 匹 日 歳 つ 枚 個 頭 羽 本
    ('接尾辞', '名詞的', '一般'),  # 人 冊
    ('名詞', '普通名詞', '助数詞可能'),  # 回 階 分 時 月 年 円 台 足 件 杯 週間 割 ヶ月
}
# A re-parse token that fuses number and counter is only a reading of the pair
# (一人 ヒトリ, 二手 フタテ, 二十歳 ハタチ) for these values and POS; anything
# else is an unrelated word (三重 ミエ, 一寸 チョット, 百足 ムカデ, 四周 シシュウ).
LEXICAL_NUMBERS = {1, 2, 20}
LEXICAL_OK_POS = {('名詞', '普通名詞'), ('名詞', '数詞')}
# Counter tokens whose UniDic reading ignores the number (日間 is always カカン:
# 十一日間 ジュウイチカカン), read as a shorter counter plus a fixed tail.
SPLIT_COUNTERS = {'日間': ('日', 'ニチ', 'カン')}
NUMBER_SEPARATORS = {'.', '．', ',', '，'}
RE_DIGITS = re.compile('^[0-9０-９]+$')
BIG_UNITS = {'十': 10, '百': 100, '千': 1000, '万': 10**4, '億': 10**8, '兆': 10**12}
KANJI_DIGITS = '〇一二三四五六七八九'
VOICELESS = set('カキクケコサシスセソタチツテトパピプペポ')
H_ROW = set('ハヒフヘホ')
H_TO_P = str.maketrans('ハヒフヘホ', 'パピプペポ')
P_TO_H = str.maketrans('パピプペポ', 'ハヒフヘホ')
UNGEMINATE = {
    'イッ': 'イチ', 'ロッ': 'ロク', 'ハッ': 'ハチ', 'ジュッ': 'ジュウ', 'ジッ': 'ジュウ',
    'ヒャッ': 'ヒャク', 'ビャッ': 'ビャク', 'ピャッ': 'ピャク',
}
# number-final form -> (geminated form, onsets before which it geminates)
GEMINATE = {
    'イチ': ('イッ', VOICELESS | H_ROW),
    'ハチ': ('ハッ', VOICELESS | H_ROW),
    'ジュウ': ('ジュッ', VOICELESS | H_ROW),
    'ロク': ('ロッ', set('カキクケコパピプペポハヒフヘホ')),
    'ヒャク': ('ヒャッ', set('カキクケコパピプペポハヒフヘホ')),
    'ビャク': ('ビャッ', set('カキクケコパピプペポハヒフヘホ')),  # 三百
    'ピャク': ('ピャッ', set('カキクケコパピプペポハヒフヘホ')),  # 六百 八百
}
# Final-digit forms that depend on the counter: digit -> ({counter: form}, default).
DIGIT_FORMS = {
    4: ({'人': 'ヨ', '時': 'ヨ', '時間': 'ヨ', '年': 'ヨ', '年間': 'ヨ', '円': 'ヨ', '月': 'シ'}, 'ヨン'),
    7: ({'月': 'シチ', '時': 'シチ', '日': 'シチ'}, 'ナナ'),
    9: ({'月': 'ク', '時': 'ク', '日': 'ク'}, 'キュウ'),
}
# After サン (3) some h-row counters take rendaku instead of p.
SAN_RENDAKU = {'本': 'ボン', '杯': 'バイ', '匹': 'ビキ', '階': 'ガイ', '軒': 'ゲン', '足': 'ゾク'}
# Keyed by the NFKC-normalized surface.
OVERRIDES = {'1日': 'イチニチ', '10分': 'ジュップン', '4人': 'ヨニン', '2割': 'ニワリ', '110番': 'ヒャクトオバン'}


def is_number_token(token):
    return token['pos1'] == '名詞' and token['pos2'] == '数詞'


def find_counter_sites(tokens):
    """Yield (start, end) of each digit run plus the counter token after it.

    The run starts on an Arabic-digit token and may continue through kanji units
    (100万, 3億5000万, 5千). Runs after a decimal point or thousands separator
    (3.5倍, 1,000人) are left alone.
    """
    i = 0
    while i < len(tokens):
        if not (is_number_token(tokens[i]) and RE_DIGITS.match(tokens[i]['source'])):
            i += 1
            continue
        j = i + 1
        while j < len(tokens) and is_number_token(tokens[j]) and (
                RE_DIGITS.match(tokens[j]['source']) or tokens[j]['source'] in BIG_UNITS):
            j += 1
        separator_before = i > 0 and tokens[i - 1]['source'] in NUMBER_SEPARATORS
        if (not separator_before and j < len(tokens)
                and (tokens[j]['pos1'], tokens[j]['pos2'], tokens[j]['pos3']) in COUNTER_POS):
            yield i, j + 1
        i = j


def number_value(surfaces):
    """'5', '000', '万' -> 50000000; handles 3億5000万 and full-width digits."""
    total, section, cur = 0, 0, 0
    for s in surfaces:
        s = unicodedata.normalize('NFKC', s)
        if s.isdigit():
            cur = cur * 10 ** len(s) + int(s)
        else:
            unit = BIG_UNITS[s]
            if unit >= 10**4:
                total += (section + cur or 1) * unit
                section = cur = 0
            else:
                section += (cur or 1) * unit
                cur = 0
    return total + section + cur


def num_to_kanji(n):
    """1234 -> 千二百三十四. Only below 10**16 (no unit above 兆)."""
    if n == 0:
        return '零'
    def under_10000(n):
        s = ''
        for val, ch in ((1000, '千'), (100, '百'), (10, '十')):
            d, n = divmod(n, val)
            if d:
                s += ('' if d == 1 else KANJI_DIGITS[d]) + ch
        return s + (KANJI_DIGITS[n] if n else '')
    out = ''
    for val, ch in ((10**12, '兆'), (10**8, '億'), (10**4, '万')):
        d, n = divmod(n, val)
        if d:
            out += under_10000(d) + ch
    return out + (under_10000(n) if n else '')


def repair_counter_reading(num, ctr, n, counter):
    """Fix number/counter allomorphs. num/ctr are katakana, n the value, counter the surface."""
    # The h/p alternation is for Sino-Japanese counters; loanwords keep their
    # onset (2ページ ニページ, 1ヘルツ イチヘルツ).
    alternates = not ('ァ' <= counter[:1] <= 'ヺ')
    # Counter-dependent final-digit forms (4/7/9).
    if n % 10 in DIGIT_FORMS:
        forms, default = DIGIT_FORMS[n % 10]
        for alt in ('ヨン', 'ヨ', 'シ', 'ナナ', 'シチ', 'キュウ', 'ク'):
            if num.endswith(alt):
                num = num[:-len(alt)] + forms.get(counter, default)
                break
    # Un-geminate before voiced / nasal / vowel onsets (イッ+ネン -> イチネン).
    for g, full in UNGEMINATE.items():
        if num.endswith(g) and ctr[:1] not in VOICELESS:
            num = num[:-len(g)] + full
            break
    # After サン: rendaku for specific counters.
    if num.endswith('サン') and counter in SAN_RENDAKU:
        ctr = SAN_RENDAKU[counter]
    # Geminate before voiceless onsets (イチ+カイ -> イッカイ, ハチ+フン -> ハップン).
    for full, (g, onsets) in GEMINATE.items():
        if num.endswith(full) and ctr[:1] in onsets and (alternates or ctr[:1] not in H_ROW):
            num = num[:-len(full)] + g
            ctr = ctr[:1].translate(H_TO_P) + ctr[1:]  # h-row counters take p after ッ (イッ+ハイ -> イッパイ)
            break
    # p-onset only survives after ッ or ン (ニ+ポン -> ニホン).
    if alternates and ctr[:1] in 'パピプペポ' and not num.endswith(('ッ', 'ン')):
        ctr = ctr[:1].translate(P_TO_H) + ctr[1:]
    return num + ctr


def join_readings(tokens):
    return ''.join(t['reading'] or '' for t in tokens)


class Mecab:
    dictionaries = {
        'ipadic': ['pos1', 'pos2', 'pos3', 'pos4', 'inflection_type', 'inflection_form', 'expression', 'reading', 'pron'],
        'ipadic-neologd': ['pos1', 'pos2', 'pos3', 'pos4', '_', '_', 'expression', 'reading', 'pron'],
        'unidic-mecab-translate': [
            'pos1', 'pos2', 'pos3', 'pos4', 'inflection_type', 'inflection_form',
            'lemma_reading', 'lemma', 'expression', 'reading', 'expression_base', 'reading_base'
        ],
        'unidic-csj-202302': [
            'pos1', 'pos2', 'pos3', 'pos4', 'inflection_type', 'inflection_form',
            'lemma_reading', 'lemma', 'expression', 'reading', 'expression_base', 'reading_base'
        ],
        # Full UniDic build (29 feature columns). Unlike the trimmed
        # unidic-mecab-translate build, this emits the kana surface form
        # (仮名形出現形, col 21) which preserves written orthography (rendaku づ/ぢ,
        # long vowels おお, etc.). `reading` is sourced from that column rather
        # than from `pron` (発音形出現形, col 10), which is lossy. Column layout
        # verified against the shipped unidic-csj-202512 build; UniDic column
        # counts/order can shift between versions, so re-count for other builds.
        'unidic-csj-202512': [
            'pos1', 'pos2', 'pos3', 'pos4', 'inflection_type', 'inflection_form',
            'lemma_reading', 'lemma', 'expression', 'pron', 'expression_base', 'pron_base',
            'word_type', 'i_type', 'i_form', 'f_type', 'f_form', 'i_con_type', 'f_con_type', 'type',
            'reading', 'reading_base', 'word_form', 'word_form_base',
            'accent_type', 'accent_con_type', 'accent_mod_type', 'lid', 'lemma_id'
        ]
    }
    skip_patt = u'[\\s\u30fb]'

    def __init__(self, dictionary_name):
        self.dictionary_name = dictionary_name
        self.dictionary = Mecab.dictionaries[dictionary_name]
        self.fix_counters = dictionary_name in COUNTER_FIX_DICTIONARIES
        args = [self.get_executable_path(), '-d', os.path.join(DIR, 'data', dictionary_name), '-r', os.path.join(DIR, 'mecabrc')]
        self.process = subprocess.Popen(
            args,
            stdout=subprocess.PIPE,
            stdin=subprocess.PIPE
        )
        self.process_output_queue = queue.Queue()

        self.stdout_thread = threading.Thread(target=self.bg_handle_stdout)
        self.stdout_thread.daemon = True
        self.stdout_thread.start()

    def get_executable_path(self):
        if os.name == 'nt':
            return self.get_nt_executable_path()
        if sys.platform == 'darwin': # macOS
            return self.get_darwin_executable_path()
        return 'mecab'

    def get_nt_executable_path(self):
        # look up from registry
        if sys.version_info[0] == 3:
            import winreg
        elif sys.version_info[0] == 2:
            import _winreg as winreg
        try:
            reg_key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, 'SOFTWARE\\MeCab', 0, winreg.KEY_READ)
            path, _ = winreg.QueryValueEx(reg_key, 'mecabrc')
            for _ in range(2):
                path = os.path.dirname(path)
            path = os.path.join(path, 'bin', 'mecab.exe')
            if os.path.isfile(path):
                return path
        except OSError:
            pass
        # look up from program files
        path = os.path.join(os.getenv("programfiles(x86)"), 'MeCab', 'bin', 'mecab.exe')
        if os.path.isfile(path):
            return path
        # assume it exists in %PATH%
        return 'mecab.exe'

    def get_darwin_executable_path(self):
        # check %PATH%
        if shutil.which('mecab') != None:
            return 'mecab'
        # assume mecab is installed via Homebrew
        if platform.processor() == 'arm':
            # use default Apple Silicon path
            return '/opt/homebrew/bin/mecab'
        # use default macOS Intel path
        return '/usr/local/bin/mecab'

    def parse(self, text):
        parsed_lines = []
        for text_line in text.splitlines():
            parsed_line = []
            for text_line_part in re.findall(u'{0}|.*?(?={0})|.*'.format(Mecab.skip_patt), text_line):
                if re.match(Mecab.skip_patt, text_line_part):
                    parsed_line.append(self.gen_dummy_output(text_line_part))
                    continue
                parsed_part = self._run([text_line_part])[0]
                if self.fix_counters:
                    parsed_part = self.fix_counter_readings(parsed_part)
                parsed_line.extend(parsed_part)
            parsed_lines.append(parsed_line)
        return parsed_lines

    def _run(self, lines):
        """Parse each line with the mecab process; return one token list per line.

        The process is persistent and answers in order, so all lines are written
        at once and the output is split on its EOS markers.
        """
        self.process.stdin.write(''.join(line + '\n' for line in lines).encode('utf-8'))
        self.process.stdin.flush()
        parsed_parts = []
        for _ in lines:
            parsed_part = []
            for output_part in iter(self.process_output_queue.get, 'EOS'):
                token = {}
                try:
                    token['source'], output_part_info = output_part.split('\t', 1)
                    # UniDic feature strings are CSV: some fields (e.g. the
                    # accent connection type on the た auxiliary) are quoted
                    # and contain internal commas, so a plain split(',') would
                    # miscount columns. Parse as CSV to keep fields aligned.
                    output_part_info_parsed = [None if i == '*'
                                               else re.sub(Mecab.skip_patt, '|', i)
                                               for i in next(csv.reader([output_part_info]))]
                    token.update(zip_longest(self.dictionary, output_part_info_parsed))
                    parsed_part.append(token)
                except Exception as e:
                    print(e, file=sys.stderr)
            parsed_parts.append(parsed_part)
        return parsed_parts

    def fix_counter_readings(self, tokens):
        """Merge each digit run + counter into one token with the right reading."""
        sites = []
        for start, end in find_counter_sites(tokens):
            n = number_value(t['source'] for t in tokens[start:end - 1])
            if n >= 10**16:
                continue
            site_tokens, tail = tokens[start:end], ''
            if site_tokens[-1]['source'] in SPLIT_COUNTERS:
                counter, counter_reading, tail = SPLIT_COUNTERS[site_tokens[-1]['source']]
                site_tokens = site_tokens[:-1] + [dict(site_tokens[-1], source=counter, reading=counter_reading)]
            sites.append((start, end, n, site_tokens, tail))
        if not sites:
            return tokens
        kanji_parses = self._run([num_to_kanji(n) + site_tokens[-1]['source'] for _, _, n, site_tokens, _ in sites])
        fixed, prev = [], 0
        for (start, end, n, site_tokens, tail), kanji_parse in zip(sites, kanji_parses):
            reading = self._counter_site_reading(site_tokens, kanji_parse, n)
            if not reading:
                continue
            fixed.extend(tokens[prev:start])
            fixed.append(self._merge_tokens(tokens[start:end], reading + tail, n))
            prev = end
        return fixed + tokens[prev:]

    def _counter_site_reading(self, site_tokens, kanji_parse, n):
        """Reading for one site, given the UniDic parse of <kanji numeral><counter>."""
        counter = site_tokens[-1]['source']
        key = unicodedata.normalize('NFKC', ''.join(t['source'] for t in site_tokens))
        if key in OVERRIDES:
            return OVERRIDES[key]
        kanji = num_to_kanji(n)
        num_tokens = [t for t in kanji_parse if is_number_token(t)]
        if ''.join(t['source'] for t in num_tokens) != kanji:
            # A token fuses number and counter. Keep the reading of a word
            # spanning the whole number (二人 フタリ, not 四十|一人 ヨンジュウヒトリ)
            # if it is a lexical irregular; otherwise read the number alone
            # with the original counter.
            first = kanji_parse[0]
            if (n in LEXICAL_NUMBERS and len(first['source']) > len(kanji)
                    and (first['pos1'], first['pos2']) in LEXICAL_OK_POS
                    and all(t['reading'] for t in kanji_parse)):
                return join_readings(kanji_parse)
            num = join_readings(self._run([kanji])[0])
            return repair_counter_reading(num, site_tokens[-1]['reading'] or '', n, counter)
        num = join_readings(num_tokens)
        ctr = join_readings(t for t in kanji_parse if not is_number_token(t))
        # The date series and native numbers come back as non-standard number
        # forms (フツ+カ, ヨウ+カ, ヒト+ツ) that the repair rules would break.
        if counter == 'つ' and n <= 10 or counter == '日' and (n <= 10 or n == 20 or n % 10 == 4):
            return num + ctr
        if counter == '日':
            # Otherwise 日 is ニチ, but UniDic still reads the end of a longer
            # number as a date (四十二日 ヨンジュウフツカ, 六十日 ロクジュウンチ).
            num, ctr = join_readings(self._run([kanji])[0]), 'ニチ'
        return repair_counter_reading(num, ctr, n, counter)

    def _merge_tokens(self, tokens, reading, n):
        # The expression is the surface as written (２５人, not 二十五人), so
        # the reading goes over the digits.
        surface = ''.join(t['source'] for t in tokens)
        merged = self.gen_dummy_output(surface)
        # Yomitan passes `lemma` on to its API clients. asbplayer colors a
        # token by its lemma's learning status, and nothing has 2人 as a
        # lemma, so use the kanji of the first non-zero digit (2人 -> 二,
        # 16本 -> 一), which a learner knows. Before merging, Yomitan's own
        # digit+counter tokens carried a digit lemma too.
        leading_digit = next((d for d in str(n) if d != '0'), '0')
        merged.update({
            'pos1': '名詞', 'pos2': '数詞',
            'expression': surface, 'expression_base': surface, 'lemma': KANJI_DIGITS[int(leading_digit)],
            'reading': reading, 'reading_base': reading,
            'pron': reading, 'pron_base': reading,
        })
        return merged

    def gen_dummy_output(self, text):
        output = {'source': text}
        for key in self.dictionary:
            if key not in output:
                output[key] = None
        return output

    def bg_handle_stdout(self):
        for line in iter(self.process.stdout.readline, b''):
            self.process_output_queue.put(line.decode('utf-8').strip())
        self.process.stdout.close()


class MecabOrchestrator:
    def __init__(self):
        self.mecabs = {}
        self.start_mecabs()

    def parse(self, text, dictionaries=None, retry=True):
        try:
            output = {}
            if not dictionaries:
                for mecab_name in self.mecabs:
                    output[mecab_name] = self.mecabs[mecab_name].parse(text)
            else:
                for dictionary_name in dictionaries:
                    output[dictionary_name] = self.mecabs[dictionary_name].parse(text)
            return output
        except Exception as e:
            print(e, file=sys.stderr)
            if retry:
                self.reload_mecabs()
                return self.parse(text, dictionaries, False)
            raise

    def reload_mecabs(self):
        self.stop_mecabs()
        self.start_mecabs()

    def stop_mecabs(self):
        for mecab_name in list(self.mecabs):
            mecab = self.mecabs[mecab_name]
            mecab.process.kill()
            del self.mecabs[mecab_name]

    def start_mecabs(self):
        for dictionary_name in Mecab.dictionaries:
            if os.path.isdir(os.path.join(DIR, 'data', dictionary_name)):
                self.mecabs[dictionary_name] = Mecab(dictionary_name)


def main():
    mecabs = MecabOrchestrator()
    while True:
        msg = get_message()
        if msg['action'] == 'get_version':
            send_message({
                'sequence': msg['sequence'],
                'data': {'version': 1},
            })
        elif msg['action'] == 'parse_text':
            text = msg['params']['text']
            dictionaries = msg['params'].get('dictionaries')
            response = mecabs.parse(text, dictionaries)
            send_message({
                'sequence': msg['sequence'],
                'data': response,
            })

if __name__ == '__main__':
    main()
