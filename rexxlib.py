"""
rexxlib.py — Regina REXX compatibility in Python (lowercase API)

Implements the requested built-ins in lowercase, aiming for faithful behavior:
abs, digits, form, fuzz, max, min, random, sign, trunc, compare, datatype,
symbol, b2x, c2d, c2x, d2c, d2x, x2b, x2c, x2d, center, centre, copies, format,
justify, left, right, space, abbrev, delstr, delword, find, index, insert,
lastpos, length, overlay, pos, reverse, strip, substr, subword, translate,
verify, word, wordindex, wordlength, wordpos, words, address, arg, bitand,
bitor, bitxor, condition, date, errortext, externals, linesize, queued,
sourceline, time, trace, userid, value, xrange, queue, linein, lineout, say.
"""
from __future__ import annotations

import sys
import os
import re
import getpass
import datetime as _dt
import random as _random
import builtins
import subprocess
from pathlib import Path
from collections import deque
from dataclasses import dataclass, field
from decimal import Decimal, getcontext, ROUND_DOWN, InvalidOperation
from itertools import zip_longest
from typing import Dict, List, Optional, Any

# --------------------------- helpers --------------------------- #

def _s(x) -> str:
    return x if isinstance(x, str) else str(x)


def _words(s: str) -> List[str]:
    return re.findall(r"[^\s]+", s or "")


def _pad_left(s: str, n: int, pad: str = " ") -> str:
    pad = (pad or " ")[:1]
    s = _s(s)
    n = int(n)
    if len(s) >= n:
        return s[:n]
    return s + pad * (n - len(s))


def _pad_right(s: str, n: int, pad: str = " ") -> str:
    pad = (pad or " ")[:1]
    s = _s(s)
    n = int(n)
    if len(s) >= n:
        return s[-n:]
    return pad * (n - len(s)) + s


def _cmp_with_pad(a: str, b: str, pad: str = " ") -> int:
    a, b, pad = _s(a), _s(b), (pad or " ")[:1]
    la, lb = len(a), len(b)
    m = max(la, lb)
    for i in range(m):
        ca = a[i] if i < la else pad
        cb = b[i] if i < lb else pad
        if ca != cb:
            return i + 1
    return 0


def _hex_to_bytes(x: str) -> bytes:
    x = re.sub(r"\s+", "", x or "")
    if len(x) % 2:
        x = "0" + x
    return bytes.fromhex(x) if x else b""


def _bin_to_bytes(b: str) -> bytes:
    b = re.sub(r"\s+", "", b or "")
    if not b:
        return b""
    if len(b) % 8:
        b = b.zfill(((len(b) + 7)//8)*8)
    return int(b, 2).to_bytes(len(b)//8, "big")


_file_handles = {}

# ------------------------- context/state ------------------------- #

@dataclass
class ProcedureFrame:
    variables: Dict[str, str]
    exposed_vars: List[str]

@dataclass
class RexxContext:
    # numeric environment
    digits_setting: int = 9
    form_setting: str = "scientific"  # informational
    fuzz_setting: int = 0

    # execution-ish
    address_setting: str = "COMMAND"
    trace_setting: str = "off"
    last_condition: str = ""

    # program context
    args: List[str] = field(default_factory=list)
    variables: Dict[str, str] = field(default_factory=dict)
    source_lines: List[str] = field(default_factory=list)

    # queue
    queue_store: deque = field(default_factory=deque)

    # i/o: sequential positions per file (1-based next line index)
    file_positions: Dict[str, int] = field(default_factory=dict)
    linesize_value: int = 255

    # rng
    _rng: _random.Random = field(default_factory=_random.Random, repr=False)

    # procedure stack
    procedure_stack: List[ProcedureFrame] = field(default_factory=list)

    # new settings
    exit_on_error: bool = True
    verbose: bool = True

    # Constants for file operations
    FILE_NOT_FOUND: int = 0xEEEEEEEE
    END_OF_FILE: int = 0xFFFFFFFF

    def __init__(self, exit_on_error=True, verbose=True):
        """Initialize REXX context with error handling settings"""
        self.exit_on_error = exit_on_error
        self.verbose = verbose
        self._file_positions = {}
        self._rng = _random.Random()
        self.queue_store = deque()
        self.variables = {}
        self.procedure_stack = []
        self.file_positions = {}

    # ---------------------- numeric & compare ---------------------- #
    def abs(self, x) -> str:
        getcontext().prec = self.digits_setting
        return str(Decimal(_s(x)).copy_abs())

    def digits(self, n: Optional[int] = None) -> int:
        prev = self.digits_setting
        if n is not None:
            self.digits_setting = int(n)
            getcontext().prec = self.digits_setting
        return prev if n is not None else self.digits_setting

    def form(self, s: Optional[str] = None) -> str:
        prev = self.form_setting
        if s is not None:
            self.form_setting = _s(s).lower()
        return prev if s is not None else self.form_setting

    def fuzz(self, n: Optional[int] = None) -> int:
        prev = self.fuzz_setting
        if n is not None:
            self.fuzz_setting = int(n)
        return prev if n is not None else self.fuzz_setting

    # ---------------------- numeric & compare (cont.) ---------------------- #
    def max(self, *args):
        """Rexx MAX function."""
        decs = []
        for a in args:
            try:
                decs.append(Decimal(str(a)))
            except (InvalidOperation, ValueError):
                decs.append(Decimal(0))
        return str(builtins.max(decs))

    def min(self, *args):
        """Rexx MIN function."""
        decs = []
        for a in args:
            try:
                decs.append(Decimal(str(a)))
            except (InvalidOperation, ValueError):
                decs.append(Decimal(0))
        return str(builtins.min(decs))

    def random(self, min_: int = 0, max_: int = 999, seed: Optional[int] = None) -> int:
        if seed is not None:
            self._rng.seed(int(seed))
        return self._rng.randint(int(min_), int(max_))

    def sign(self, x) -> int:
        d = Decimal(_s(x))
        return 0 if d == 0 else (1 if d > 0 else -1)

    @staticmethod
    def trunc(d, digits=0):
        """
        Trunca o número d para o número de casas decimais especificado.
        digits = 0 → retorna inteiro
        """
        try:
            d = Decimal(str(float(d)))  # força conversão via float primeiro
        except (ValueError, InvalidOperation):
            raise ValueError(f"Valor inválido para trunc(): {d}")

        if digits == 0:
            return int(d.to_integral_value(rounding=ROUND_DOWN))
        else:
            quant = Decimal("1." + "0"*digits)  # ex: digits=2 → 1.00
            return d.quantize(quant, rounding=ROUND_DOWN)

    def compare(self, a: str, b: str, pad: str = " ") -> int:
        return _cmp_with_pad(a, b, pad)

    def datatype(self, s: str, t: Optional[str] = None):
        s = _s(s)
        if t is None:
            if re.fullmatch(r"[+-]?\d+(?:\.\d+)?", s):
                return "NUM"
            if s.isalpha() and s.isupper():
                return "UPPER"
            if s.isalpha() and s.islower():
                return "LOWER"
            if s.isalpha():
                return "ALPHA"
            return "CHAR"
        t = t.upper()
        if t == "N":
            return 1 if re.fullmatch(r"[+-]?\d+(?:\.\d+)?", s) else 0
        if t == "W":
            return 1 if re.fullmatch(r"[+-]?\d+", s) else 0
        if t == "A":
            return 1 if s.isalpha() else 0
        if t == "X":
            return 1 if re.fullmatch(r"[0-9A-Fa-f]*", s) else 0
        if t == "B":
            return 1 if re.fullmatch(r"[01]*", s) else 0
        if t == "L":
            return 1 if s.islower() else 0
        if t == "U":
            return 1 if s.isupper() else 0
        return 0

    def symbol(self, name: str) -> str:
        name = _s(name)
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name):
            return "bad"
        return "var" if name in self.variables else "lit"

    # ---------------- conversions: bin/hex/char/dec ---------------- #
    def b2x(self, b: str) -> str:
        return _bin_to_bytes(b).hex().upper()

    def x2b(self, x: str) -> str:
        bs = _hex_to_bytes(x)
        return bin(int(bs.hex() or "0", 16))[2:] if bs else ""

    def c2x(self, s: str) -> str:
        return _s(s).encode("latin1", "replace").hex().upper()

    def x2c(self, x: str) -> str:
        return _hex_to_bytes(x).decode("latin1", "replace")

    def c2d(self, s: str, n: Optional[int] = None) -> int:
        b = _s(s).encode("latin1", "replace")
        if n is not None:
            b = b[: int(n)]
        return int.from_bytes(b, "big") if b else 0

    def d2c(self, n: int, length: Optional[int] = None) -> str:
        n = int(n)
        if n < 0:
            raise ValueError("d2c expects non-negative integer")
        if length is None:
            length = max(1, (n.bit_length() + 7) // 8)
        return n.to_bytes(int(length), "big").decode("latin1", "replace")

    def x2d(self, x: str) -> int:
        x = re.sub(r"\s+", "", x or "0")
        return int(x or "0", 16)

    def d2x(self, n: int, length: Optional[int] = None) -> str:
        hx = f"{int(n):X}"
        if length is not None:
            hx = hx.rjust(int(length), "0")
        return hx

    # --------------------------- strings --------------------------- #
    def center(self, s: str, width: int, pad: str = " ") -> str:
        s = _s(s)
        pad = (pad or " ")[:1]
        width = int(width)
        if len(s) >= width:
            return s[:width]
        total = width - len(s)
        left = total // 2
        right = total - left
        return pad * left + s + pad * right

    def centre(self, s: str, width: int, pad: str = " ") -> str:
        return self.center(s, width, pad)

    def copies(self, s: str, n: int) -> str:
        return _s(s) * int(n)

    def format(self, num, before: Optional[int] = None, after: Optional[int] = None, exp: Optional[int] = None) -> str:
        d = Decimal(_s(num))
        if after is not None:
            q = Decimal(1).scaleb(-int(after))
            d = d.quantize(q)
        out = f"{d}"
        if before is not None:
            parts = out.split('.')
            parts[0] = parts[0][-int(before):]
            out = '.'.join(parts)
        return out

    def justify(self, s: str, width: int) -> str:
        words = _words(s)
        width = int(width)
        if not words:
            return " " * width
        if len(words) == 1:
            return _pad_left(words[0], width)
        total_chars = sum(len(w) for w in words)
        gaps = len(words) - 1
        spaces_total = max(width - total_chars, gaps)
        base, extra = divmod(spaces_total, gaps)
        out = []
        for i, w in enumerate(words):
            out.append(w)
            if i < gaps:
                out.append(" " * (base + (1 if i < extra else 0)))
        return "".join(out)[:width]

    def left(self, s: str, n: int, pad: str = " ") -> str:
        return _pad_left(s, n, pad)

    def right(self, s: str, n: int, pad: str = " ") -> str:
        return _pad_right(s, n, pad)

    def space(self, s: str, n: int = 1) -> str:
        return (" ".join(_words(s))).replace(" ", " " * int(n))

    def abbrev(self, a: str, b: str, n: Optional[int] = None) -> int:
        a, b = _s(a), _s(b)
        n = 0 if n is None else int(n)
        return 1 if b.startswith(a) and len(a) >= n else 0

    def delstr(self, s: str, start: int, length: Optional[int] = None) -> str:
        s = _s(s)
        start = int(max(1, int(start)))
        i = int(start) - 1
        if length is None:
            return s[:i]
        return s[:i] + s[i+int(length):]

    def delword(self, s: str, n: int, length: Optional[int] = None) -> str:
        wl = _words(s)
        n = int(n)
    
        if n < 1 or n > len(wl):
            return " ".join(wl)
    
        if length is None:
            # Comportamento REXX: remove da palavra n até o final
            del wl[n-1:]
        else:
            length = int(length)
            del wl[n-1:n-1+length]
    
        return " ".join(wl)

    def pos(self, needle: str, haystack: str, start: int = 1) -> int:
        """
        REXX POS function - CORRECTED VERSION
        Finds the position of a substring within a string (1-based)
        """
        try:
            # Convert to strings safely
            needle_str = str(needle) if needle is not None else ""
            haystack_str = str(haystack) if haystack is not None else ""

            # Handle empty cases
            if not needle_str:
                return 0

            # Convert and validate start position
            start_pos = int(start) if start is not None else 1
            if start_pos < 1:
                start_pos = 1

            # Adjust for 0-based indexing (Python uses 0-based)
            start_index = start_pos - 1

            # Check if start index is beyond string length
            if start_index >= len(haystack_str):
                return 0

            # Perform the search using Python's find()
            found_index = haystack_str.find(needle_str, start_index)

            # Return 1-based position (REXX style) or 0 if not found
            return found_index + 1 if found_index >= 0 else 0

        except (ValueError, TypeError, Exception):
            # Return 0 for any errors
            return 0

    def index(self, haystack: str, needle: str, start: int = 1) -> int:
        return self.pos(needle, haystack, start)

    def find(self, haystack: str, needle: str, start: int = 1) -> int:
        return self.pos(needle, haystack, start)

    def lastpos(self, needle: str, haystack: str, start: Optional[int] = None) -> int:
        h = _s(haystack)
        if start is None:
            idx = h.rfind(_s(needle))
        else:
            idx = h.rfind(_s(needle), 0, int(start))
        return idx + 1 if idx >= 0 else 0

    def length(self, s: str) -> int:
        return len(_s(s))

    def insert(self, new, target, n=0, length=None, pad=" "):
        new = str(new)
        target = str(target)
 
        # força n ser inteiro
        try:
            n = int(n)
        except Exception:
            n = 0
        if n < 0:
            n = 0
 
        # força length ser inteiro ou None
        if length is not None:
            try:
                length = int(length)
            except Exception:
                length = len(new)
        else:
            length = len(new)
 
        pad = (pad or " ")[0]
 
        # ajusta new ao tamanho length
        if len(new) < length:
            new = new + pad * (length - len(new))
        elif len(new) > length:
            new = new[:length]
 
        # pad target se n maior que len(target)
        if n > len(target):
            target = target + pad * (n - len(target))
 
        left = target[:n]
        right = target[n:]
        return left + new + right

    def overlay(self, new: str, target: str, position: int = 1, length: Optional[int] = None, pad: str = " ") -> str:
        new, target, pad = _s(new), _s(target), (pad or " ")[:1]
        position = max(1, int(position))
        if length is None:
            length = len(new)
        left = _pad_left(target[:position-1], position-1, pad)
        right = target[position-1+int(length):]
        overlay = _pad_left(new, int(length), pad)
        return left + overlay + right

    def reverse(self, s: str) -> str:
        return _s(s)[::-1]

    def strip(self, s: str, option: str = "B", char: str = " ") -> str:
        s = _s(s)
        option = (option or "B").upper()
        char = (char or " ")[:1]
        if option == "L":
            return s.lstrip(char)
        if option == "T":
            return s.rstrip(char)
        return s.strip(char)

    def substr(self, s: str, start: int, length: Optional[int] = None, pad: str = " ") -> str:
        s = _s(s)
        start = int(start)
        if start <= 0:
            s = (pad or " ") * (1 - start) + s
            start = 1
        i = start - 1
        if length is None:
            return s[i:]
        out = s[i:i+int(length)]
        if len(out) < int(length):
            out += (pad or " ") * (int(length) - len(out))
        return out

    def subword(self, s: str, n: int, length: Optional[int] = None) -> str:
        wl = _words(s)
        n = int(n)
        if n < 1 or n > len(wl):
            return ""
        if length is None:
            return " ".join(wl[n-1:])
        return " ".join(wl[n-1:n-1+int(length)])

    def translate(self, s: str, tableout: Optional[str] = None, tablein: Optional[str] = None, pad: str = " ") -> str:
        s = _s(s)
        if tableout is None and tablein is None:
            return s.upper()
        tableout = _s(tableout or "")
        tablein = _s(tablein or "")
        tr = {tablein[i]: tableout[i] if i < len(tableout) else (pad or " ") for i in range(len(tablein))}
        return "".join(tr.get(ch, ch) for ch in s)

    def verify(self, s: str, reference: str, option: str = "", start: Any = 1) -> int:
        s = _s(s)
        reference = set(_s(reference))
        invert = (option or "").upper() == "N"
  
        # Conversão segura para inteiro do parâmetro start
        try:
            start_int = int(float(start))  # Converte para float primeiro, depois para int
        except (ValueError, TypeError):
            start_int = 1
    
        # Usar max() mas garantir que a saída seja inteiro
        start_int = max(1, start_int)
        start_int = int(start_int)  # ✅ FORÇA conversão para inteiro
    
        # Subtração segura
        start_pos = start_int - 1
  
        # Verificar se está dentro dos limites
        if start_pos >= len(s):
            return 0
    
        # Executar a verificação
        for i, ch in enumerate(s[start_pos:], start=start_pos):
            ok = ch in reference
            if invert:
                ok = not ok
            if not ok:
                return i + 1
    
        return 0

    def word(self, s: str, n: int) -> str:
        wl = _words(s)
        n = int(n)
        return wl[n-1] if 1 <= n <= len(wl) else ""

    def wordindex(self, s: str, n: int) -> int:
        s = _s(s)
        if n <= 0:
            return 0
        count = 0
        in_word = False
        for i, ch in enumerate(s):
            if ch.isspace():
                in_word = False
            else:
                if not in_word:
                    count += 1
                    if count == n:
                        return i + 1
                in_word = True
        return 0

    def wordlength(self, s: str, n: int) -> int:
        return len(self.word(s, n))

    def wordpos(self, *args):
        """
        Robust REXX-like WORDPOS method.
        Usage:
          rx.wordpos(needle, haystack)
          rx.wordpos(needle, haystack, start)
        This version auto-detects if the two first args were passed invertidos
        (e.g., wordpos(ttxt, "três")) and corrige.
        Returns 1-based position of the first matching word/phrase, or 0 if not found.
        """
        # Normalize args length
        if len(args) == 0:
            return 0
        if len(args) == 1:
            # not enough information
            return 0
    
        a = args[0]
        b = args[1]
        c = args[2] if len(args) >= 3 else None
    
        # Decide which is needle and which is haystack.
        # Heurística prática:
        #  - se b contém espaços e a não contém -> b é haystack, a é needle (caso comum)
        #  - se a contém espaços e b não contém -> a é haystack, b é needle (chamada invertida)
        #  - caso ambíguo, assumimos needle=a, haystack=b
        a_str = str(a) if a is not None else ""
        b_str = str(b) if b is not None else ""
    
        a_has_space = (" " in a_str)
        b_has_space = (" " in b_str)
    
        if b_has_space and not a_has_space:
            needle = a_str
            haystack = b_str
        elif a_has_space and not b_has_space:
            needle = b_str
            haystack = a_str
        else:
            # fallback: assume (needle, haystack)
            needle = a_str
            haystack = b_str
    
        # start safe conversion (default 1)
        try:
            start = int(c) if c is not None else 1
        except Exception:
            # If c looks like a haystack (string with spaces) then caller may have passed 3 args in some wrong order.
            # fallback to 1
            start = 1
        if start < 1:
            start = 1
    
        # Split into words (REXX-like: whitespace separator)
        lw = haystack.split()
        pw = needle.split()
        if not pw:
            return 0
    
        last_i = len(lw) - len(pw)
        i0 = start - 1
        if i0 > last_i:
            return 0
    
        for i in range(i0, last_i + 1):
            if lw[i:i+len(pw)] == pw:
                return i + 1  # 1-based
        return 0

    def words(self, s):
        """
        Retorna o número de palavras em uma string (separadas por espaço).
        """
        if s is None:
            return 0
        return len(str(s).split())

    # --------------------------- environment --------------------------- #
    def address(self, s: Optional[str] = None) -> str:
        prev = self.address_setting
        if s is not None:
            self.address_setting = _s(s)
        return prev if s is not None else self.address_setting

    def arg(self, n: Optional[int] = None) -> str | int:
        if n is None:
            return len(self.args)
        n = int(n)
        return self.args[n-1] if 1 <= n <= len(self.args) else ""

    def bitand(self, a: str, b: str) -> str:
        ba = _s(a).encode("latin1", "replace")
        bb = _s(b).encode("latin1", "replace")
        out = bytes((x & y) for x, y in zip_longest(ba, bb, fillvalue=0))
        return out.decode("latin1", "replace")

    def bitor(self, a: str, b: str) -> str:
        ba = _s(a).encode("latin1", "replace")
        bb = _s(b).encode("latin1", "replace")
        out = bytes((x | y) for x, y in zip_longest(ba, bb, fillvalue=0))
        return out.decode("latin1", "replace")

    def bitxor(self, a: str, b: str) -> str:
        ba = _s(a).encode("latin1", "replace")
        bb = _s(b).encode("latin1", "replace")
        out = bytes((x ^ y) for x, y in zip_longest(ba, bb, fillvalue=0))
        return out.decode("latin1", "replace")

    def condition(self, option: str = "C") -> str:
        """
        Versão expandida da função condition
        """
        option = option.upper()
        if option == "C":
            return self.last_condition
        elif option == "D":
            # Retorna descrição detalhada (simplificado)
            return f"Condition: {self.last_condition}"
        elif option == "I":
            # Retorna informações adicionais
            return f"Condition occurred at {_dt.datetime.now()}"
        return self.last_condition

    def date(self, option: str = "I") -> str:
        now = _dt.date.today()
        o = (option or "I").upper()
        if o == "S":
            return now.strftime("%d %b %Y")
        if o == "B":
            base = _dt.date(1, 1, 1)
            return str((now - base).days)
        return now.isoformat()

    def errortext(self, n: int) -> str:
        return f"Error {int(n)}"

    def externals(self) -> str:
        return ""  # placeholder for function registry

    def linesize(self, n: Optional[int] = None) -> int:
        prev = self.linesize_value
        if n is not None:
            self.linesize_value = int(n)
        return prev if n is not None else self.linesize_value

    def queued(self) -> int:
        return len(self.queue_store)

    def sourceline(self, n: Optional[int] = None) -> str | int:
        if n is None:
            return len(self.source_lines)
        n = int(n)
        return self.source_lines[n-1] if 1 <= n <= len(self.source_lines) else ""

    def time(self, option: str = "N") -> str:
        now = _dt.datetime.now()
        o = (option or "N").upper()
        if o == "L":
            return now.strftime("%H:%M:%S.%f")
        return now.strftime("%H:%M:%S")

    def trace(self, setting: Optional[str] = None) -> str:
        prev = self.trace_setting
        if setting is not None:
            self.trace_setting = _s(setting).lower()
        return prev if setting is not None else self.trace_setting

    def userid(self) -> str:
        return getpass.getuser() or os.getenv("USER") or os.getenv("USERNAME") or os.getenv("LOGNAME") or "user"

    def value(self, name: str, new: Optional[str] = None, selector: Optional[str] = None) -> str:
        name = _s(name)
        prev = self.variables.get(name, "")
        if new is not None:
            self.variables[name] = _s(new)
        return prev

    def xrange(self, start: str = "00", end: str = "FF") -> str:
        def _ch(v: str) -> int:
            v = _s(v)
            if len(v) == 1:
                return ord(v)
            return int(v, 16)
        a = _ch(start)
        b = _ch(end)
        if a > b:
            a, b = b, a
        return "".join(chr(i) for i in range(a, b+1))

    # ------------------------------ I/O ------------------------------ #

    def linein(self, file_path, line_number=None, exit_on_eof=True):
        """
        Read from file with improved error handling
        """
        try:
            path = Path(file_path).absolute()
            if not path.exists():
                if self.verbose:
                    print(f"File does not exist: {path}", file=sys.stderr)
                if self.exit_on_error:
                    sys.exit(1)
                return self.FILE_NOT_FOUND
            if not path.is_file():
                if self.verbose:
                    print(f"Path is not a file: {path}", file=sys.stderr)
                if self.exit_on_error:
                    sys.exit(1)
                return self.FILE_NOT_FOUND

            file_key = str(path)
            if file_key not in self._file_positions:
                self._file_positions[file_key] = 0

            target_line = (self._file_positions[file_key] + 1) if line_number is None else line_number

            with open(path, 'r') as file:
                for current_line, content in enumerate(file, 1):
                    if current_line == target_line:
                        self._file_positions[file_key] = current_line
                        return content.rstrip('\n')

                if line_number is None:
                    self._file_positions[file_key] = 0
                if exit_on_eof and self.exit_on_error:
                    sys.exit(0)
                return self.END_OF_FILE

        except Exception as e:
            if self.verbose:
                print(f"Error reading file {file_path}: {str(e)}", file=sys.stderr)
            if self.exit_on_error:
                sys.exit(1)
            return self.END_OF_FILE

    def lineout(self, file_path, string, append=True):
        """
        Write to file with error handling
        """
        try:
            with open(file_path, 'a' if append else 'w') as file:
                file.write(string + '\n')
            return 0
        except Exception as e:
            if self.verbose:
                print(f"Error writing to file {file_path}: {str(e)}", file=sys.stderr)
            if self.exit_on_error:
                sys.exit(1)
            return 1

    def rm(self, file_path):
        """
        Remove file with error handling
        """
        path = Path(file_path).absolute()
        if not path.exists():
            if self.verbose:
                print(f"File does not exist (not deleted): {path}", file=sys.stderr)
            return self.FILE_NOT_FOUND
        try:
            path.unlink()
            return 0
        except Exception as e:
            if self.verbose:
                print(f"Error deleting file {path}: {str(e)}", file=sys.stderr)
            if self.exit_on_error:
                sys.exit(1)
            return 1

    # ------------------------------ queue ------------------------------ #
    def queue(self, s: Optional[str] = None):
        if s is None:
            return self.queue_store.popleft() if self.queue_store else ""
        self.queue_store.append(_s(s))
        return len(self.queue_store)

    # ---------------------- New Implementations ---------------------- #
    def signal(self, condition: str):
        """
        Emula SIGNAL do REXX
        """
        condition = condition.upper()
        self.last_condition = condition
        
        # Condições padrão do REXX
        standard_conditions = {
            'ERROR', 'FAILURE', 'HALT', 'NOVALUE', 'NOTREADY',
            'SYNTAX', 'LOSTDIGITS', 'NOMETHOD'
        }
        
        if condition in standard_conditions:
            # Aqui você implementaria a lógica de tratamento
            # Por enquanto apenas registra a condição
            pass
            
        return condition

    def procedure(self, expose_vars: List[str] = None):
        """
        Emula PROCEDURE EXPOSE do REXX
        """
        expose_vars = expose_vars or []
        
        # Salvar estado atual das variáveis
        current_vars = self.variables.copy()
        
        # Criar novo frame
        new_frame = ProcedureFrame(
            variables=current_vars,
            exposed_vars=expose_vars
        )
        self.procedure_stack.append(new_frame)
        
        # Limpar variáveis não expostas
        if expose_vars:
            vars_to_keep = {k: v for k, v in self.variables.items() 
                          if k in expose_vars}
            self.variables = vars_to_keep
        else:
            self.variables = {}
            
        return len(self.procedure_stack)

    def end_procedure(self):
        """
        Finaliza um bloco PROCEDURE - versão FINAL corrigida
        """
        if not self.procedure_stack:
            return 0
        
        old_frame = self.procedure_stack.pop()
    
        # Salvar APENAS as variáveis expostas que existiam antes ou foram modificadas
        exposed_vars_to_keep = {}
        for var_name in old_frame.exposed_vars:
            if var_name in self.variables:
                exposed_vars_to_keep[var_name] = self.variables[var_name]
    
        # Restaurar COMPLETAMENTE o estado original das variáveis
        self.variables = old_frame.variables.copy()
    
        # Apenas atualizar as variáveis expostas que foram modificadas
        # Variáveis NOVAS (não existentes antes) são DESCARTADAS
        for var_name in exposed_vars_to_keep:
            if var_name in self.variables:  # Apenas se existia antes
                self.variables[var_name] = exposed_vars_to_keep[var_name]
    
        return len(self.procedure_stack)

    def interpret(self, code: str):
        """
        Emula INTERPRET do REXX - versão corrigida
        """
        try:
            lines = code.split(';')

            for line in lines:
                line = line.strip()
                if not line or line.startswith('/*'):  # Ignorar comentários
                    continue

                # Comando SAY
                if line.upper().startswith('SAY '):
                    message = line[4:].strip()
                    self.say(message)

                # Atribuição (var = value)
                elif '=' in line:
                    parts = line.split('=', 1)
                    var_name = parts[0].strip()
                    expr = parts[1].strip()

                    # Avaliar a expressão (simplificado)
                    if expr.isdigit():
                        value = expr
                    elif expr.startswith('"') and expr.endswith('"'):
                        value = expr[1:-1]
                    elif expr.startswith("'") and expr.endswith("'"):
                        value = expr[1:-1]
                    else:
                        # Tentar avaliar como expressão ou usar valor literal
                        value = expr

                    self.variables[var_name] = str(value)

                # Chamada de função (simplificada)
                elif '(' in line and line.endswith(')'):
                    func_name = line.split('(', 1)[0].strip()
                    if hasattr(self, func_name):
                        # Chamada simplificada sem parâmetros
                        getattr(self, func_name)()

            return 0
        except Exception as e:
            self.last_condition = f"SYNTAX: {str(e)}"
            return 1

    def raise_condition(self, condition_type: str, description: str = ""):
        """
        Sistema unificado para levantar condições
        """
        condition_type = condition_type.upper()
        self.last_condition = condition_type
        
        conditions_actions = {
            'ERROR': lambda: self._handle_error(description),
            'SYNTAX': lambda: self._handle_syntax_error(description),
            'NOVALUE': lambda: self._handle_novalue(description),
            'HALT': lambda: self._handle_halt(description),
        }
        
        if condition_type in conditions_actions:
            conditions_actions[condition_type]()
        
        return condition_type

    def _handle_error(self, description: str):
        """Tratamento interno para erro"""
        print(f"ERROR: {description}")

    def _handle_syntax_error(self, description: str):
        """Tratamento interno para erro de sintaxe"""
        print(f"SYNTAX ERROR: {description}")

    def _handle_novalue(self, var_name: str):
        """Tratamento interno para variável não definida"""
        print(f"NOVALUE: Variable {var_name} not defined")

    def _handle_halt(self, description: str):
        """Tratamento interno para halt"""
        print(f"HALT: {description}")

    def bpxwunix(self, command: str, options: str = "") -> str:
        """
        Emula BPXWUNIX (Unix command execution)
        """
        try:
            result = subprocess.run(command, shell=True, 
                                  capture_output=True, text=True)
            return result.stdout
        except Exception as e:
            self.last_condition = f"ERROR: {str(e)}"
            return ""

    def stream(self, filename: str, operation: str = "", options: str = "") -> str:
        """
        Emula STREAM function para operações de arquivo
        """
        operation = operation.upper()
        
        if operation == "C":  # Close
            if filename in _file_handles:
                _file_handles[filename]['handle'].close()
                del _file_handles[filename]
            return "READY"
        
        elif operation == "S":  # Status
            if filename in _file_handles:
                return "READY"
            return "NOTREADY"
        
        return "UNKNOWN"

    def test_rexx_functions(self):
        """
        Função de teste para verificar implementações
        """
        tests = [
            ("abs(-5)", "5"),
            ("digits()", "9"),
            ("left('hello', 10)", "hello     "),
            ("words('a b c')", "3")
        ]
        
        for test_input, expected in tests:
            try:
                result = str(eval(test_input, {}, self.__dict__))
                status = "PASS" if result == expected else "FAIL"
                print(f"{status}: {test_input} -> {result} (expected: {expected})")
            except Exception as e:
                print(f"ERROR: {test_input} -> {str(e)}")

# ------------------------- SAY instruction ------------------------- #
class Say:
    """Emula a instrução Regina REXX SAY."""
    def __call__(self, *args):
        print(" ".join(str(a) for a in args))

    def __getattr__(self, name):
        self(str(name))
        return self

# ------------------------- Concatenation Functions ------------------------- #
def concat(*args):
    """
    Emula o operador || de concatenação do REXX
    Usage: concat('a', 'b', 'c') → 'abc'
    """
    return ''.join(str(arg) for arg in args)

def c(*args):
    """
    Alias curto para concatenação
    Usage: c('a', 'b', 'c') → 'abc'
    """
    return concat(*args)

# instância global SAY
say = Say()

#---------------------------------------------------------------------#
_default = RexxContext()

# Bindings numéricos
abs = _default.abs
digits = _default.digits
form = _default.form
fuzz = _default.fuzz
max = _default.max
min = _default.min
random = _default.random
sign = _default.sign
trunc = _default.trunc
compare = _default.compare
datatype = _default.datatype
symbol = _default.symbol

# Bindings conversões
b2x = _default.b2x
c2d = _default.c2d
c2x = _default.c2x
d2c = _default.d2c
d2x = _default.d2x
x2b = _default.x2b
x2c = _default.x2c
x2d = _default.x2d

# Bindings strings
center = _default.center
centre = _default.centre
copies = _default.copies
format = _default.format
justify = _default.justify
left = _default.left
right = _default.right
space = _default.space
abbrev = _default.abbrev
delstr = _default.delstr
delword = _default.delword
find = _default.find
index = _default.index
insert = _default.insert
lastpos = _default.lastpos
length = _default.length
overlay = _default.overlay
pos = _default.pos
reverse = _default.reverse
strip = _default.strip
substr = _default.substr
subword = _default.subword
translate = _default.translate
verify = _default.verify
word = _default.word
wordindex = _default.wordindex
wordlength = _default.wordlength
wordpos = _default.wordpos
words = _default.words

# Bindings ambiente
address = _default.address
arg = _default.arg
bitand = _default.bitand
bitor = _default.bitor
bitxor = _default.bitxor
condition = _default.condition
date = _default.date
errortext = _default.errortext
externals = _default.externals
linesize = _default.linesize
queued = _default.queued
sourceline = _default.sourceline
time = _default.time
trace = _default.trace
userid = _default.userid
value = _default.value
xrange = _default.xrange

# Bindings I/O e fila
linein = _default.linein
lineout = _default.lineout
rm = _default.rm
queue = _default.queue

# Novas bindings
signal = _default.signal
procedure = _default.procedure
end_procedure = _default.end_procedure
interpret = _default.interpret
raise_condition = _default.raise_condition
bpxwunix = _default.bpxwunix
stream = _default.stream
test_rexx_functions = _default.test_rexx_functions

# Funções de concatenação (novas)
concat = concat
c = c

# SAY
say = Say()
_default.say = say
