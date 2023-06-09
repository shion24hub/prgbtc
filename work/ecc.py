"""
楕円曲線暗号
"""

from random import randint # 本番環境には絶対に使わない。
from unittest import TestCase

import hashlib
import hmac


P = 2 ** 256 - 2 ** 32 - 977 # secp256k1の法とする素数
A = 0 # secp256k1のa
B = 7 # secp256k1のb
N = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141
GX = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798
GY = 0x483ada7726a3c4655da4fbfc0e1108a8fd17b448a68554199c47d08ffb10d4b8

BASE58_ALPHABET = '123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz'


def hash256(s):
    '''two rounds of sha256'''
    return hashlib.sha256(hashlib.sha256(s).digest()).digest()


def encode_base58(s):
    count = 0
    for c in s:
        if c == 0:
            count += 1
        else:
            break
    
    num = int.from_bytes(s, "big")
    prefix = "1" * count
    result = ""
    while num > 0:
        num, mod = divmod(num, 58)
        result = BASE58_ALPHABET[mod] + result
    
    return prefix + result

def encode_base58_checksum(b):
    return encode_base58(b + hash256((b))[:4])

def hash160(s):
    """
    sha256 → ripemd160
    """
    return hashlib.new("ripemd160", hashlib.sha256(s).digest()).digest()


class FieldElement:
    """
    有限体
    """

    def __init__(self, num, prime):
        if num >= prime or num < 0:
            error = "Num {} not in field range 0 to {}".format(num, prime - 1)
            raise ValueError(error)
        
        self.num = num
        self.prime = prime

    def __repr__(self):
        return "FieldElement_{}({})".format(self.prime, self.num)
    
    def __eq__(self, other):
        """
        ==演算子のオーバーロード
        """

        if other is None:
            return False
        
        return self.num == other.num and self.prime == other.prime
    
    def __ne__(self, other):
        """
        !=演算子のオーバーロード
        """

        # __eq__を利用すればよい
        return not(self == other)
    
    def __add__(self, other):
        """
        +演算子のオーバーロード
        """

        if self.prime != other.prime:
            error = "Cannot add two numbers in different Fields"
            raise TypeError(error)

        num = (self.num + other.num) % self.prime
        
        return self.__class__(num, self.prime)
    
    def __sub__(self, other):
        """
        -演算子のオーバーロード
        """

        if self.prime != other.prime:
            error = "Cannot sub two numbers in different Fields"
            raise TypeError(error)
        
        num = (self.num - other.num) % self.prime

        return self.__class__(num, self.prime)

    def __mul__(self, other):
        """
        *演算子のオーバーロード
        """

        if self.prime != other.prime:
            error = "Cannot mul two numbers in different Fields"
            raise TypeError(error)
        
        num = (self.num * other.num) % self.prime

        return self.__class__(num, self.prime)
    
    def __pow__(self, exponent):
        """
        **演算子のオーバーロード
        """

        # 指数が負の場合の処理
        #アルゴリズムについては『プログラミングビットコイン』 p.17参照
        while exponent < 0:
            exponent += self.prime - 1

        # exponent %= self.prime - 1 # こちらの方が効率的
        
        num = pow(self.num, exponent, self.prime)

        return self.__class__(num, self.prime)
    
    def __truediv__(self, other):
        """
        /演算子のオーバーロード
        """

        if self.prime != other.prime:
            error = "Cannot div two numbers in different Fields"
            raise TypeError(error)
        
        inverse = pow(other.num, self.prime - 2, self.prime) # 逆元
        num = (self.num * inverse) % self.prime

        return self.__class__(num, self.prime)
    
    def __rmul__(self, coefficient):
        num = (self.num * coefficient) % self.prime
        return self.__class__(num=num, prime=self.prime)
    

class Point:
    """
    楕円曲線上の特定の点
    無限遠点の場合は、x = None, y = Noneで表す
    """
    
    def __init__(self, x, y, a, b):
        self.a = a
        self.b = b
        self.x = x
        self.y = y

        # 無限遠点の場合
        if self.x is None and self.y is None:
            return

        if self.y ** 2 != self.x ** 3 + a * x + b:
            error = "({}, {}) is not on ther curve".format(x, y)
            raise ValueError(error)
        
    def __repr__(self):
        if self.x is None:
            return 'Point(infinity)'
        elif isinstance(self.x, FieldElement):
            return 'Point({},{})_{}_{} FieldElement({})'.format(
                self.x.num, self.y.num, self.a.num, self.b.num, self.x.prime)
        else:
            return 'Point({},{})_{}_{}'.format(self.x, self.y, self.a, self.b)
        
    def __eq__(self, other):
        return self.x == other.x and self.y == other.y and self.a == other.a and self.b == other.b
    
    def __ne__(self, other):
        return not(self == other)
    
    def __add__(self, other):
        if self.a != other.a or self.b != other.b:
            error = "Points {}, {} are not on the same curve".format(self, other)
            raise TypeError(error)
        
        # selfが加法単位元である場合
        if self.x is None:
            return other
        
        # otherが加法単位元である場合
        if self.x is None:
            return self
        
        # selfとotherが垂直線の関係にある場合
        if self.x == other.x and self.y != other.y:
            return self.__class__(None, None, self.a, self.b)
        
        # self.x != other.xの場合
        if self.x != other.x:
            s = (other.y - self.y) / (other.x - self.x) # selfとotherを通る直線の傾き
            x = s ** 2 - self.x - other.x # 加算後のx座標
            y = s * (self.x - x) - self.y # 加算後のy座標

            return self.__class__(x, y, self.a, self.b)
        
        # self == otherで、y座標が0の場合（接線が垂直線である場合）
        if self == other and self.y == 0 * self.x:
            return self.__class__(None, None, self.a, self.b)
        
        # self == otherの場合
        if self == other:
            s = (3 * self.x ** 2 + self.a) / (2 * self.y)
            x = s ** 2 - 2 * self.x
            y = s * (self.x - x) - self.y

            return self.__class__(x, y, self.a, self.b)
        
    def __rmul__(self, coefficient):
        coef = coefficient
        current = self  # <1>
        result = self.__class__(None, None, self.a, self.b)  # <2>
        while coef:
            if coef & 1:  # <3>
                result += current
            current += current  # <4>
            coef >>= 1  # <5>
        return result    


class S256Field(FieldElement):
    def __init__(self, num, prime=None):
        super().__init__(num, prime=P)
    
    def __repr__(self):
        return "{:x}".format(self.num).zfill(64)
    
    def sqrt(self):
        return self ** ((P + 1) // 4)


class S256Point(Point):
    def __init__(self, x, y, a=None, b=None):
        a, b = S256Field(A), S256Field(B)

        if type(x) == int:
            super().__init__(x=S256Field(x), y=S256Field(y), a=a, b=b)
        else:
            super().__init__(x=x, y=y, a=a, b=b) # 無限遠点で初期化する場合は、x, yをそのまま渡す

    def __rmul__(self, coefficient):
        coef = coefficient % N

        return super().__rmul__(coef)
    
    def verify(self, z, sig):
        s_inv = pow(sig.s, N - 2, N)
        u = z * s_inv % N
        v = sig.r * s_inv % N
        total = u * G + v * self

        return total.x.num == sig.r
    
    def sec(self, is_compressed=True):

        if is_compressed:
            # 圧縮SECフォーマット
            if self.y.num % 2 == 0:
                # y座標が偶数のときは、x02のプレフィックス
                return b"\x02" + self.x.num.to_bytes(32, "big")
            else:
                # y座標が奇数のときは、x03のプレフィックス
                return b"\x03" + self.x.num.to_bytes(32, "big")
        else:
            # 非圧縮SECフォーマット。
            # 0x04のプレフィックスの後に、32バイトのx座標とy座標をビッグエンディアン整数として追加
            return b"\x04" + self.x.num.to_bytes(32, "big") + self.y.num.to_bytes(32, "big")
    
    @classmethod
    def parse(self, sec_bin):

        # 非圧縮SECフォーマットの場合は簡単
        if sec_bin[0] == 4:
            x = int.from_bytes(sec_bin[1:33], "big")
            y = int.from_bytes(sec_bin[33:65], "big")

            return S256Point(x=x, y=y)
        
        # 圧縮SECフォーマットの場合
        is_even = sec_bin[0] == 2
        x = S256Field(int.from_bytes(sec_bin[1:], "big"))
        
        alpha = x ** 3 + S256Field(B) # secp256k1の左辺, つまりy^2
        beta = alpha.sqrt() # y
        
        if beta.num % 2 == 0:
            even_beta = beta
            odd_beta = S256Field(P - beta.num)
        else:
            even_beta = S256Field(P - beta.num)
            odd_beta = beta
        
        if is_even:
            return S256Point(x, even_beta)
        else:
            return S256Point(x, odd_beta)
    
    def hash160(self, compressed=True):
        return hash160(self.sec(compressed))
    
    def address(self, compressed=True, testnet=False):
        h160 = self.hash160(compressed)
        if testnet:
            prefix = b"\x6f"
        else:
            prefix = b"\x00"
        
        return encode_base58_checksum(prefix + h160)
        

G = S256Point(GX, GY)


class Signature:

    def __init__(self, r, s):
        self.r = r
        self.s = s

    def __repr__(self):
        return "Signature({:x}, {:x})".format(self.r, self.s)
    
    def der(self):
        rbin = self.r.to_bytes(32, "big")
        
        # 先頭のnullバイトをすべて取り除く
        rbin = rbin.lstrip(b"\x00")

        # rbinの最上位ビットが1の場合、\x00を追加する
        if rbin[0] & 0x80:
            rbin = b"\x00" + rbin
        
        result = bytes([2, len(rbin)]) + rbin

        sbin = self.s.to_bytes(32, "big")
        # 先頭のnullバイトをすべて取り除く
        sbin = sbin.lstrip(b"\x00")

        # sbinの最上位ビットが1の場合、\x00を追加する
        if sbin[0] & 0x80:
            sbin = b"\x00" + sbin
        
        result += bytes([2, len(sbin)]) + sbin
        
        # 最後にDER署名のマーカーとそれ以降の長さの情報を足す
        return bytes([0x30, len(result)]) + result


class PrivateKey:

    def __init__(self, secret):

        self.secret = secret
        self.point = secret * G

    def hex(self):

        return "{:x}".format(self.secret).zfill(64)
    
    def sign(self, z):

        # k = randint(0, N - 1) # 危険
        k = self.deterministic_k(z)
        r = (k * G).x.num
        k_inv = pow(k, N - 2, N)
        s = (z + r * self.secret) * k_inv % N

        if s > N / 2:
            s = N - s

        return Signature(r, s)
    
    def deterministic_k(self, z):
        # 暗号論的擬似乱数
        k = b'\x00' * 32
        v = b'\x01' * 32
        if z > N:
            z -= N
        z_bytes = z.to_bytes(32, 'big')
        secret_bytes = self.secret.to_bytes(32, 'big')
        s256 = hashlib.sha256
        k = hmac.new(k, v + b'\x00' + secret_bytes + z_bytes, s256).digest()
        v = hmac.new(k, v, s256).digest()
        k = hmac.new(k, v + b'\x01' + secret_bytes + z_bytes, s256).digest()
        v = hmac.new(k, v, s256).digest()
        while True:
            v = hmac.new(k, v, s256).digest()
            candidate = int.from_bytes(v, 'big')
            if candidate >= 1 and candidate < N:
                return candidate  # <2>
            k = hmac.new(k, v + b'\x00', s256).digest()
            v = hmac.new(k, v, s256).digest()

    def wif(self, compressed=True, testnet=False):
        secret_bytes = self.secret.to_bytes(32, "big")

        # prefix
        if testnet:
            prefix = b"\xef"
        else:
            prefix = b"\x80"
        
        # suffix
        if compressed:
            suffix = b"\x01"
        else:
            suffix = b""

        return encode_base58_checksum(prefix + secret_bytes + suffix)

        