module Hello where

open import Agda.Builtin.IO using (IO)
open import Agda.Builtin.Unit using (⊤)
open import Agda.Builtin.String using (String)

data B : Set where
  t : B
  f : B

greet : B
greet = t

gre : B
gre = f

postulate putStrLn : String → IO ⊤

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

a : ⊤ -> ℕ -> ⊤
a c zero = c
a c (suc b) = a c b

