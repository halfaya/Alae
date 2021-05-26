{-# OPTIONS --cubical --safe #-}

module Equality where

open import Cubical.Core.Everything         using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)
open import Cubical.Foundations.Prelude     using (refl; sym; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Bool.Base      using (Bool; true; false; _∧_)
open import Data.Nat.Base       using (ℕ; zero; suc; _+_)
open import Data.Fin            using (Fin; toℕ; fromℕ; #_; opposite) renaming (zero to fz; suc to fs)
open import Data.Product        using (_×_; proj₁; proj₂)

-- mutual recursion
data Γ : ℕ → Type
data U : {n : ℕ} → Γ n → Type

-- context (snoc list of dependent types)
data Γ where
  ε   : Γ 0
  _∙_ : {n : ℕ} → (γ : Γ n) → U γ → Γ (suc n)

tail : {n : ℕ} → Γ (suc n) → Γ n
tail (γ ∙ _) = γ

drop : {n : ℕ} → (k : ℕ) → Γ (k + n) → Γ n
drop zero    γ       = γ
drop (suc k) (γ ∙ x) = drop k γ

head : {n : ℕ} → (γ : Γ (suc n)) → U (tail γ)
head (_ ∙ A) = A

-- lookup a type in a context at position k
lookup : {n : ℕ} → (k : ℕ) → (γ : Γ (k + suc n)) → U (tail (drop k γ))
lookup k γ = head (drop k γ)

-- type universe
data U where
  nat : {n : ℕ} → {γ : Γ n} → U γ
  pi  : {n : ℕ} → {γ : Γ n} → (A : U γ) → U (γ ∙ A) → U γ

data Term : {n : ℕ} → (γ : Γ n) → U γ → Type where
--  v  : {n : ℕ} → (k : ℕ) → {γ : Γ (k + suc n)} → {A : U (tail (drop k γ))} → Term (tail (drop k γ)) A
  v  : {n : ℕ} → (k : ℕ) → {γ : Γ (k + suc n)} → {A : U (tail (drop k γ))} → Term (tail (drop k γ)) A
  tz : {n : ℕ} → {γ : Γ n} → Term γ nat -- zero
  ts : {n : ℕ} → {γ : Γ n} → Term γ nat → Term γ nat -- suc
--  tn : (P : Term nat → U) → Term (P tz) → ((n : Term nat) → Term (P n) → Term (P (ts n))) → (n : Term nat) → Term (P n) -- natrec
  tλ : {n : ℕ} → {γ : Γ n} → {A : U γ} → {B : U (γ ∙ A)} → Term (γ ∙ A) B → Term γ (pi A B)
  ta : {n : ℕ} → {γ : Γ n} → {A : U γ} → {B : U (γ ∙ A)} → Term γ (pi A B) → Term γ A → Term (γ ∙ A) B

--+1 : Term ε (pi nat nat)
--+1 = tλ {!!} --(v {n = 0} 0)

data Eq : Type where
  eq : Eq -- equal
  ne : Eq -- not equal

data Maybe (a : Type) : Type where
  nothing : Maybe a
  just    : a → Maybe a

ℕeq : ℕ → ℕ → Eq
ℕeq zero zero       = eq
ℕeq zero (suc n)    = ne
ℕeq (suc m) zero    = ne
ℕeq (suc m) (suc n) = ℕeq m n


natrec : (P : ℕ → Type) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natrec P z s zero    = z
natrec P z s (suc n) = s n (natrec P z s n)


_+'_ : ℕ → ℕ → ℕ
_+'_ = λ m → λ n → natrec (λ _ → ℕ) n (λ _ → suc) m

0=0 : 0 ≡ 0
0=0 = refl

suc=suc : (m n : ℕ) → m ≡ n → suc m ≡ suc n
suc=suc m n e = cong suc e

0+n=n : (n : ℕ) → 0 + n ≡ n
0+n=n = natrec (λ k → 0 + k ≡ k) 0=0 (λ n e → suc=suc n n e)

n=0+n : (n : ℕ) → n + 0 ≡ n
n=0+n = natrec (λ k → k + 0 ≡ k) 0=0 λ n e → suc=suc (n + 0) n e

