{-# OPTIONS --cubical --safe #-}

module Test where

open import Cubical.Core.Everything         using (_≡_; Level; Type; Σ; _,_; fst; snd; _≃_; ~_)
open import Cubical.Foundations.Prelude     using (refl; sym; _∙_; cong; transport; subst; funExt; transp; I; i0; i1)
open import Cubical.Foundations.Function    using (_∘_)
open import Cubical.Foundations.Univalence  using (ua)
open import Cubical.Foundations.Isomorphism using (iso; Iso; isoToPath; section; retract)

open import Data.Bool.Base using (Bool; true; false; _∧_)
open import Data.Nat.Base  using (ℕ; zero; suc)
open import Data.Product   using (_×_; proj₁; proj₂)

natrec : (P : ℕ → Type) → P 0 → ((n : ℕ) → P n → P (suc n)) → (n : ℕ) → P n
natrec P z s zero    = z
natrec P z s (suc n) = s n (natrec P z s n)

_+_ : ℕ → ℕ → ℕ
_+_ = λ m → λ n → natrec (λ _ → ℕ) n (λ _ → suc) m

0=0 : 0 ≡ 0
0=0 = refl

suc=suc : (m n : ℕ) → m ≡ n → suc m ≡ suc n
suc=suc m n e = cong suc e

0+n=n : (n : ℕ) → 0 + n ≡ n
0+n=n = natrec (λ k → 0 + k ≡ k) 0=0 (λ n e → suc=suc n n e)

n=0+n : (n : ℕ) → n + 0 ≡ n
n=0+n = natrec (λ k → k + 0 ≡ k) 0=0 λ n e → suc=suc (n + 0) n e

