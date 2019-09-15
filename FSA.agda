module FSA where

open import Data.List

-- example 1 on https://www.cs.odu.edu/~zeil/cs390/latest/Public/fsa/index.html
-- Q is a finite set of states;
-- Σ is a finite input alphabet;
-- q0∈Q is the initial state;
-- A⊆Q is the set of accepting states; in this case implemented as a function
-- δ:Q×Σ→Q is the transition function.

-- alphabet
data Σ : Set where
  a : Σ
  b : Σ

-- states
data Q : Set where
  A : Q
  B : Q
  C : Q

δ : Q → Σ → Q
δ A a = B
δ A b = C
δ B a = B
δ B b = B
δ C a = C
δ C b = C

data accepts? : Set where
  accept : accepts?
  reject : accepts?

-- can we collapse this into one definition?

data start? : Set where
  initial : start?
  not-initial : start?

q₀ : Q
q₀ = A

accept? : Q → accepts?
accept? A = reject
accept? B = accept
accept? C = reject

evalMachine : List Σ → start? → Q → accepts?
evalMachine [] initial q = reject
evalMachine [] not-initial q = accept? q
evalMachine (x ∷ xs) initial q = evalMachine xs not-initial (δ q₀ x)
evalMachine (x ∷ xs) not-initial q = evalMachine xs not-initial (δ q x)

--testing

tryme : List Σ
tryme = a ∷ b ∷ []

flail = b ∷ tryme
failed = evalMachine flail initial A

asdf = evalMachine tryme initial A
fdsa = evalMachine (a ∷ []) initial A

-- ok, now how to prove this machine only accepts strings starting with A?
