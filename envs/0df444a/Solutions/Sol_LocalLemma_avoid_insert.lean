-- Prove2me | solution 1 for LocalLemma.avoid_insert
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:21:18.859876+00:00
-- url     : https://prove2.me/submissions/125caf1a-8f05-4e82-b168-feb617194c6f

module
public import Mathlib
public import Definitions.Def_LocalLemmaLib_Coin
public import Definitions.Def_LocalLemmaLib_LocalLemma

set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory ProbabilityTheory
open LocalLemma
namespace LocalLemma
theorem _root_.solution {Ω : Type*} {n : ℕ} (A : Fin n → Set Ω) (S : Finset (Fin n)) (j : Fin n) :
    avoid A (insert j S) = avoid A S \ A j := by
  ext ω; simp [avoid, and_comm]
end LocalLemma
