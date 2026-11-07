-- Prove2me | solution 1 for NaturalProofs.prob_equiv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:30.150647+00:00
-- url     : https://prove2.me/submissions/1bf49496-57a4-4f81-aad3-067ebd4ad81f

module
public import Mathlib
public import Definitions.Def_NaturalProofs_Prob

set_option autoImplicit true
@[expose] public section
public section
open NaturalProofs
open Finset
variable {Ω Ω' A B I X : Type} [Fintype Ω] [Fintype Ω'] [Fintype A] [Fintype B] [Fintype I]
  [Fintype X]
namespace NaturalProofs
theorem _root_.solution (e : Ω ≃ Ω') (p : Ω' → Bool) : prob (fun ω => p (e ω)) = prob p := by
  simp only [prob]
  rw [Equiv.sum_comp e (fun ω' => ind (p ω')), Fintype.card_congr e]
end NaturalProofs
