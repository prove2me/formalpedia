-- Prove2me | solution 1 for NaturalProofs.prob_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:36:54.940199+00:00
-- url     : https://prove2.me/submissions/c728e508-9efb-4afb-b4e1-c6fb4cb38421

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
theorem _root_.solution [Nonempty A] (p : B → Bool) : prob (fun ω : A × B => p ω.2) = prob p := by
  have hA : (Fintype.card A : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [prob, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp
end NaturalProofs
