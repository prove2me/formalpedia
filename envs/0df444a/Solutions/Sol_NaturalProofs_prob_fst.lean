-- Prove2me | solution 1 for NaturalProofs.prob_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:29:46.766521+00:00
-- url     : https://prove2.me/submissions/bc65f0f3-5dcf-481d-8199-f89395870124

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
theorem _root_.solution [Nonempty B] (p : A → Bool) : prob (fun ω : A × B => p ω.1) = prob p := by
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [prob, Fintype.sum_prod_type, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Fintype.card_prod, Nat.cast_mul]
  rw [← Finset.mul_sum]
  field_simp
end NaturalProofs
