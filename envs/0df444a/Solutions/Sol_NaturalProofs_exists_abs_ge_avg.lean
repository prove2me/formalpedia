-- Prove2me | solution 1 for NaturalProofs.exists_abs_ge_avg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T08:37:21.405209+00:00
-- url     : https://prove2.me/submissions/70ab468f-85ef-4035-837c-cfa1efdc2776

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
theorem _root_.solution [Nonempty Ω] (u : Ω → ℝ) :
    ∃ ω, |∑ ω, u ω| / Fintype.card Ω ≤ |u ω| := by
  by_contra h
  push Not at h
  have h1 : |∑ ω, u ω| ≤ ∑ ω, |u ω| := Finset.abs_sum_le_sum_abs _ _
  have h2 : ∑ ω, |u ω| < ∑ _ω : Ω, |∑ ω, u ω| / Fintype.card Ω :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun ω _ => h ω)
  have hc : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_div_cancel₀ _ hc] at h2
  linarith
end NaturalProofs
