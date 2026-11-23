-- Prove2me | solution 1 for KernelRank.eq_zero_of_sum_expPoly_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T02:34:24.905241+00:00
-- url     : https://prove2.me/submissions/75cf2d1c-8e25-42f4-a1bd-94bdc531077e

import Mathlib
import Definitions.Def_KernelRankLean_ExpPoly
import Theorems.Thm_KernelRank_expPoly_zero
import Theorems.Thm_KernelRank_iterate_sum_shiftDeriv_eq_zero
import Theorems.Thm_KernelRank_shiftDeriv_self
import Theorems.Thm_KernelRank_eq_zero_of_iterate_shiftDeriv_eq_zero
import Theorems.Thm_KernelRank_eq_zero_of_eval_ofReal_eq_zero
attribute [local simp] KernelRank.expPoly_zero

set_option autoImplicit true
open Complex Polynomial
open KernelRank
namespace KernelRank
theorem _root_.solution (S : Finset ℂ) (P : ℂ → ℂ[X])
    (h : ∀ u : ℝ, 0 < u → ∑ μ ∈ S, expPoly (P μ) μ u = 0) : ∀ μ ∈ S, P μ = 0 := by
  induction S using Finset.induction_on generalizing P with
  | empty => simp
  | insert a S ha ih =>
    -- Remove the term with rate `a` by applying `d/du - a` enough times.
    have hQ := iterate_sum_shiftDeriv_eq_zero a ((P a).natDegree + 1) h
    have hQa : (shiftDeriv a a)^[(P a).natDegree + 1] (P a) = 0 := by
      have : shiftDeriv a a = derivative := funext (shiftDeriv_self a)
      rw [this]
      exact iterate_derivative_eq_zero (Nat.lt_succ_self _)
    simp only [Finset.sum_insert ha, hQa, expPoly_zero, zero_add] at hQ
    have hS : ∀ μ ∈ S, P μ = 0 := fun μ hμ =>
      eq_zero_of_iterate_shiftDeriv_eq_zero (by rintro rfl; exact ha hμ) _
        (ih (fun μ => (shiftDeriv a μ)^[(P a).natDegree + 1] (P μ)) hQ μ hμ)
    -- Then the remaining term `P a (u) · exp (a u)` vanishes, so `P a` has infinitely many roots.
    have ha0 : P a = 0 := by
      refine eq_zero_of_eval_ofReal_eq_zero fun u hu => ?_
      have := h u hu
      rw [Finset.sum_insert ha, Finset.sum_eq_zero fun μ hμ => by simp [hS μ hμ], add_zero,
        expPoly] at this
      exact (mul_eq_zero.mp this).resolve_right (exp_ne_zero _)
    intro μ hμ
    rcases Finset.mem_insert.mp hμ with rfl | hμ
    · exact ha0
    · exact hS μ hμ
end KernelRank
