-- Prove2me | solution 1 for GroundTheory.Automorphic.GodementJacquet.eq_of_laurent_div_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T00:06:36.892285+00:00
-- url     : https://prove2.me/submissions/1af17413-4c6a-4256-beea-6f87ba3f1c69

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJLaurentIdeal
import Theorems.Thm_GroundTheory_Automorphic_GodementJacquet_dvd_of_inv_eq_laurent_div

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.GodementJacquet
open Polynomial
namespace GroundTheory.Automorphic.GodementJacquet
theorem _root_.solution {P P' : ℂ[X]} (hP : P.eval 0 = 1) (hP' : P'.eval 0 = 1)
    (h : ∀ R : RatFunc ℂ, (∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P) ↔
      ∃ L ∈ laurentSubalgebra, R = L / algebraMap ℂ[X] (RatFunc ℂ) P') : P = P' := by
  have h1 : P' ∣ P := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P')⁻¹).2
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP']; exact one_ne_zero) hL hLeq
  have h2 : P ∣ P' := by
    obtain ⟨L, hL, hLeq⟩ := (h (algebraMap ℂ[X] (RatFunc ℂ) P)⁻¹).1
      ⟨1, one_mem _, by rw [one_div]⟩
    exact dvd_of_inv_eq_laurent_div (by rw [hP]; exact one_ne_zero) hL hLeq
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hP
  obtain ⟨A, hA⟩ := h1
  obtain ⟨B, hB⟩ := h2
  have hBA : B * A = 1 := by
    have : P * (B * A) = P * 1 := by
      rw [mul_one, ← mul_assoc, ← hB, ← hA]
    exact mul_left_cancel₀ hP0 this
  obtain ⟨a, -, ha⟩ := Polynomial.isUnit_iff.1 (IsUnit.of_mul_eq_one_right B hBA)
  have ha1 : a = 1 := by
    have := congrArg (Polynomial.eval 0) hA
    rw [Polynomial.eval_mul, ← ha, Polynomial.eval_C, hP, hP', one_mul] at this
    exact this.symm
  rw [hA, ← ha, ha1, map_one, mul_one]
end GroundTheory.Automorphic.GodementJacquet
