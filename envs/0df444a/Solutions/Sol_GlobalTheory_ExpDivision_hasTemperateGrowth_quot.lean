-- Prove2me | solution 1 for GlobalTheory.ExpDivision.hasTemperateGrowth_quot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:20.837731+00:00
-- url     : https://prove2.me/submissions/c7ef45b0-602c-4d56-9d39-9a1b54a8935e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdentityAsSumExpMinusOne
import Theorems.Thm_GlobalTheory_ExpDivision_hasTemperateGrowth_of_entire
import Theorems.Thm_GlobalTheory_ExpDivision_mul_quot
import Theorems.Thm_GlobalTheory_ExpDivision_differentiable_quot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ContDiff
open GlobalTheory GlobalTheory.ExpDivision
namespace GlobalTheory.ExpDivision
theorem _root_.solution (a : ℝ) : (fun t : ℝ => quot a t).HasTemperateGrowth := by
  refine hasTemperateGrowth_of_entire (differentiable_quot a) fun R => ?_
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 1).exists_bound_of_continuousOn
    (differentiable_quot a).continuous.continuousOn
  refine ⟨max C (Real.exp (|a| * R) + 1), fun z hz => ?_⟩
  by_cases h : ‖z‖ ≤ 1
  · exact (hC z (by simpa using h)).trans (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    push Not at h
    have h1 : ‖z‖ * ‖quot a z‖ ≤ Real.exp (|a| * R) + 1 := by
      rw [← norm_mul, mul_quot]
      refine (norm_sub_le _ _).trans ?_
      rw [Complex.norm_exp, norm_one]
      gcongr
      have : (Complex.I * (a * z)).re = -(a * z.im) := by simp
      rw [this]
      refine (neg_le_abs _).trans ?_
      rw [abs_mul]
      gcongr
    nlinarith [norm_nonneg (quot a z)]
end GlobalTheory.ExpDivision
