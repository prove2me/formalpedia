-- Prove2me | solution 1 for GlobalTheory.finrank_mul_abs_norm_rpow_le_sum_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:44.887294+00:00
-- url     : https://prove2.me/submissions/a08a4d2e-34dc-4765-9cf3-e2ae13485d2d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution (x : K) :
    (finrank ℚ K : ℝ) * |((Algebra.norm ℚ x : ℚ) : ℝ)| ^ (2 / (finrank ℚ K : ℝ))
      ≤ ∑ σ : K →+* ℂ, ‖σ x‖ ^ 2 := by
  have h := finrank_mul_abs_norm_rpow_le_sum (x ^ 2)
  simp only [map_pow, norm_pow, Rat.cast_pow, abs_pow] at h
  rwa [div_eq_mul_inv, Real.rpow_mul (abs_nonneg _), Real.rpow_two]
end GlobalTheory
