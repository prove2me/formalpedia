-- Prove2me | solution 1 for GlobalTheory.finrank_le_sum_norm_of_isIntegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:44:43.8978+00:00
-- url     : https://prove2.me/submissions/da3d13f9-70fc-43e9-95ee-713cce12e130

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum
import Theorems.Thm_GlobalTheory_one_le_abs_norm_of_isIntegral

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
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x) (h0 : x ≠ 0) :
    (finrank ℚ K : ℝ) ≤ ∑ σ : K →+* ℂ, ‖σ x‖ := by
  refine le_trans ?_ (finrank_mul_abs_norm_rpow_le_sum x)
  have h1 : (1 : ℝ) ≤ |((Algebra.norm ℚ x : ℚ) : ℝ)| := by
    exact_mod_cast one_le_abs_norm_of_isIntegral hx h0
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) (Real.one_le_rpow h1 (by positivity))
end GlobalTheory
