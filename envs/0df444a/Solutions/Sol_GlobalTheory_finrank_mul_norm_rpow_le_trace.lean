-- Prove2me | solution 1 for GlobalTheory.finrank_mul_norm_rpow_le_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:15.212656+00:00
-- url     : https://prove2.me/submissions/7530e415-7469-460f-a28a-9781ae33bd5f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_finrank_mul_abs_norm_rpow_le_sum
import Theorems.Thm_GlobalTheory_trace_eq_sum_realEmbeddings
import Theorems.Thm_GlobalTheory_sum_abs_realEmbeddings
import Theorems.Thm_GlobalTheory_norm_pos_of_totallyPos

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
variable {F : Type*} [Field F] [NumberField F] [IsTotallyReal F]
namespace GlobalTheory
theorem _root_.solution {a : F} (ha : ∀ σ : F →+* ℝ, 0 < σ a) :
    (finrank ℚ F : ℝ) * ((Algebra.norm ℚ a : ℚ) : ℝ) ^ (1 / (finrank ℚ F : ℝ))
      ≤ ((Algebra.trace ℚ F a : ℚ) : ℝ) := by
  have h := finrank_mul_abs_norm_rpow_le_sum a
  have hp : (0 : ℝ) < ((Algebra.norm ℚ a : ℚ) : ℝ) := by
    exact_mod_cast norm_pos_of_totallyPos ha
  rw [abs_of_pos hp, ← sum_abs_realEmbeddings,
    Finset.sum_congr rfl fun σ _ => abs_of_pos (ha σ)] at h
  rwa [one_div, trace_eq_sum_realEmbeddings]
end GlobalTheory
