-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_isIntegral_of_sum_norm_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:54:12.883861+00:00
-- url     : https://prove2.me/submissions/f2fcf63f-362c-4f62-8785-ce327a6d16a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_finrank_le_sum_norm_of_isIntegral

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
theorem _root_.solution {x : K} (hx : IsIntegral ℤ x)
    (h : ∑ σ : K →+* ℂ, ‖σ x‖ < finrank ℚ K) : x = 0 := by
  by_contra h0
  exact absurd h (not_lt.mpr (finrank_le_sum_norm_of_isIntegral hx h0))
end GlobalTheory
