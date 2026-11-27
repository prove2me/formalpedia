-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_isIntegral_of_sum_abs_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:38:16.955012+00:00
-- url     : https://prove2.me/submissions/f47a6bb9-8263-44a9-9d75-00df153197fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual
import Theorems.Thm_GlobalTheory_eq_zero_of_isIntegral_of_sum_norm_lt
import Theorems.Thm_GlobalTheory_sum_abs_realEmbeddings

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
theorem _root_.solution {x : F} (hx : IsIntegral ℤ x)
    (h : ∑ σ : F →+* ℝ, |σ x| < finrank ℚ F) : x = 0 :=
  eq_zero_of_isIntegral_of_sum_norm_lt hx (by rwa [← sum_abs_realEmbeddings])
end GlobalTheory
