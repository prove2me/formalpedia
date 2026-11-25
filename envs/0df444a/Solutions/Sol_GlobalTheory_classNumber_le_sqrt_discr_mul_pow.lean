-- Prove2me | solution 1 for GlobalTheory.classNumber_le_sqrt_discr_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:03:21.15624+00:00
-- url     : https://prove2.me/submissions/5bc3b064-63e0-4db4-a764-324c22e53c0c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_one_le_sqrt_abs_discr
import Theorems.Thm_GlobalTheory_classNumber_le_sqrt_discr_mul_pow_pred

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Real NumberField ArithmeticFunction.zeta
open Module NumberField Finset
open GlobalTheory
variable (K : Type*) [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ finrank ℚ K := by
  refine (classNumber_le_sqrt_discr_mul_pow_pred K).trans ?_
  have := Real.log_nonneg (one_le_sqrt_abs_discr K)
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by linarith) (Nat.sub_le _ _))
    (Real.sqrt_nonneg _)
end GlobalTheory
