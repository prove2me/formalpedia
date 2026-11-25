-- Prove2me | solution 1 for GlobalTheory.classNumber_le_of_finrank_eq_two_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:08:45.78953+00:00
-- url     : https://prove2.me/submissions/b4033de8-3ab6-44aa-a1af-c3e1088e76fb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr
import Theorems.Thm_GlobalTheory_classNumber_le_sqrt_discr_mul_pow

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
theorem _root_.solution {f : ℕ} (hf : finrank ℚ K = 2 * f) :
    (classNumber K : ℝ) ≤
      √|(discr K : ℝ)| * (1 + Real.log √|(discr K : ℝ)|) ^ (2 * f) :=
  hf ▸ classNumber_le_sqrt_discr_mul_pow K
end GlobalTheory
