-- Prove2me | solution 1 for GlobalTheory.one_le_sqrt_abs_discr
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:58:42.195576+00:00
-- url     : https://prove2.me/submissions/064bfe75-448c-471f-8173-69afcc9f4ed9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIdealInClassOfNormLeSqrtDiscr

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
theorem _root_.solution : 1 ≤ √|(discr K : ℝ)| := by
  rw [Real.one_le_sqrt]
  exact_mod_cast Int.one_le_abs (discr_ne_zero K)
end GlobalTheory
