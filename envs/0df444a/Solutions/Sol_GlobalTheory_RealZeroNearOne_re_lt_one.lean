-- Prove2me | solution 1 for GlobalTheory.RealZeroNearOne.re_lt_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:44.42307+00:00
-- url     : https://prove2.me/submissions/e2e594c0-1970-408e-9730-f8ed60d23223

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivDirichletLFunctionLocalZeroSumStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegReLogDerivPrincipalLFunctionLeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NegSumLogDerivNonneg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_OrderNeTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory GlobalTheory.RealZeroNearOne
namespace GlobalTheory.RealZeroNearOne
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) {z : ℂ}
    (hz : LFunction χ z = 0) : z.re < 1 := by
  by_contra hc
  exact LFunction_ne_zero_of_one_le_re χ (.inl h) (not_lt.mp hc) hz
end GlobalTheory.RealZeroNearOne
