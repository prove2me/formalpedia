-- Prove2me | solution 1 for GlobalTheory.RealZeroNearOne.analyticAt_L
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:18.998793+00:00
-- url     : https://prove2.me/submissions/950452ac-aa2e-4d2b-8431-a97138384d99

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
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} (h : χ ≠ 1) (z : ℂ) :
    AnalyticAt ℂ (LFunction χ) z := (differentiable_LFunction h).analyticAt z
end GlobalTheory.RealZeroNearOne
