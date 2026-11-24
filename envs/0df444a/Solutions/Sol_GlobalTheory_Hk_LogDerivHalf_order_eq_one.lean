-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.order_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:23.011031+00:00
-- url     : https://prove2.me/submissions/4e5fcee8-03f2-4390-b8f6-2f029629d252

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf
namespace GlobalTheory.Hk.LogDerivHalf
theorem _root_.solution {f : ℂ → ℂ} {z : ℂ} (hf : AnalyticAt ℂ f z) (h0 : f z = 0) (h1 : deriv f z ≠ 0) :
    analyticOrderNatAt f z = 1 := by
  simp [analyticOrderNatAt, hf.analyticOrderAt_eq_one_of_zero_deriv_ne_zero h0 h1]
end GlobalTheory.Hk.LogDerivHalf
