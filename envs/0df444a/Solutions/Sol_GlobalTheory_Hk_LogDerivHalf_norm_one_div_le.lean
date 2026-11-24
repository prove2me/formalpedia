-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.norm_one_div_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:21.799746+00:00
-- url     : https://prove2.me/submissions/3e4e34c7-b739-4cf9-8f06-5c9eaf3331ee

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
theorem _root_.solution {z : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖z‖) : ‖1 / z‖ ≤ 1 / r := by
  rw [norm_div, norm_one]
  exact one_div_le_one_div_of_le hr h
end GlobalTheory.Hk.LogDerivHalf
