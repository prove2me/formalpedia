-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.pole_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:54:04.302784+00:00
-- url     : https://prove2.me/submissions/4ad2ef5a-b426-48b7-94ba-51d0fbcc5366

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
import Theorems.Thm_GlobalTheory_Hk_LFamPos_positivity


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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree
namespace GlobalTheory.Hk.ZeroFree
theorem _root_.solution {ε y : ℝ} (hε : 0 < ε) (hy : (30 * ε) ^ 2 ≤ y ^ 2) :
    6 * ε / ((6 * ε) ^ 2 + y ^ 2) ≤ 1 / 156 * (1 / ε) := by
  have hD : 0 < (6 * ε) ^ 2 + y ^ 2 := by positivity
  have e : 1 / 156 * (1 / ε) = 1 / (156 * ε) := by ring
  rw [e, div_le_div_iff₀ hD (by positivity)]
  nlinarith
end GlobalTheory.Hk.ZeroFree
