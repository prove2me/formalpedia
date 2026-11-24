-- Prove2me | solution 1 for GlobalTheory.Hk.RealZero.re_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:21.139508+00:00
-- url     : https://prove2.me/submissions/e9b41d74-7b1b-40ab-9cc4-d2863cf2f762

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionUniqueSimpleExceptionalZero
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one


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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealZero
namespace GlobalTheory.Hk.RealZero
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ}
    (hz : 𝓕.F χ z = 0) : z.re ≤ 1 := by
  by_contra h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ z (not_le.mp h)).2.2.1 hz
end GlobalTheory.Hk.RealZero
