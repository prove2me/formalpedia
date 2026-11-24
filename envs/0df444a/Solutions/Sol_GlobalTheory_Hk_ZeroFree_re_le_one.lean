-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.re_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:03:22.175752+00:00
-- url     : https://prove2.me/submissions/ea513e3e-9b61-4d96-8555-bf2bbafd2ded

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree
namespace GlobalTheory.Hk.ZeroFree
theorem _root_.solution {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {w : ℂ} (hw : 𝓕.F χ w = 0) : w.re ≤ 1 := by
  by_contra h
  push_neg at h
  exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ w h).2.2.1 hw
end GlobalTheory.Hk.ZeroFree
