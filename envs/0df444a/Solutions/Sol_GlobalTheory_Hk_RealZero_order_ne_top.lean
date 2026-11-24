-- Prove2me | solution 1 for GlobalTheory.Hk.RealZero.order_ne_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:11.079022+00:00
-- url     : https://prove2.me/submissions/441e44c0-a1b4-4cbb-8a1e-26f787a6af16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionUniqueSimpleExceptionalZero
import Theorems.Thm_GlobalTheory_T_rayClassFamily_logDeriv_re_gt_one
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_continuation_growth


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
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) :
    analyticOrderAt (𝓕.F χ) z ≠ ⊤ := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hU : IsPreconnected {s : ℂ | 1 / 2 < s.re} := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  have h2 : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    show (1 : ℝ) / 2 < (2 : ℂ).re
    norm_num
  have hF2 : 𝓕.F χ 2 ≠ 0 := (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 (by norm_num)).2.2.1
  have h2top : analyticOrderAt (𝓕.F χ) 2 ≠ ⊤ := by
    rw [(hA 2 h2).analyticOrderAt_eq_zero.mpr hF2]
    exact ENat.zero_ne_top
  exact hA.analyticOrderAt_ne_top_of_isPreconnected hU h2 hz h2top
end GlobalTheory.Hk.RealZero
