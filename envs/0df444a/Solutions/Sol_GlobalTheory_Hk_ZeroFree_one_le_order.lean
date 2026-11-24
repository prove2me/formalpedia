-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.one_le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:03:11.9068+00:00
-- url     : https://prove2.me/submissions/f7db4907-e4c7-4cef-8522-a97968f8e3f0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionZeroFreeRegion
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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.ZeroFree
namespace GlobalTheory.Hk.ZeroFree
theorem _root_.solution {𝓕 : LFam} {χ : AddChar 𝓕.G ℂ} {ρ : ℂ} (h : 1 / 2 < ρ.re)
    (hρ : 𝓕.F χ ρ = 0) : 1 ≤ analyticOrderNatAt (𝓕.F χ) ρ := by
  have hU := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1
  have hA : AnalyticAt ℂ (𝓕.F χ) ρ := hU ρ h
  have htop : analyticOrderAt (𝓕.F χ) ρ ≠ ⊤ := by
    intro ht
    rw [analyticOrderAt_eq_top] at ht
    have hc : Convex ℝ {s : ℂ | 1 / 2 < s.re} := convex_halfSpace_re_gt _
    have hE := hU.eqOn_zero_of_preconnected_of_eventuallyEq_zero hc.isPreconnected h ht
    have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
    exact (GlobalTheory.T.rayClassFamily_logDeriv_re_gt_one 𝓕 χ 2 h2).2.2.1 (hE (show (1 : ℝ) / 2 < (2 : ℂ).re by norm_num))
  have hz : analyticOrderAt (𝓕.F χ) ρ ≠ 0 := hA.analyticOrderAt_ne_zero.mpr hρ
  rw [Nat.one_le_iff_ne_zero]
  intro h0
  apply hz
  rw [← Nat.cast_analyticOrderNatAt htop, h0]
  simp
end GlobalTheory.Hk.ZeroFree
