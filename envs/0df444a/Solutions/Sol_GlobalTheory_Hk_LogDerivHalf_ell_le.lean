-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.ell_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:32:19.348103+00:00
-- url     : https://prove2.me/submissions/a7b458f3-e9f1-43a7-be08-1ebd49cdab1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe
import Theorems.Thm_GlobalTheory_Hk_LFam_two_lt_ell


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
theorem _root_.solution (𝓕 : LFam) (t u : ℝ) (h : |u - t| ≤ 3 / 5) : 𝓕.ell u ≤ 4 / 3 * 𝓕.ell t := by
  have hB : (4 : ℝ) ≤ 𝓕.B := 𝓕.B_ge
  have h2 := 𝓕.two_lt_ell t
  have hu : |u| ≤ |t| + 3 / 5 := by
    have := abs_sub_abs_le_abs_sub u t
    linarith
  have ht0 := abs_nonneg t
  have hpos : 0 < 𝓕.B * (|u| + 2) := by positivity
  have hle : 𝓕.B * (|u| + 2) ≤ 𝓕.B * (|t| + 2) * (13 / 10) := by
    have : |u| + 2 ≤ (|t| + 2) * (13 / 10) := by linarith
    nlinarith
  have hlog : Real.log (𝓕.B * (|u| + 2)) ≤ Real.log (𝓕.B * (|t| + 2)) + Real.log (13 / 10) := by
    rw [← Real.log_mul (by positivity) (by norm_num)]
    exact Real.log_le_log hpos hle
  have h13 : Real.log (13 / 10 : ℝ) ≤ 3 / 10 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 13 / 10 by norm_num)
    linarith
  unfold LFam.ell at h2 ⊢
  linarith
end GlobalTheory.Hk.LogDerivHalf
