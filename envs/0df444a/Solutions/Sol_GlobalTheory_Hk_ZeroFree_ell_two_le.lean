-- Prove2me | solution 1 for GlobalTheory.Hk.ZeroFree.ell_two_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:53:58.891428+00:00
-- url     : https://prove2.me/submissions/4ee4ce1c-3e6d-470b-ab29-34bdb4409d5f

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
theorem _root_.solution (𝓕 : LFam) (t : ℝ) : 𝓕.ell (2 * t) ≤ 2 * 𝓕.ell t := by
  unfold LFam.ell
  have hB : (4 : ℝ) ≤ 𝓕.B := 𝓕.B_ge
  have hu := abs_nonneg t
  have e : 2 * Real.log (𝓕.B * (|t| + 2)) = Real.log ((𝓕.B * (|t| + 2)) ^ 2) := by
    rw [Real.log_pow]
    norm_num
  rw [e, abs_mul, abs_two]
  apply Real.log_le_log
  · positivity
  · have h1 : 2 * |t| + 2 ≤ 4 * (|t| + 2) ^ 2 := by nlinarith
    have h2 : 4 * (|t| + 2) ^ 2 ≤ 𝓕.B * (|t| + 2) ^ 2 := by nlinarith [sq_nonneg (|t| + 2)]
    calc 𝓕.B * (2 * |t| + 2) ≤ 𝓕.B * (𝓕.B * (|t| + 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (by linarith) (by linarith)
      _ = (𝓕.B * (|t| + 2)) ^ 2 := by ring
end GlobalTheory.Hk.ZeroFree
