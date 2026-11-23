-- Prove2me | solution 1 for GlobalTheory.Hk.LogDeriv.summable_of_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:48.927368+00:00
-- url     : https://prove2.me/submissions/614f62c8-5b42-46ee-b658-16ee02a3170f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TsumOneDivRpowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOne

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDeriv
open LSeries
open scoped LSeries.notation
namespace GlobalTheory.Hk.LogDeriv
theorem _root_.solution {l : ℕ → ℂ} (hl : ∀ n, ‖l n‖ ≤ 2 * Λ n) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable l s := by
  have hΛ := LSeriesSummable_vonMangoldt hs
  refine Summable.of_norm_bounded (g := fun n => 2 * ‖LSeries.term (↗Λ) s n‖)
    ((summable_norm_iff.mpr hΛ).mul_left 2) (fun n => ?_)
  simp only [LSeries.norm_term_eq]
  split_ifs
  · simp
  · rw [← mul_div_assoc]
    gcongr
    rw [Complex.norm_of_nonneg vonMangoldt_nonneg]
    exact hl n
end GlobalTheory.Hk.LogDeriv
