-- Prove2me | solution 1 for GlobalTheory.T.rayClassLFunctionFamily_continuation_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:42:45.827817+00:00
-- url     : https://prove2.me/submissions/f555f896-5768-42cb-8dc0-b82046ba382d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowth
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Theorems.Thm_GlobalTheory_Hk_RayCont_continuation_growth


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
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ), AnalyticOnNhd ℂ (𝓕.F χ) {s | 1 / 2 < s.re} ∧ (∀ s : ℂ, 1 < s.re → LSeriesSummable (𝓕.aChi χ) s ∧ 𝓕.F χ s = (if χ = 1 then s - 1 else 1) * LSeries (𝓕.aChi χ) s) ∧ (∀ s : ℂ, 11 / 20 ≤ s.re → ‖𝓕.F χ s‖ ≤ 300 * 𝓕.B * (‖s‖ + 1) ^ 2) ∧ (χ * χ = 1 → ∀ s : ℂ, 𝓕.F χ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (𝓕.F χ s)) := by
  first | exact @GlobalTheory.Hk.RayCont.continuation_growth | exact GlobalTheory.Hk.RayCont.continuation_growth | (intros; apply GlobalTheory.Hk.RayCont.continuation_growth <;> assumption)
end _root_.GlobalTheory.T
