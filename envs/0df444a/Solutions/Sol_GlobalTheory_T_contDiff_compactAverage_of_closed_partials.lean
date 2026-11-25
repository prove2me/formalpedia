-- Prove2me | solution 1 for GlobalTheory.T.contDiff_compactAverage_of_closed_partials
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:15:07.148963+00:00
-- url     : https://prove2.me/submissions/6238de04-f4ea-428b-a16b-60b13205ddea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartials
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ContDiffCompactAverageOfClosedPartialsStatement
import Theorems.Thm_GlobalTheory_AvgSmooth_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ContDiff
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K] (μ : Measure K) [IsFiniteMeasure μ] (n : ℕ) (φ : Fin n → (Fin n → ℝ) → ℂ), (∀ i, ContDiff ℝ ∞ (φ i)) → ∀ 𝒢 : Set (K → (Fin n → ℝ) → ℂ), (∀ F ∈ 𝒢, Continuous fun p : K × (Fin n → ℝ) => F p.1 p.2) → (∀ F ∈ 𝒢, ∀ k, Differentiable ℝ (F k)) → (∀ F ∈ 𝒢, ∀ i, ∃ F' ∈ 𝒢, ∀ k t, fderiv ℝ (F k) t (Pi.single i 1) = F' k t + φ i t * F k t) → ∀ F ∈ 𝒢, ContDiff ℝ ∞ fun t => ∫ k, F k t ∂μ := by
  first | exact @GlobalTheory.AvgSmooth.main | exact GlobalTheory.AvgSmooth.main | (intros; apply GlobalTheory.AvgSmooth.main <;> assumption)
end _root_.GlobalTheory.T
