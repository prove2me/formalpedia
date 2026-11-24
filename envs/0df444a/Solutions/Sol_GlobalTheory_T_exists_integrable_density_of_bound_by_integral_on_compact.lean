-- Prove2me | solution 1 for GlobalTheory.T.exists_integrable_density_of_bound_by_integral_on_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:51:31.64164+00:00
-- url     : https://prove2.me/submissions/d06169f2-1b20-4bb2-8629-19e5ef67b8f9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntegrableDensityOfBoundByIntegralCompactAStatement
import Theorems.Thm_GlobalTheory_exists_integrable_density_of_bound_by_integral_compact


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X : Type) [TopologicalSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure X) (K : Set X), IsCompact K → μ K < ⊤ → ∀ (S : Submodule ℂ (X → ℂ)), (∀ f ∈ S, Continuous f) → ∀ (Λ : (X → ℂ) → ℂ) (C : ℝ), (∀ f ∈ S, ∀ f' ∈ S, ∀ c : ℂ, Λ (c • f + f') = c * Λ f + Λ f') → (∀ f ∈ S, ‖Λ f‖ ≤ C * ∫ x in K, ‖f x‖ ∂μ) → ∃ a : X → ℂ, Measurable a ∧ Integrable a μ ∧ (∀ x ∉ K, a x = 0) ∧ ∀ f ∈ S, ∫ x, f x * a x ∂μ = Λ f := by
  first | exact @GlobalTheory.exists_integrable_density_of_bound_by_integral_compact | exact GlobalTheory.exists_integrable_density_of_bound_by_integral_compact | (intros; apply GlobalTheory.exists_integrable_density_of_bound_by_integral_compact <;> assumption)
end _root_.GlobalTheory.T
