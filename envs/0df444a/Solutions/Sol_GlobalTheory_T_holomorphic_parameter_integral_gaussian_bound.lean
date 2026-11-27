-- Prove2me | solution 1 for GlobalTheory.T.holomorphic_parameter_integral_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:34:09.204711+00:00
-- url     : https://prove2.me/submissions/041ec0e9-0c9b-4ce9-ab34-93e7b75f0af8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBound
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HolomorphicParameterIntegralGaussianBoundStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HolMean_GaussianFamily_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (m n : ℕ) (Φ : ℂ → (Fin m → Fin n → ℂ) → ℂ) (ρ C δ : ℝ), 0 < ρ → 0 < δ → (∀ v, DifferentiableOn ℂ (fun z => Φ z v) (Metric.ball 0 ρ)) → ContinuousOn (fun zv : ℂ × (Fin m → Fin n → ℂ) => Φ zv.1 zv.2) (Metric.ball 0 ρ ×ˢ Set.univ) → (∀ z ∈ Metric.ball (0 : ℂ) ρ, ∀ v, ‖Φ z v‖ ≤ C * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2)) → ∀ K : (Fin m → Fin n → ℂ) → ℂ, Continuous K → (∀ v, ‖K v‖ ≤ 1) → ∃ ρ' : ℝ, 0 < ρ' ∧ DifferentiableOn ℂ (fun z => ∫ v, K v * Φ z v) (Metric.ball 0 ρ') ∧ ∀ r : ℕ, iteratedDeriv r (fun z => ∫ v, K v * Φ z v) 0 = ∫ v, K v * iteratedDeriv r (fun z => Φ z v) 0 ∧ Continuous (fun v => iteratedDeriv r (fun z => Φ z v) 0) ∧ ∃ C' : ℝ, ∀ v, ‖iteratedDeriv r (fun z => Φ z v) 0‖ ≤ C' * Real.exp (-δ * ∑ a, ∑ j, ‖v a j‖ ^ 2) := by
  first | exact @GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | exact GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main | (intros; apply GlobalTheory.CompanionTheory.HolMean.GaussianFamily.main <;> assumption)
end _root_.GlobalTheory.T
