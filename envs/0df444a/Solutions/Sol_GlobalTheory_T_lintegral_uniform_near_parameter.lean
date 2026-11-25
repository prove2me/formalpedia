-- Prove2me | solution 1 for GlobalTheory.T.lintegral_uniform_near_parameter
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:23:56.824843+00:00
-- url     : https://prove2.me/submissions/a59d5c63-1d48-4ed9-9120-3b61498c409c

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameter
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralUniformNearParameterStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FibSch_integral_comp_additive_continuousAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal NNReal Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] [TopologicalSpace P] [FirstCountableTopology P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → ∀ (c : P) (m0 : Measure X) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → ∀ δ : ℝ, 0 < δ → (∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖) → ∫⁻ x, ENNReal.ofReal ((1 + ‖e x‖) ^ (-((N + 1 : ℕ) : ℝ))) ∂m0 ≠ ⊤ → ∀ (u : (Fin N → ℝ) → ℂ) (C : ℝ), Continuous u → (∀ y, ‖u y‖ ≤ C * (1 + ‖y‖) ^ (-((N + 1 : ℕ) : ℝ))) → (∀ᶠ s in nhds c, Integrable (fun x => u (e (A s x))) m0) ∧ ContinuousAt (fun s => ∫ x, u (e (A s x)) ∂m0) c := by
  first | exact @GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | exact GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt | (intros; apply GlobalTheory.CompanionTheory.FibSch.integral_comp_additive_continuousAt <;> assumption)
end _root_.GlobalTheory.T
