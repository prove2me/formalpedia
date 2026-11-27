-- Prove2me | solution 1 for GlobalTheory.T.uniform_lower_bound_near_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:05.61132+00:00
-- url     : https://prove2.me/submissions/efe87353-f255-4c06-962f-630f6b1c2175

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjective
import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_UniformLowerBoundNearInjectiveStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RealCoordinates_eventually_lower_bound_of_tendsto_injective


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
theorem _root_.solution : ∀ (X P : Type) [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace P] (N : ℕ) (e : X ≃+ (Fin N → ℝ)), Continuous e → Continuous e.symm → ∀ (c : P) (A : P → X →+ X), (∀ s, Continuous (A s)) → (∀ x, Filter.Tendsto (fun s => A s x) (nhds c) (nhds (A c x))) → Function.Injective (A c) → ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ s in nhds c, ∀ x, δ * ‖e x‖ ≤ ‖e (A s x)‖ := by
  first | exact @GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | exact GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective | (intros; apply GlobalTheory.CompanionTheory.RealCoordinates.eventually_lower_bound_of_tendsto_injective <;> assumption)
end _root_.GlobalTheory.T
