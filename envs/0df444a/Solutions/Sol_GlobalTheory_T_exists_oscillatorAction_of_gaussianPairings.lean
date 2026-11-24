-- Prove2me | solution 1 for GlobalTheory.T.exists_oscillatorAction_of_gaussianPairings
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:16:19.70695+00:00
-- url     : https://prove2.me/submissions/b1e0025f-c12c-4fcc-93af-e44bc5866384

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairings
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsOscillatorActionOfGaussianPairingsStatement
import Theorems.Thm_GlobalTheory_RealWeil_Osc_exists_isOsc


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ (G : Type) [Group G] (k : G →* (V →L[ℝ] V)) (c : G → ℂ), (∀ g x y, omJ J (k g x) (k g y) = omJ J x y) → c 1 = 1 → (∀ g, star (c g) * c g * lam (k g) = 1) → (∀ g g', c g * c g' * mu J (k (g * g')) (k g) = c (g * g') * lam (k (g * g'))) → ∃ Ω : G → B → B, IsOsc ρ (fun g v => k g v) Ω ∧ (∀ (Y : Type) [TopologicalSpace Y] (γ : Y → G), Continuous (fun y => k (γ y)) → Continuous (fun y => c (γ y)) → ∀ f, Sm ρ f → Continuous fun y => Ω (γ y) f) ∧ ∀ a g, (∀ x, ‖k g x‖ = ‖x‖) → ∀ f, Sm ρ f → ∫ u, gau u • ρ (k a u) f = f → Ω (a * g * a⁻¹) f = c g • f := by
  first | exact @GlobalTheory.RealWeil.Osc.exists_isOsc | exact GlobalTheory.RealWeil.Osc.exists_isOsc | (intros; apply GlobalTheory.RealWeil.Osc.exists_isOsc <;> assumption)
end _root_.GlobalTheory.T
