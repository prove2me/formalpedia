-- Prove2me | solution 1 for GlobalTheory.T.gaussianPairing_unitaryGroup_two_three
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:35:31.935803+00:00
-- url     : https://prove2.me/submissions/eb5a7603-b32f-42c2-b493-cd33dc38d656

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThree
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussianPairingUnitaryGroupTwoThreeStatement
import Theorems.Thm_GlobalTheory_RealWeil_GaussPairing_lam_mu_eq


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
theorem _root_.solution : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  first | exact @GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | exact GlobalTheory.RealWeil.GaussPairing.lam_mu_eq | (intros; apply GlobalTheory.RealWeil.GaussPairing.lam_mu_eq <;> assumption)
end _root_.GlobalTheory.T
