-- Prove2me | solution 1 for GlobalTheory.T.exists_thetaSeries_apply_ne_zero_of_large_form
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:06:09.871687+00:00
-- url     : https://prove2.me/submissions/8f4c659f-1880-4edc-b6d2-6cee9ddc9b82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeFormStatement
import Theorems.Thm_GlobalTheory_ThetaLarge_exists_theta_apply_ne_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) := by
  first | exact @GlobalTheory.ThetaLarge.exists_theta_apply_ne_zero | exact GlobalTheory.ThetaLarge.exists_theta_apply_ne_zero | (intros; apply GlobalTheory.ThetaLarge.exists_theta_apply_ne_zero <;> assumption)
end _root_.GlobalTheory.T
