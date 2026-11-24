-- Prove2me | solution 1 for GlobalTheory.ThetaLarge.exists_theta_apply_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:55:59.034799+00:00
-- url     : https://prove2.me/submissions/b03773ea-1ffc-4e57-8a42-2bfb91ad4438

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SummableLatticeExpNegPiMulNormSqDiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsThetaSeriesApplyNeZeroOfLargeForm
import Theorems.Thm_GlobalTheory_ThetaLarge_exists_tsum_gauss_lt_one
import Theorems.Thm_GlobalTheory_ThetaLarge_exists_theta
import Theorems.Thm_GlobalTheory_ThetaLarge_continuous_form
import Theorems.Thm_GlobalTheory_ThetaLarge_exists_coercive
import Theorems.Thm_GlobalTheory_ThetaLarge_form_symm

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
noncomputable section
open GlobalTheory GlobalTheory.ThetaLarge
variable {g : ℕ}
namespace GlobalTheory.ThetaLarge
theorem _root_.solution :
    (∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → ∀ H₀ : Matrix (Fin g) (Fin g) ℂ, (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₀.mulVec (star z)).re) → ∃ ρ : ℝ, ∀ (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, ρ * (z ⬝ᵥ H₀.mulVec (star z)).re ≤ (z ⬝ᵥ Hm.mulVec (star z)).re) → (∀ l, ‖χ l‖ = 1) → (∀ l m : Λ, χ (l + m) = χ l * χ m * cexp (Real.pi * I * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ))).im)) → ∀ z₀, ∃ θ : (Fin g → ℂ) → ℂ, Differentiable ℂ θ ∧ θ z₀ ≠ 0 ∧ ∀ (l : Λ) z, θ (z + l) = (χ l * cexp (Real.pi * (z ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))) + Real.pi / 2 * ((l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ))))) * θ z) := by
  classical
  intro g Λ hΛ _ H₀ hH₀
  obtain ⟨a, ha, hsum⟩ := exists_tsum_gauss_lt_one Λ
  obtain ⟨c, hc, hco⟩ := exists_coercive H₀ hH₀
  refine ⟨a / c, fun Hm χ hH hρ h1 hχ z₀ => ?_⟩
  refine exists_theta (H := fun x y => x ⬝ᵥ Hm.mulVec (star y)) (fun x y w => add_dotProduct ..)
    (fun x y w => by rw [star_add, mulVec_add, dotProduct_add]) (form_symm hH) (fun w => ?_)
    (continuous_form Hm) ha hsum (fun z => ?_) h1 hχ z₀
  · simp only [dotProduct]
    fun_prop
  · have h2 : a * ‖z‖ ^ 2 ≤ (z ⬝ᵥ Hm.mulVec (star z)).re := by
      refine le_trans ?_ (hρ z)
      calc a * ‖z‖ ^ 2 = a / c * (c * ‖z‖ ^ 2) := by field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left (hco z) (by positivity)
    have h3 : 0 ≤ a * ‖z‖ ^ 2 := by positivity
    nlinarith [Real.two_le_pi]
end GlobalTheory.ThetaLarge
