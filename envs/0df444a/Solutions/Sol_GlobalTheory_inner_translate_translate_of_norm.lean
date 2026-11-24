-- Prove2me | solution 1 for GlobalTheory.inner_translate_translate_of_norm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:03.615161+00:00
-- url     : https://prove2.me/submissions/f66ecf11-319f-444c-a923-947b0553f770

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsIsometricIntertwinerOfMatrixCoeffEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {G : Type} [Group G] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖) (w : H)
    (g h : G) : ⟪σ g w, σ h w⟫_ℂ = ⟪w, σ (g⁻¹ * h) w⟫_ℂ := by
  have hmul : σ h w = σ g (σ (g⁻¹ * h) w) := by
    show σ h w = (σ g * σ (g⁻¹ * h)) w
    rw [← map_mul, mul_inv_cancel_left]
  let T : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  rw [hmul]
  exact T.inner_map_map w (σ (g⁻¹ * h) w)
end GlobalTheory
