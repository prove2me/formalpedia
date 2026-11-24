-- Prove2me | solution 1 for GlobalTheory.inner_isometricRep_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:00:00.20497+00:00
-- url     : https://prove2.me/submissions/f154fe03-690f-4f46-989a-d7920411804d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCoeffIdempotentOfOrthogonality

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
    [InnerProductSpace ℂ H] (σ : G →* (H →L[ℂ] H)) (hσ : ∀ g x, ‖σ g x‖ = ‖x‖)
    (g : G) (u v : H) : ⟪u, σ g⁻¹ v⟫_ℂ = ⟪σ g u, v⟫_ℂ := by
  have hv : σ g (σ g⁻¹ v) = v := by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      ContinuousLinearMap.one_apply]
  let f : H →ₗᵢ[ℂ] H := { toLinearMap := (σ g : H →ₗ[ℂ] H), norm_map' := hσ g }
  have hf : ∀ x, f x = σ g x := fun _ => rfl
  calc ⟪u, σ g⁻¹ v⟫_ℂ = ⟪f u, f (σ g⁻¹ v)⟫_ℂ := (f.inner_map_map _ _).symm
    _ = ⟪σ g u, v⟫_ℂ := by rw [hf, hf, hv]
end GlobalTheory
