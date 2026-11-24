-- Prove2me | solution 1 for GlobalTheory.matrixCoeff_idempotent_of_orthogonality
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:49.925801+00:00
-- url     : https://prove2.me/submissions/6a15eae5-b4aa-47df-b4e2-619514ff75ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MatrixCoeffIdempotentOfOrthogonality
import Theorems.Thm_GlobalTheory_inner_isometricRep_inv

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
theorem _root_.solution : ∀ (G : Type) [Group G] [MeasurableSpace G] (μ : Measure G) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : G →* (H →L[ℂ] H)) (d : ℝ), 0 < d → (∀ g x, ‖σ g x‖ = ‖x‖) → (∀ v w v' w' : H, ∫ g, ⟪w, σ g v⟫_ℂ * star ⟪w', σ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) → ∀ w : H, ‖w‖ = 1 → (∀ g : G, star ((d : ℂ) * star ⟪w, σ g⁻¹ w⟫_ℂ) = (d : ℂ) * star ⟪w, σ g w⟫_ℂ) ∧ (∀ x y : G, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ)) ∧ (∀ u u' : H, ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ) ∧ ∀ y : H, (∀ g, ⟪y, σ g w⟫_ℂ = 0) → y = 0 := by
  intro G _ _ μ H _ _ _ σ d hd hσ hS w hw
  have adj : ∀ (g : G) (a b : H), ⟪a, σ g⁻¹ b⟫_ℂ = ⟪σ g a, b⟫_ℂ :=
    fun g a b => inner_isometricRep_inv σ hσ g a b
  have hc : ∀ a b : H, star ⟪a, b⟫_ℂ = ⟪b, a⟫_ℂ := fun a b => by
    rw [← starRingEnd_apply, inner_conj_symm]
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdc : star (d : ℂ) = d := by simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    rw [star_mul', star_star, hdc, adj, hc]
  · intro x y
    have key : ∀ g : G, star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ = ⟪σ y w, σ g (σ x w)⟫_ℂ := by
      intro g
      rw [map_mul, map_mul, ContinuousLinearMap.mul_apply, ContinuousLinearMap.mul_apply,
        adj, adj, hc]
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ((d : ℂ) * star ⟪w, σ (x⁻¹ * g⁻¹ * y) w⟫_ℂ) ∂μ
        = ∫ g, ((d : ℂ) * d) * (⟪σ y w, σ g (σ x w)⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; rw [key]; ring
      _ = ((d : ℂ) * d) * (⟪w, σ x w⟫_ℂ * ⟪σ y w, w⟫_ℂ / d) := by
          rw [integral_const_mul, hS]
      _ = ⟪w, σ x w⟫_ℂ * ((d : ℂ) * star ⟪w, σ y w⟫_ℂ) := by
          rw [hc]; field_simp
  · intro u u'
    calc ∫ g, ((d : ℂ) * star ⟪w, σ g w⟫_ℂ) * ⟪u', σ g u⟫_ℂ ∂μ
        = ∫ g, (d : ℂ) * (⟪u', σ g u⟫_ℂ * star ⟪w, σ g w⟫_ℂ) ∂μ := by
          congr 1; funext g; ring
      _ = ⟪w, u⟫_ℂ * ⟪u', w⟫_ℂ := by
          rw [integral_const_mul, hS]; field_simp
  · intro y hy
    have h0 := hS w y w y
    simp only [hy, zero_mul, integral_zero] at h0
    have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw]; simp
    rw [hww, one_mul] at h0
    have hyy : ⟪y, y⟫_ℂ = 0 := (div_eq_zero_iff.mp h0.symm).resolve_right hd0
    exact inner_self_eq_zero.mp hyy
end GlobalTheory
