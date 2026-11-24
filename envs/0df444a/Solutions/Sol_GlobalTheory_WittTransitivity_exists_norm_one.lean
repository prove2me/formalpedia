-- Prove2me | solution 1 for GlobalTheory.WittTransitivity.exists_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:17:49.550197+00:00
-- url     : https://prove2.me/submissions/7aaa58dd-23db-41cd-a210-3a3070f9fc8f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DisjointSpanPerpLat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsReflection

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped Matrix
open Formalism.UG
open GlobalTheory GlobalTheory.WittTransitivity
variable {A : Type} [CommRing A] (c : A →+* A) {M : ℕ} (J : Matrix (Fin M) (Fin M) A)
namespace GlobalTheory.WittTransitivity
theorem _root_.solution (hc : ∀ a, c (c a) = a) (hf : ∀ a, c a = a → a ≠ 0 → IsUnit a)
    (h2 : IsUnit (2 : A)) (h3 : (3 : A) ≠ 0) (hθ : ∃ θ, IsUnit (θ - c θ))
    (b t : A) (hcb : c b = b) (hb : IsUnit b) :
    ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
  have hN : ∀ a : A, a * c a ≠ 0 → IsUnit (a * c a) := by
    intro a ha
    exact hf _ (by rw [map_mul, hc, mul_comm]) ha
  by_cases h1 : (b - t) * c (b - t) = 0
  · by_cases h1' : (b + t) * c (b + t) = 0
    · rw [map_sub, hcb] at h1
      rw [map_add, hcb] at h1'
      have h4 : (2 * b) * (t + c t) = (2 * b) * 0 := by linear_combination h1' - h1
      have htc : t + c t = 0 := (h2.mul hb).mul_left_cancel h4
      have hct : c t = -t := by linear_combination htc
      rw [hct] at h1 h1'
      have h5 : (2 : A) * (b * b - t * t) = 2 * 0 := by linear_combination h1 + h1'
      have hb2 : b * b = t * t := sub_eq_zero.mp (h2.mul_left_cancel h5)
      have ht : IsUnit t := isUnit_of_mul_isUnit_left (by rw [← hb2]; exact hb.mul hb)
      have key : ∀ w : A, IsUnit (w * c w) → IsUnit (w - c w) → IsUnit (w + c w) →
          ∃ u : A, u * c u = 1 ∧ IsUnit (b - c u * t) := by
        intro w hw hm hp
        obtain ⟨e, he⟩ := isUnit_of_mul_isUnit_right hw
        have h0 : c (↑e⁻¹ : A) * w = 1 := by
          have h6 := congrArg c (Units.inv_mul e)
          rw [map_mul, he, hc, map_one] at h6
          exact h6
        refine ⟨w * ↑e⁻¹, ?_, ?_⟩
        · calc w * ↑e⁻¹ * c (w * ↑e⁻¹) = (↑e⁻¹ * c w) * (c ↑e⁻¹ * w) := by rw [map_mul]; ring
            _ = 1 := by rw [← he, Units.inv_mul, h0, one_mul]
        · have hprod : IsUnit ((w * b - c w * t) * (c w * b + w * t)) := by
            have e1 : (w * b - c w * t) * (c w * b + w * t) = b * t * (w - c w) * (w + c w) := by
              linear_combination (w * c w) * hb2
            rw [e1]
            exact ((hb.mul ht).mul hm).mul hp
          have e2 : b - c (w * ↑e⁻¹) * t = c ↑e⁻¹ * (w * b - c w * t) := by
            rw [map_mul]
            linear_combination (-b) * h0
          rw [e2]
          exact (isUnit_of_mul_isUnit_left (by rw [h0]; exact isUnit_one)).mul
            (isUnit_of_mul_isUnit_left hprod)
      obtain ⟨θ, hθu⟩ := hθ
      have hcδ : c (θ - c θ) = -(θ - c θ) := by rw [map_sub, hc]; ring
      by_cases hd : (1 + (θ - c θ)) * c (1 + (θ - c θ)) = 0
      · rw [map_add, map_one, hcδ] at hd
        apply key (2 + (θ - c θ))
        · have e : (2 + (θ - c θ)) * c (2 + (θ - c θ)) = 3 := by
            rw [map_add, map_ofNat, hcδ]
            linear_combination hd
          rw [e]
          exact hf 3 (map_ofNat c 3) h3
        · have e : 2 + (θ - c θ) - c (2 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add, map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 2 + (θ - c θ) + c (2 + (θ - c θ)) = 2 * 2 := by
            rw [map_add, map_ofNat, hcδ]
            ring
          rw [e]
          exact h2.mul h2
      · apply key (1 + (θ - c θ)) (hN _ hd)
        · have e : 1 + (θ - c θ) - c (1 + (θ - c θ)) = 2 * (θ - c θ) := by
            rw [map_add, map_one, hcδ]
            ring
          rw [e]
          exact h2.mul hθu
        · have e : 1 + (θ - c θ) + c (1 + (θ - c θ)) = 2 := by
            rw [map_add, map_one, hcδ]
            ring
          rw [e]
          exact h2
    · refine ⟨-1, by rw [map_neg, map_one]; ring, ?_⟩
      have e : b - c (-1) * t = b + t := by rw [map_neg, map_one]; ring
      rw [e]
      exact isUnit_of_mul_isUnit_left (hN _ h1')
  · refine ⟨1, by rw [map_one, one_mul], ?_⟩
    have e : b - c 1 * t = b - t := by rw [map_one, one_mul]
    rw [e]
    exact isUnit_of_mul_isUnit_left (hN _ h1)
end GlobalTheory.WittTransitivity
