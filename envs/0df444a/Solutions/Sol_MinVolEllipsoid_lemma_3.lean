-- Prove2me | solution 1 for MinVolEllipsoid.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:27:23.277013+00:00
-- url     : https://prove2.me/submissions/69fb8af1-cb71-433f-8bd5-40e2baf1f930

import Mathlib

open Matrix

namespace Aux_MVEl3

variable {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)

theorem Qadd (u w : Fin n → ℝ) :
    (u + w) ⬝ᵥ (M *ᵥ (u + w)) =
      u ⬝ᵥ (M *ᵥ u) + w ⬝ᵥ (M *ᵥ w) + (u ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ u)) := by
  rw [mulVec_add, add_dotProduct, dotProduct_add, dotProduct_add]; ring

theorem Qline (u w : Fin n → ℝ) (c : ℝ) :
    (u + c • w) ⬝ᵥ (M *ᵥ (u + c • w)) =
      u ⬝ᵥ (M *ᵥ u) + c ^ 2 * (w ⬝ᵥ (M *ᵥ w)) + c * (u ⬝ᵥ (M *ᵥ w) + w ⬝ᵥ (M *ᵥ u)) := by
  rw [Qadd]
  simp only [mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

theorem entry (i j : Fin n) :
    (Pi.single i (1 : ℝ)) ⬝ᵥ (M *ᵥ Pi.single j (1 : ℝ)) = M i j := by
  simp [dotProduct, Matrix.mulVec, Pi.single_apply]

end Aux_MVEl3

open Aux_MVEl3 in
theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) (S : Set (Fin n → ℝ))
    (hS : (interior S).Nonempty) (hv : ∀ v ∈ S, v ⬝ᵥ (M *ᵥ v) = 0) : M = 0 := by
  obtain ⟨v0, hv0⟩ := hS
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hv0)
  have hv0S : v0 ∈ S := interior_subset hv0
  have hQ : ∀ w : Fin n → ℝ, w ⬝ᵥ (M *ᵥ w) = 0 := by
    intro w
    set δ : ℝ := ε / (2 * (‖w‖ + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hmem : ∀ c : ℝ, |c| = δ → v0 + c • w ∈ S := by
      intro c hc
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, hc]
      have hw := norm_nonneg w
      rw [hδ, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    have h1 := hv _ (hmem δ (abs_of_pos hδpos))
    have h2 := hv _ (hmem (-δ) (by rw [abs_neg, abs_of_pos hδpos]))
    rw [Qline] at h1 h2
    have h0 := hv v0 hv0S
    have : 2 * δ ^ 2 * (w ⬝ᵥ (M *ᵥ w)) = 0 := by nlinarith
    have hδ2 : 2 * δ ^ 2 ≠ 0 := by positivity
    exact (mul_eq_zero.mp this).resolve_left hδ2
  ext i j
  have hii := hQ (Pi.single i 1)
  have hjj := hQ (Pi.single j 1)
  have hij := hQ (Pi.single i 1 + Pi.single j 1)
  rw [Qadd, hii, hjj, entry, entry] at hij
  rw [entry] at hii
  have hsym : M j i = M i j := by
    have := congrFun (congrFun hM i) j
    simpa [Matrix.transpose_apply] using this
  simp only [Matrix.zero_apply]
  linarith
