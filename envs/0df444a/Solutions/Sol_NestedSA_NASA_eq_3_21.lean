-- Prove2me | solution 1 for NestedSA.NASA.eq_3_21
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:40.115739+00:00
-- url     : https://prove2.me/submissions/76058f17-bb5e-45aa-9582-d7e5f8562de1

import Mathlib
import Definitions.Def_SpectralProjGrad_Shared_IsProjOnto
import Definitions.Def_NestedSA_NASA_Basic

set_option autoImplicit false
open scoped RealInnerProductSpace
open NestedSA.NASA

lemma CC_var {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (w : EuclideanSpace ℝ (Fin n)) :
    ∀ y ∈ X, ⟪w - P w, y - P w⟫ ≤ 0 := by
  have hmem := (hP w).1
  have : ‖w - P w‖ = ⨅ v : X, ‖w - v‖ := by
    apply le_antisymm
    · haveI : Nonempty X := ⟨⟨P w, hmem⟩⟩
      exact le_ciInf (fun v => (hP w).2 v v.2)
    · exact ciInf_le ⟨0, by rintro _ ⟨v, rfl⟩; exact norm_nonneg _⟩ (⟨P w, hmem⟩ : X)
  exact (norm_eq_iInf_iff_real_inner_le_zero hX_cvx hmem).1 this

lemma CC_key {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P) (x z : EuclideanSpace ℝ (Fin n))
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) :
    ‖P (x - s • z) - x‖ ≤ ‖P (x - t • z) - x‖ ∧
      s * ‖P (x - t • z) - x‖ ≤ t * ‖P (x - s • z) - x‖ := by
  set a := P (x - s • z) with ha
  set b := P (x - t • z) with hb
  have haX : a ∈ X := (hP _).1
  have hbX : b ∈ X := (hP _).1
  have h3 := CC_var X hX_cvx P hP (x - s • z) b hbX
  have h4 := CC_var X hX_cvx P hP (x - t • z) a haX
  rw [← ha] at h3
  rw [← hb] at h4
  set u := x - a with hu
  set v := x - b with hv
  have e1 : x - s • z - a = u - s • z := by rw [hu]; abel
  have e2 : b - a = u - v := by rw [hu, hv]; abel
  have e3 : x - t • z - b = v - t • z := by rw [hv]; abel
  have e4 : a - b = v - u := by rw [hu, hv]; abel
  rw [e1, e2] at h3
  rw [e3, e4] at h4
  simp only [inner_sub_left, inner_sub_right, real_inner_smul_left, real_inner_self_eq_norm_sq] at h3 h4
  have hc : ⟪u, v⟫ ≤ ‖u‖ * ‖v‖ := real_inner_le_norm u v
  have hcomm : ⟪v, u⟫ = ⟪u, v⟫ := real_inner_comm _ _
  have hA : ‖P (x - s • z) - x‖ = ‖u‖ := by rw [← ha, hu, norm_sub_rev]
  have hB : ‖P (x - t • z) - x‖ = ‖v‖ := by rw [← hb, hv, norm_sub_rev]
  rw [hA, hB]
  have hAn := norm_nonneg u
  have hBn := norm_nonneg v
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have m3 := mul_nonpos_of_nonneg_of_nonpos ht.le h3
  have m4 := mul_nonpos_of_nonneg_of_nonpos hs.le h4
  rw [hcomm] at m4
  have hprod : (t * ‖u‖ - s * ‖v‖) * (‖u‖ - ‖v‖) ≤ 0 := by
    have hz : ⟪z, u⟫ * (t * s) - ⟪z, u⟫ * (s * t) = 0 := by ring
    nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : 0 ≤ s + t)]
  constructor
  · by_contra hlt
    push_neg at hlt
    nlinarith [mul_pos (sub_pos.2 hlt) hs, mul_nonneg (sub_nonneg.2 hst) hAn]
  · by_contra hlt
    push_neg at hlt
    nlinarith [mul_nonneg (sub_nonneg.2 hst) hAn, mul_nonneg hs.le hAn, mul_nonneg hs.le hBn]

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    ⟪z, ybar P x z β - x⟫ + β * ‖ybar P x z β - x‖ ^ 2 ≤ 0 := by
  have h := CC_var X hX_cvx P hP (x - β⁻¹ • z) x hx
  have hy : ybar P x z β = P (x - β⁻¹ • z) := rfl
  rw [hy]
  set p := P (x - β⁻¹ • z) with hp
  have e1 : x - β⁻¹ • z - p = -((p - x) + β⁻¹ • z) := by abel
  have e2 : x - p = -(p - x) := by abel
  rw [e1, e2, inner_neg_neg, inner_add_left, real_inner_self_eq_norm_sq, real_inner_smul_left,
    real_inner_comm] at h
  have h' := mul_le_mul_of_nonneg_left h hβ.le
  have : β * (‖p - x‖ ^ 2 + β⁻¹ * ⟪p - x, z⟫) = β * ‖p - x‖ ^ 2 + ⟪p - x, z⟫ := by
    field_simp
  rw [this] at h'
  linarith [real_inner_comm (p - x) z]
