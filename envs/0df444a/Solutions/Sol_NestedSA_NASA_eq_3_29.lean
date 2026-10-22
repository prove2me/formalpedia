-- Prove2me | solution 1 for NestedSA.NASA.eq_3_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:31:51.644988+00:00
-- url     : https://prove2.me/submissions/ff07becd-bc37-43c1-8f78-1982d5034bae

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

lemma CC_l1 {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    ‖ybar P x z 1 - x‖ ≤ max 1 β * ‖ybar P x z β - x‖ := by
  unfold ybar
  simp only [inv_one, one_smul]
  rcases le_total β 1 with h | h
  · have hs : (1 : ℝ) ≤ β⁻¹ := by rw [le_inv_comm₀ one_pos hβ]; simpa using h
    have := (CC_key X hX_cvx P hP x z 1 β⁻¹ one_pos hs).1
    rw [one_smul] at this
    rw [max_eq_left h]; linarith
  · have hs : β⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h
    have := (CC_key X hX_cvx P hP x z β⁻¹ 1 (inv_pos.2 hβ) hs).2
    rw [one_smul, one_mul] at this
    rw [max_eq_right h]
    have h2 : β⁻¹ * ‖P (x - z) - x‖ ≤ ‖P (x - β⁻¹ • z) - x‖ := by linarith
    calc ‖P (x - z) - x‖ = β * (β⁻¹ * ‖P (x - z) - x‖) := by field_simp
      _ ≤ β * ‖P (x - β⁻¹ • z) - x‖ := mul_le_mul_of_nonneg_left h2 hβ.le

theorem solution {n m : ℕ} (X : Set (EuclideanSpace ℝ (Fin n))) (hX_cl : IsClosed X) (hX_cvx : Convex ℝ X)
    (P : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hP : SpectralProjGrad.Shared.IsProjOnto X P)
    (f : EuclideanSpace ℝ (Fin m) → ℝ) (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ X) (z : EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β) :
    V P f g x z ≤ max 1 (β ^ 2) * ‖ybar P x z β - x‖ ^ 2 + ‖z - gradF f g x‖ ^ 2 := by
  have h1 := CC_l1 X hX_cl hX_cvx P hP x hx z β hβ
  have hmax : max 1 β ^ 2 = max 1 (β ^ 2) := by
    rcases le_total β 1 with h | h
    · rw [max_eq_left h, max_eq_left (by nlinarith)]; norm_num
    · rw [max_eq_right h, max_eq_right (by nlinarith)]
  have h2 : ‖ybar P x z 1 - x‖ ^ 2 ≤ max 1 (β ^ 2) * ‖ybar P x z β - x‖ ^ 2 := by
    rw [← hmax, ← mul_pow]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  unfold V
  linarith
