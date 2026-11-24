-- Prove2me | solution 1 for GlobalTheory.CayleyInv.cayley_transform
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:24:37.187389+00:00
-- url     : https://prove2.me/submissions/1801851d-f01e-431e-9b38-e147189cd8a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutive
import Theorems.Thm_GlobalTheory_CayleyInv_map_mul_map_inv
import Theorems.Thm_GlobalTheory_CayleyInv_map_one_add
import Theorems.Thm_GlobalTheory_CayleyInv_map_one_sub
import Theorems.Thm_GlobalTheory_CayleyInv_one_add_cayley
import Theorems.Thm_GlobalTheory_CayleyInv_one_sub_cayley
import Theorems.Thm_GlobalTheory_CayleyInv_one_add_cayley_mul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
namespace GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
private theorem eq_zero_of_mul_mul_eq_zero_of_isUnit_det (A B X : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * X * B = 0) : X = 0 := by
  calc X = (A⁻¹ * A) * X * (B * B⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
          Matrix.mul_one]
    _ = A⁻¹ * (A * X * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]
private theorem isUnit_det_map_of_isUnit_det (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : IsUnit (M.map σ).det := by
  simpa [RingHom.map_det, RingHom.mapMatrix_apply] using h.map σ
end GlobalTheory.CayleyInv
end

set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.CayleyInv
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.CayleyInv
theorem _root_.solution : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  intro R _ σ n G hσ hG hGu h2
  obtain ⟨c, hc⟩ := h2.exists_right_inv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg hP
    have hSP : (1 - g) * (1 + g)⁻¹ * (1 + g) = 1 - g := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + g)ᵀ) ((1 + g).map σ) _
        (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
      have e1 : (1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ = (1 - g)ᵀ := by
        rw [← Matrix.transpose_mul, hSP]
      have e2 : ((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ = (1 - g).map σ := by
        rw [← Matrix.map_mul, hSP]
      have e3 : (1 - gᵀ) * G * (1 + g.map σ) + (1 + gᵀ) * G * (1 - g.map σ)
          = (G - gᵀ * G * g.map σ) + (G - gᵀ * G * g.map σ) := by noncomm_ring
      calc (1 + g)ᵀ * (((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ)
            * (1 + g).map σ
          = ((1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ) * G * (1 + g).map σ
            + (1 + g)ᵀ * G * (((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (1 - g)ᵀ * G * (1 + g).map σ + (1 + g)ᵀ * G * (1 - g).map σ := by rw [e1, e2]
        _ = 0 := by
            rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
              map_one_add, map_one_sub, e3, hg, sub_self, add_zero]
    · rw [one_add_cayley g hP, Matrix.det_smul]
      exact (h2.pow _).mul (Matrix.isUnit_nonsing_inv_det _ hP)
  · intro g hP
    have hinv : (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = c • (1 + g) :=
      Matrix.inv_eq_right_inv (one_add_cayley_mul g hP c hc)
    rw [hinv, one_sub_cayley g hP, smul_mul_smul_comm, hc, one_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  · intro S hS hP
    have hgP : (1 - S) * (1 + S)⁻¹ * (1 + S) = 1 - S := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [← sub_eq_zero]
    apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + S)ᵀ) ((1 + S).map σ) _
      (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
    have e1 : (1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ = (1 - S)ᵀ := by
      rw [← Matrix.transpose_mul, hgP]
    have e2 : ((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ = (1 - S).map σ := by
      rw [← Matrix.map_mul, hgP]
    have e3 : (1 - Sᵀ) * G * (1 - S.map σ) - (1 + Sᵀ) * G * (1 + S.map σ)
        = -((Sᵀ * G + G * S.map σ) + (Sᵀ * G + G * S.map σ)) := by noncomm_ring
    calc (1 + S)ᵀ * (((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ - G)
          * (1 + S).map σ
        = ((1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ) * G
            * (((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ)
          - (1 + S)ᵀ * G * (1 + S).map σ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (1 - S)ᵀ * G * (1 - S).map σ - (1 + S)ᵀ * G * (1 + S).map σ := by rw [e1, e2]
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
            map_one_add, map_one_sub, e3, hS, add_zero, neg_zero]
  · intro A
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hKG : ((G⁻¹).map σ)ᵀ * G = 1 := by
      calc ((G⁻¹).map σ)ᵀ * G = ((G⁻¹).map σ)ᵀ * (G.map σ)ᵀ := by rw [hG]
        _ = (G.map σ * (G⁻¹).map σ)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [map_mul_map_inv σ G hGu, Matrix.transpose_one]
    have hGK : G * ((G⁻¹).map σ)ᵀ = 1 := by
      rw [← Matrix.inv_eq_left_inv hKG]
      exact Matrix.mul_nonsing_inv _ hGu
    have hAA : (A.map σ).map σ = A := by
      ext i j
      simp [hσ]
    have hT : (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ = Aᵀ - G * A.map σ * G⁻¹ := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose]
    have hTs : (A - (G * A.map σ * G⁻¹)ᵀ).map σ
        = A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G) := by
      rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul,
        hAA, Matrix.transpose_mul, Matrix.transpose_mul, hG]
    rw [hT, hTs]
    calc (Aᵀ - G * A.map σ * G⁻¹) * G + G * (A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G))
        = Aᵀ * G - G * A.map σ * (G⁻¹ * G)
          + (G * A.map σ - (G * ((G⁻¹).map σ)ᵀ) * (Aᵀ * G)) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by
          rw [hGinvG, hGK, Matrix.mul_one, Matrix.one_mul]
          abel
end GlobalTheory.CayleyInv
