-- Prove2me | solution 1 for GlobalTheory.exists_dual_pair_isUnit_det_blocks
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:19:05.638938+00:00
-- url     : https://prove2.me/submissions/9ec610e7-1652-4488-a35c-b8670de4a432

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsDualPairIsUnitDetBlocks
import Theorems.Thm_GlobalTheory_exists_isUnit_det_toBlocks_add_mul
import Theorems.Thm_GlobalTheory_isUnit_det_of_dual_blocks
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open scoped Matrix
namespace GlobalTheory
private lemma blocks_conj_eq_fromBlocks_sums {R : Type} [CommRing R] {n : ℕ}
    (G : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R) :
    Matrix.fromBlocks 1 1 1 (-1) * G * Matrix.fromBlocks 1 1 1 (-1) =
      Matrix.fromBlocks (G.toBlocks₁₁ + G.toBlocks₁₂ + G.toBlocks₂₁ + G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ + G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ + G.toBlocks₁₂ - G.toBlocks₂₁ - G.toBlocks₂₂)
        (G.toBlocks₁₁ - G.toBlocks₁₂ - G.toBlocks₂₁ + G.toBlocks₂₂) := by
  conv_lhs => rw [← Matrix.fromBlocks_toBlocks G]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  congr 1 <;> noncomm_ring
private lemma H_affine_combination_eq_of_quadratic_relation {R : Type} [CommRing R] {n : ℕ}
    (S a11 a12 a21 a22 b11 b12 b21 b22 X₁ X₂ : Matrix (Fin n) (Fin n) R)
    (E11 : a11ᵀ * S * b11 - a21ᵀ * S * b21 = S) (E12 : a11ᵀ * S * b12 - a21ᵀ * S * b22 = 0)
    (E21 : a12ᵀ * S * b11 - a22ᵀ * S * b21 = 0) (E22 : a12ᵀ * S * b12 - a22ᵀ * S * b22 = -S)
    (hX : X₁ᵀ * S + S * X₂ = 0) :
    (a11 + a12 + a21 + a22 + X₁ * (a11 + a12 - a21 - a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 + a12 - a21 - a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = 0 ∧
      (a11 - a12 + a21 - a22 + X₁ * (a11 - a12 - a21 + a22))ᵀ * (S * (b11 + b12 - b21 - b22)) +
        (a11 - a12 - a21 + a22)ᵀ *
          (S * (b11 + b12 + b21 + b22 + X₂ * (b11 + b12 - b21 - b22))) = S + S + S + S := by
  simp only [Matrix.transpose_add, Matrix.transpose_sub, Matrix.transpose_mul]
  constructor
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) +
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) + (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ + a12ᵀ - a21ᵀ - a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) := by
          noncomm_ring
      _ = 0 := by rw [E11, E12, E21, E22, hX]; noncomm_ring
  · calc _ = ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          ((a11ᵀ * S * b11 - a21ᵀ * S * b21 - S) + (a11ᵀ * S * b12 - a21ᵀ * S * b22) -
            (a12ᵀ * S * b11 - a22ᵀ * S * b21) - (a12ᵀ * S * b12 - a22ᵀ * S * b22 + S)) +
          (a11ᵀ - a12ᵀ - a21ᵀ + a22ᵀ) * (X₁ᵀ * S + S * X₂) * (b11 + b12 - b21 - b22) +
          (S + S + S + S) := by
          noncomm_ring
      _ = S + S + S + S := by rw [E11, E12, E21, E22, hX]; noncomm_ring
end GlobalTheory
end

set_option autoImplicit false
open scoped Matrix
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  intro R _ _ h2 n S hS G₁ G₂ hG₁ hG
  classical
  have hKdet : IsUnit (Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (1 : Matrix (Fin n) (Fin n) R)
      (1 : Matrix (Fin n) (Fin n) R) (-1 : Matrix (Fin n) (Fin n) R)).det := by
    rw [Matrix.det_fromBlocks_one₁₁]
    have e : (-1 - 1 * 1 : Matrix (Fin n) (Fin n) R) = (-2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
      ext i j
      simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.one_mul, Matrix.smul_apply, smul_eq_mul,
        Matrix.one_apply]
      split_ifs <;> ring
    rw [e, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin]
    exact h2.neg.pow n
  obtain ⟨X₁, hX₁⟩ := exists_isUnit_det_toBlocks_add_mul
    (Matrix.fromBlocks 1 1 1 (-1) * G₁ * Matrix.fromBlocks 1 1 1 (-1))
    (by rw [Matrix.det_mul, Matrix.det_mul]; exact (hKdet.mul hG₁).mul hKdet)
  rw [blocks_conj_eq_fromBlocks_sums, Matrix.toBlocks_fromBlocks₁₁, Matrix.toBlocks_fromBlocks₂₁] at hX₁
  have hsum : X₁ᵀ * S + S * -(S⁻¹ * X₁ᵀ * S) = 0 := by
    rw [Matrix.mul_neg, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hS,
      Matrix.one_mul, add_neg_cancel]
  refine ⟨X₁, -(S⁻¹ * X₁ᵀ * S), hsum, hX₁, ?_⟩
  have hG' := hG
  rw [← Matrix.fromBlocks_toBlocks G₁, ← Matrix.fromBlocks_toBlocks G₂, Matrix.fromBlocks_transpose,
    Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply] at hG'
  obtain ⟨e11, e12, e21, e22⟩ := Matrix.fromBlocks_inj.mp hG'
  have E11 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₁ = S := by
    convert e11 using 1; noncomm_ring
  have E12 : G₁.toBlocks₁₁ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₁ᵀ * S * G₂.toBlocks₂₂ = 0 := by
    convert e12 using 1; noncomm_ring
  have E21 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₁ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₁ = 0 := by
    convert e21 using 1; noncomm_ring
  have E22 : G₁.toBlocks₁₂ᵀ * S * G₂.toBlocks₁₂ - G₁.toBlocks₂₂ᵀ * S * G₂.toBlocks₂₂ = -S := by
    convert e22 using 1; noncomm_ring
  obtain ⟨c1, c2⟩ := H_affine_combination_eq_of_quadratic_relation S _ _ _ _ _ _ _ _ X₁ _ E11 E12 E21 E22 hsum
  have h4 : IsUnit (4 : R) := by
    have := h2.mul h2
    norm_num at this
    exact this
  have hU4 : IsUnit (S + S + S + S).det := by
    have e : S + S + S + S = (4 : R) • S := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
      ring
    rw [e, Matrix.det_smul]
    exact (h4.pow _).mul hS
  rw [← c2] at hU4
  exact isUnit_det_of_dual_blocks S _ _ _ _ _ _ hX₁ c1 hU4
end GlobalTheory
