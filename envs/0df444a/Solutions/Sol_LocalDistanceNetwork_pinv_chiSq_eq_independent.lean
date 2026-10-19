-- Prove2me | solution 1 for LocalDistanceNetwork.pinv_chiSq_eq_independent
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:00:18.578566+00:00
-- url     : https://prove2.me/submissions/a570e2f7-643b-4ac0-bd15-b145e9fa2f46

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix
open LocalDistanceNetwork

theorem solution {m k n : Type*} [Fintype m] [Fintype k] [Fintype n]
    [DecidableEq k] [DecidableEq n]
    (S : Matrix k k ℝ) (hS : S.PosDef)
    (B : Matrix m k ℝ) (hB : Function.Injective B.mulVec)
    (A₀ : Matrix k n ℝ) (Z : k → ℝ)
    (P : Matrix m m ℝ) (hP : IsMoorePenroseInverse (B * S * Bᵀ) P) :
    (∀ X : n → ℝ, glsObjective (B * A₀) P (B *ᵥ Z) X = glsObjective A₀ S⁻¹ Z X) ∧
    glsEstimate (B * A₀) P (B *ᵥ Z) = glsEstimate A₀ S⁻¹ Z := by
  have hBt : Bᴴ = Bᵀ := conjTranspose_eq_transpose_of_trivial B
  have hH : (Bᵀ * B).PosDef := by rw [← hBt]; exact PosDef.conjTranspose_mul_self B hB
  have hHu : IsUnit (Bᵀ * B).det := (isUnit_iff_isUnit_det _).1 hH.isUnit
  set L := (Bᵀ * B)⁻¹ * Bᵀ
  have hL : L * B = 1 := by
    simp only [L, Matrix.mul_assoc]; exact nonsing_inv_mul _ hHu
  have hLt : Bᵀ * Lᵀ = 1 := by rw [← transpose_mul, hL, transpose_one]
  have hSu : IsUnit S.det := (isUnit_iff_isUnit_det _).1 hS.isUnit
  have key : Bᵀ * P * B = S⁻¹ := by
    have h1 := hP.1
    have h2 : L * (B * S * Bᵀ * P * (B * S * Bᵀ)) * Lᵀ = L * (B * S * Bᵀ) * Lᵀ := by rw [h1]
    have h3 : S * (Bᵀ * P * B) * S = S := by
      have e1 : L * (B * S * Bᵀ * P * (B * S * Bᵀ)) * Lᵀ
          = (L * B) * S * (Bᵀ * P * B) * S * (Bᵀ * Lᵀ) := by simp only [Matrix.mul_assoc]
      have e2 : L * (B * S * Bᵀ) * Lᵀ = (L * B) * S * (Bᵀ * Lᵀ) := by simp only [Matrix.mul_assoc]
      rw [e1, e2, hL, hLt] at h2
      simpa using h2
    calc Bᵀ * P * B = S⁻¹ * (S * (Bᵀ * P * B) * S) * S⁻¹ := by
          rw [show S⁻¹ * (S * (Bᵀ * P * B) * S) * S⁻¹
              = (S⁻¹ * S) * (Bᵀ * P * B) * (S * S⁻¹) by simp only [Matrix.mul_assoc],
            nonsing_inv_mul _ hSu, mul_nonsing_inv _ hSu, Matrix.one_mul, Matrix.mul_one]
      _ = S⁻¹ := by rw [h3, nonsing_inv_mul _ hSu, Matrix.one_mul]
  constructor
  · intro X
    unfold glsObjective
    rw [← mulVec_mulVec, ← mulVec_sub]
    set w := Z - A₀ *ᵥ X
    rw [← key, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec w Bᵀ, vecMul_transpose]
  · unfold glsEstimate glsEstimatorMatrix
    have e1 : (B * A₀)ᵀ * P * (B * A₀) = A₀ᵀ * (Bᵀ * P * B) * A₀ := by
      simp only [transpose_mul, Matrix.mul_assoc]
    have e2 : (((B * A₀)ᵀ * P * (B * A₀))⁻¹ * (B * A₀)ᵀ * P) *ᵥ (B *ᵥ Z)
        = (((B * A₀)ᵀ * P * (B * A₀))⁻¹ * A₀ᵀ * (Bᵀ * P * B)) *ᵥ Z := by
      rw [mulVec_mulVec]; simp only [transpose_mul, Matrix.mul_assoc]
    rw [e2, e1, key]
