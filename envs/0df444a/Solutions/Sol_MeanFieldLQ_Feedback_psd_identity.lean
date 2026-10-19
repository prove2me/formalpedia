-- Prove2me | solution 1 for MeanFieldLQ.Feedback.psd_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-19T08:36:26.944983+00:00
-- url     : https://prove2.me/submissions/8d606f62-4277-4e4e-aa6d-6abea0922901

import Mathlib

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

theorem solution {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (Dt : Matrix (Fin n) (Fin m) ℝ) (Rt : Matrix (Fin m) (Fin m) ℝ) (hR : Rt.PosDef)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hSP : S * S = P) :
    P - P * Dt * (Rt + Dtᵀ * P * Dt)⁻¹ * Dtᵀ * P
        = S * (1 + S * Dt * Rt⁻¹ * Dtᵀ * S)⁻¹ * S ∧
      (P - P * Dt * (Rt + Dtᵀ * P * Dt)⁻¹ * Dtᵀ * P).PosSemidef := by
  subst hSP
  have hSt : Sᵀ = S := by
    have := hS.1.eq
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin n) (Fin m) ℝ, B = S * Dt := ⟨_, rfl⟩
  have hBt : Bᵀ = Dtᵀ * S := by rw [hB, Matrix.transpose_mul, hSt]
  have hBB : Bᵀ * B = Dtᵀ * (S * S) * Dt := by
    rw [hBt, hB]; simp only [Matrix.mul_assoc]
  have hBPSD : (Bᵀ * B).PosSemidef := by
    have := Matrix.posSemidef_conjTranspose_mul_self B
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hK : (Rt + Bᵀ * B).PosDef := hR.add_posSemidef hBPSD
  have hKu : IsUnit (Rt + Bᵀ * B).det := (isUnit_iff_ne_zero.mpr hK.det_pos.ne')
  have hRu : IsUnit Rt.det := (isUnit_iff_ne_zero.mpr hR.det_pos.ne')
  obtain ⟨X, hX⟩ : ∃ X, X = Rt⁻¹ := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = (Rt + Bᵀ * B)⁻¹ := ⟨_, rfl⟩
  have hXR : X * Rt = 1 := by rw [hX]; exact Matrix.nonsing_inv_mul Rt hRu
  have hKY : (Rt + Bᵀ * B) * Y = 1 := by rw [hY]; exact Matrix.mul_nonsing_inv _ hKu
  have h0 : X - Y - X * (Bᵀ * B) * Y = 0 := by
    have h1 : X * ((Rt + Bᵀ * B) * Y) = X := by rw [hKY, mul_one]
    have h2 : X * ((Rt + Bᵀ * B) * Y) = Y + X * (Bᵀ * B) * Y := by
      rw [Matrix.add_mul, Matrix.mul_add, ← Matrix.mul_assoc X Rt, hXR, Matrix.one_mul, Matrix.mul_assoc X (Bᵀ * B) Y]
    rw [h2] at h1
    rw [sub_sub, sub_eq_zero]; exact h1.symm
  have hinv : (1 + B * X * Bᵀ)⁻¹ = 1 - B * Y * Bᵀ := by
    apply Matrix.inv_eq_right_inv
    have : (1 + B * X * Bᵀ) * (1 - B * Y * Bᵀ)
        = 1 + B * (X - Y - X * (Bᵀ * B) * Y) * Bᵀ := by
      simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
      abel
    rw [this, h0]; simp
  have hlhs : S * S - S * S * Dt * (Rt + Dtᵀ * (S * S) * Dt)⁻¹ * Dtᵀ * (S * S)
      = S * (1 - B * Y * Bᵀ) * S := by
    rw [← hBB, ← hY, hBt, hB]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc]
  have hA : S * Dt * Rt⁻¹ * Dtᵀ * S = B * X * Bᵀ := by
    rw [hBt, hB, hX]; simp only [Matrix.mul_assoc]
  have hmain : S * S - S * S * Dt * (Rt + Dtᵀ * (S * S) * Dt)⁻¹ * Dtᵀ * (S * S)
      = S * (1 + S * Dt * Rt⁻¹ * Dtᵀ * S)⁻¹ * S := by
    rw [hlhs, hA, hinv]
  refine ⟨hmain, ?_⟩
  rw [hmain]
  have hXpd : X.PosDef := by rw [hX]; exact hR.inv
  have hApsd : (B * X * Bᵀ).PosSemidef := by
    have := hXpd.posSemidef.mul_mul_conjTranspose_same B
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using this
  have hpd : (1 + B * X * Bᵀ).PosDef := by
    have h1 : (1 : Matrix (Fin n) (Fin n) ℝ).PosDef := Matrix.PosDef.one
    exact h1.add_posSemidef hApsd
  rw [hA]
  have hip : ((1 + B * X * Bᵀ)⁻¹).PosSemidef := hpd.inv.posSemidef
  have := hip.conjTranspose_mul_mul_same S
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hSt] using this
