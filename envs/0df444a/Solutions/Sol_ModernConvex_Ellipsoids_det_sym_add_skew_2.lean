-- Prove2me | solution 2 for ModernConvex.Ellipsoids.det_sym_add_skew
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:47:43.930161+00:00
-- url     : https://prove2.me/submissions/4f94ea13-7646-4d3a-b1b3-e551a65b17d8

import Mathlib
set_option autoImplicit false
open Matrix
open scoped MatrixOrder

theorem solution {n : ℕ} (S C : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (hC : Cᵀ = -C) :
    S.det ≤ |(S + C).det| := by
  have L : ∀ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef → 1 ≤ (1 + P).det := by
    intro P hP
    have hs := hP.isHermitian.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    set U := hP.isHermitian.eigenvectorUnitary with hU
    set D : Matrix (Fin n) (Fin n) ℝ := diagonal (RCLike.ofReal ∘ hP.isHermitian.eigenvalues) with hD
    have hUU : (star (U : Matrix (Fin n) (Fin n) ℝ)) * (U : Matrix (Fin n) (Fin n) ℝ) = 1 :=
      Unitary.coe_star_mul_self U
    have h1 : (1 + P).det = (1 + D).det := by
      rw [hs, mul_assoc, Matrix.det_one_add_mul_comm, mul_assoc D, hUU]
      simp
    rw [h1, hD]
    have : (1 : Matrix (Fin n) (Fin n) ℝ) + diagonal (RCLike.ofReal ∘ hP.isHermitian.eigenvalues)
        = diagonal (fun i => 1 + hP.isHermitian.eigenvalues i) := by
      rw [← diagonal_one, diagonal_add]; rfl
    rw [this, det_diagonal]
    calc (1 : ℝ) = ∏ _i : Fin n, (1 : ℝ) := by simp
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one)
          (fun i _ => by linarith [hP.eigenvalues_nonneg i])
  -- skew matrices: |det (1 + K)| ≥ 1
  have Lskew : ∀ K : Matrix (Fin n) (Fin n) ℝ, Kᵀ = -K → 1 ≤ |(1 + K).det| := by
    intro K hK
    have h1 : (1 + K).det * (1 + K).det = (1 + Kᵀ * K).det := by
      have e1 : (1 + K).det = (1 + Kᵀ).det := by
        rw [← det_transpose, transpose_add, transpose_one]
      calc (1 + K).det * (1 + K).det = (1 + K).det * (1 + Kᵀ).det := by rw [← e1]
        _ = ((1 + K) * (1 + Kᵀ)).det := (det_mul _ _).symm
        _ = (1 + Kᵀ * K).det := by
          rw [hK]
          congr 1
          noncomm_ring
    have h2 : 1 ≤ (1 + Kᵀ * K).det := L _ (by simpa using posSemidef_conjTranspose_mul_self K)
    have h3 : 1 ≤ (1 + K).det * (1 + K).det := h1 ▸ h2
    by_contra hlt
    have hlt := not_le.mp hlt
    have := abs_nonneg (1 + K).det
    have : (1 + K).det * (1 + K).det = |(1 + K).det| * |(1 + K).det| := (abs_mul_abs_self _).symm
    nlinarith
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hS.posSemidef.nonneg
  have hBt : star B = Bᵀ := by simp [star_eq_conjTranspose]
  rw [hBt] at hB
  have hdetS : S.det = B.det * B.det := by rw [hB, det_mul, det_transpose]
  have hdetpos : 0 < S.det := hS.det_pos
  have hBdet : B.det ≠ 0 := by
    intro h; rw [h] at hdetS; simp at hdetS; linarith
  have hBu : IsUnit B.det := isUnit_iff_ne_zero.mpr hBdet
  have hBtu : IsUnit Bᵀ.det := by rw [det_transpose]; exact hBu
  set K := (Bᵀ)⁻¹ * C * B⁻¹ with hKdef
  have hK : Kᵀ = -K := by
    rw [hKdef, transpose_mul, transpose_mul, transpose_nonsing_inv, transpose_nonsing_inv, transpose_transpose, hC]
    simp [mul_assoc]
  have hSC : S + C = Bᵀ * (1 + K) * B := by
    rw [hKdef, mul_add, add_mul, mul_one, ← hB]
    congr 1
    rw [← mul_assoc, ← mul_assoc, mul_nonsing_inv _ hBtu, one_mul, mul_assoc, nonsing_inv_mul _ hBu, mul_one]
  have h1 := Lskew K hK
  rw [hSC, det_mul, det_mul, det_transpose, abs_mul, abs_mul, hdetS]
  nlinarith [abs_mul_abs_self B.det, abs_nonneg B.det, abs_nonneg (1 + K).det,
    mul_nonneg (mul_nonneg (abs_nonneg B.det) (abs_nonneg B.det)) (sub_nonneg.2 h1)]
