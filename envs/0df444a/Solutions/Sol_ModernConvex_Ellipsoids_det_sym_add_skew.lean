-- Prove2me | solution 1 for ModernConvex.Ellipsoids.det_sym_add_skew
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:51:23.298139+00:00
-- url     : https://prove2.me/submissions/8898a256-2698-4ddf-ad01-798a1114b1e5

import Mathlib

open Matrix
open scoped MatrixOrder

theorem g69a2_one_le_det {k : ℕ} (P : Matrix (Fin k) (Fin k) ℝ) (hP : P.PosSemidef) :
    1 ≤ (1 + P).det := by
  have hspec := hP.1.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hspec
  set U := hP.1.eigenvectorUnitary
  set D : Matrix (Fin k) (Fin k) ℝ := diagonal (RCLike.ofReal ∘ hP.1.eigenvalues)
  have hUU : (U : Matrix (Fin k) (Fin k) ℝ) * star (U : Matrix (Fin k) (Fin k) ℝ) = 1 :=
    Unitary.coe_mul_star_self U
  have h1 : 1 + P = (U : Matrix (Fin k) (Fin k) ℝ) * (1 + D) * star (U : Matrix (Fin k) (Fin k) ℝ) := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hspec]
  have hdU : (U : Matrix (Fin k) (Fin k) ℝ).det * (star (U : Matrix (Fin k) (Fin k) ℝ)).det = 1 := by
    rw [← det_mul, hUU, det_one]
  rw [h1, det_mul, det_mul, mul_comm (det (U : Matrix (Fin k) (Fin k) ℝ)), mul_assoc, hdU, mul_one]
  have hD : 1 + D = diagonal (fun i => 1 + hP.1.eigenvalues i) := by
    ext i j
    by_cases h : i = j
    · subst h; simp [D]
    · simp [D, diagonal_apply_ne _ h, one_apply_ne h]
  rw [hD, det_diagonal]
  calc (1:ℝ) = ∏ _i : Fin k, (1:ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => by
        have := hP.eigenvalues_nonneg i; linarith)

theorem g69a2_det_main {k : ℕ} (S C : Matrix (Fin k) (Fin k) ℝ) (hS : S.PosDef)
    (hC : Cᵀ = -C) : S.det ≤ |(S + C).det| := by
  have h0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ S := hS.posSemidef.nonneg
  have h1 : CFC.sqrt S * CFC.sqrt S = S := CFC.sqrt_mul_sqrt_self S h0
  have hR : (CFC.sqrt S).PosSemidef := (CFC.sqrt_nonneg S).posSemidef
  have h2 : (CFC.sqrt S)ᵀ = CFC.sqrt S := by
    have := hR.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  set R := CFC.sqrt S
  have hdet : R.det ≠ 0 := by
    intro h
    have := hS.det_pos
    rw [← h1, det_mul, h, zero_mul] at this
    exact lt_irrefl _ this
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  set K := R⁻¹ * C * R⁻¹ with hK
  have hRi : (R⁻¹)ᵀ = R⁻¹ := by rw [transpose_nonsing_inv, h2]
  have hKT : Kᵀ = -K := by
    rw [hK, transpose_mul, transpose_mul, hRi, hC, Matrix.neg_mul, Matrix.mul_neg,
      Matrix.mul_assoc]
  have hSC : S + C = R * (1 + K) * R := by
    rw [hK, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, h1]
    congr 1
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul,
      Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
  have hsq : 1 ≤ (1 + K).det * (1 + K).det := by
    have e1 : (1 + K).det = (1 - K).det := by
      rw [← det_transpose, transpose_add, transpose_one, hKT, sub_eq_add_neg]
    have e2 : (1 + K) * (1 - K) = 1 + Kᵀ * K := by
      rw [hKT, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul, Matrix.neg_mul]
      abel
    conv_lhs => skip
    nth_rewrite 2 [e1]
    rw [← det_mul, e2]
    apply g69a2_one_le_det
    have := posSemidef_conjTranspose_mul_self K
    rwa [conjTranspose_eq_transpose_of_trivial] at this
  have habs : 1 ≤ |(1 + K).det| := by
    by_contra h
    push Not at h
    have := abs_mul_abs_self (1 + K).det
    have h0 := abs_nonneg (1 + K).det
    nlinarith
  have hdS : S.det = R.det * R.det := by rw [← det_mul, h1]
  have hSpos := hS.det_pos
  rw [hSC, det_mul, det_mul, abs_mul, abs_mul]
  have : |R.det| * |(1 + K).det| * |R.det| = S.det * |(1 + K).det| := by
    rw [hdS, show |R.det| * |(1 + K).det| * |R.det| = (|R.det| * |R.det|) * |(1 + K).det| by ring,
      abs_mul_abs_self]
  rw [this]
  nlinarith


/-- Ben-Tal–Nemirovski, Lemma 4.9.1, p. 273. Let `Y = S + C` be a square matrix represented as the
sum of a symmetric matrix `S` and a skew-symmetric (`Cᵀ = −C`) matrix `C`. Assume that `S` is
positive definite. Then `|Det(Y)| ≥ Det(S)`. -/
theorem solution {n : ℕ} (S C : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosDef)
    (hC : Cᵀ = -C) :
    S.det ≤ |(S + C).det| := g69a2_det_main S C hS hC

