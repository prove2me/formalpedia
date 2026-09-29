-- Prove2me | solution 1 for LogRegretOCO.ONS.logdet_potential
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-28T01:59:03.383396+00:00
-- url     : https://prove2.me/submissions/5a407dc6-4c30-4aa7-a621-964a7fd8b39d

import Mathlib

open Matrix
open scoped MatrixOrder

theorem solution {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : (A - B).PosSemidef) (hB : B.PosDef) :
    ∑ i, ∑ j, A⁻¹ i j * (A - B) i j ≤ Real.log (A.det / B.det) := by
  have hA : A.PosDef := by
    have hAeq : A = (A - B) + B := by abel
    refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
    · rw [hAeq]; exact hAB.1.add hB.1
    · have h1 : (0 : ℝ) ≤ star x ⬝ᵥ ((A - B) *ᵥ x) := hAB.dotProduct_mulVec_nonneg x
      have h2 : (0 : ℝ) < star x ⬝ᵥ (B *ᵥ x) := hB.dotProduct_mulVec_pos hx
      have h3 : star x ⬝ᵥ (A *ᵥ x)
          = star x ⬝ᵥ ((A - B) *ᵥ x) + star x ⬝ᵥ (B *ᵥ x) := by
        rw [← dotProduct_add, ← Matrix.add_mulVec, ← hAeq]
      rw [h3]; linarith
  have hdetA : A.det ≠ 0 := ne_of_gt hA.det_pos
  have hdetB : B.det ≠ 0 := ne_of_gt hB.det_pos
  have hAinv : A⁻¹.PosDef := hA.inv
  set S := CFC.sqrt A⁻¹ with hSdef
  have hSpsd : S.PosSemidef := (CFC.sqrt_nonneg A⁻¹).posSemidef
  have hSS : S * S = A⁻¹ := CFC.sqrt_mul_sqrt_self A⁻¹ hAinv.posSemidef.nonneg
  set N := S * B * S with hNdef
  have hSh : Sᴴ = S := hSpsd.1
  have hNpsd : N.PosSemidef := by
    have h := hB.posSemidef.conjTranspose_mul_mul_same S
    rwa [hSh] at h
  have hdetS2 : S.det * S.det = A.det⁻¹ := by
    have h : (S * S).det = A⁻¹.det := by rw [hSS]
    rw [Matrix.det_mul] at h
    rw [h, Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  have hdetN : N.det = A.det⁻¹ * B.det := by
    rw [hNdef, Matrix.det_mul, Matrix.det_mul]
    rw [show S.det * B.det * S.det = (S.det * S.det) * B.det by ring, hdetS2]
  have hdetNpos : 0 < N.det := by
    rw [hdetN]
    exact mul_pos (inv_pos.mpr hA.det_pos) hB.det_pos
  have hNpd : N.PosDef :=
    hNpsd.posDef_iff_isUnit.mpr
      (Matrix.isUnit_iff_isUnit_det N |>.mpr (isUnit_iff_ne_zero.mpr (ne_of_gt hdetNpos)))
  -- rewrite the left-hand side as a trace
  have hlhs : ∑ i, ∑ j, A⁻¹ i j * (A - B) i j = (A⁻¹ * (A - B)).trace := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := hAB.1.apply j i
    simp only [star_trivial] at h
    rw [h]
  have htrAB : (A⁻¹ * B).trace = N.trace := by
    rw [← hSS, hNdef, Matrix.mul_assoc]
    exact (Matrix.trace_mul_comm (S * B) S).symm
  have htr : (A⁻¹ * (A - B)).trace = (n : ℝ) - N.trace := by
    rw [Matrix.mul_sub, Matrix.trace_sub,
      Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hdetA), Matrix.trace_one, htrAB]
    simp
  -- eigenvalue computation
  have hev : ∀ i, 0 < hNpsd.1.eigenvalues i := fun i => hNpd.eigenvalues_pos i
  have htrN : N.trace = ∑ i, hNpsd.1.eigenvalues i := by
    have h := hNpsd.1.trace_eq_sum_eigenvalues
    simpa using h
  have hdetNeig : N.det = ∏ i, hNpsd.1.eigenvalues i := by
    have h := hNpsd.1.det_eq_prod_eigenvalues
    simpa using h
  have hlogN : Real.log N.det = ∑ i, Real.log (hNpsd.1.eigenvalues i) := by
    rw [hdetNeig]
    exact Real.log_prod fun i _ => ne_of_gt (hev i)
  have hrhs : Real.log (A.det / B.det) = -Real.log N.det := by
    rw [hdetN, Real.log_mul (inv_ne_zero hdetA) hdetB, Real.log_inv,
      Real.log_div hdetA hdetB]
    ring
  rw [hlhs, htr, hrhs, hlogN, htrN]
  have hsum : ∑ i, Real.log (hNpsd.1.eigenvalues i)
      ≤ ∑ i : Fin n, (hNpsd.1.eigenvalues i - 1) :=
    Finset.sum_le_sum fun i _ => Real.log_le_sub_one_of_pos (hev i)
  rw [Finset.sum_sub_distrib] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsum
  linarith
