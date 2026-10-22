-- Prove2me | solution 1 for ModernConvex.PathFollowing.dist_sq_eq_trace
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T12:29:13.204226+00:00
-- url     : https://prove2.me/submissions/8b040a41-135b-44bf-8847-4273e6bcabf2

import Mathlib
import Definitions.Def_ModernConvex_PathFollowing_SDP

open Matrix
open scoped MatrixOrder
open ModernConvex.PathFollowing
theorem g69a2_sqrt_facts {k : ℕ} (X : Matrix (Fin k) (Fin k) ℝ) (hX : X.PosDef) :
    CFC.sqrt X * CFC.sqrt X = X ∧ (CFC.sqrt X)ᵀ = CFC.sqrt X ∧
      CFC.sqrt X * X⁻¹ * CFC.sqrt X = 1 := by
  have h0 : (0 : Matrix (Fin k) (Fin k) ℝ) ≤ X := hX.posSemidef.nonneg
  have h1 : CFC.sqrt X * CFC.sqrt X = X := CFC.sqrt_mul_sqrt_self X h0
  have hR : (CFC.sqrt X).PosSemidef := (CFC.sqrt_nonneg X).posSemidef
  have h2 : (CFC.sqrt X)ᵀ = CFC.sqrt X := by
    have := hR.1
    rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
  refine ⟨h1, h2, ?_⟩
  set R := CFC.sqrt X
  have hdet : R.det ≠ 0 := by
    intro h
    have := hX.det_pos
    rw [← h1, det_mul, h, zero_mul] at this
    exact lt_irrefl _ this
  have hu : IsUnit R.det := isUnit_iff_ne_zero.mpr hdet
  have hXi : X⁻¹ = R⁻¹ * R⁻¹ := by rw [← h1, Matrix.mul_inv_rev]
  rw [hXi, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one,
    Matrix.mul_nonsing_inv _ hu]

theorem g69a2_frob_sq {k : ℕ} (M : Matrix (Fin k) (Fin k) ℝ) (hM : Mᵀ = M) :
    frobNorm M ^ 2 = (M * M).trace := by
  unfold frobNorm
  refine (Real.sq_sqrt (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _)).trans ?_
  conv_rhs => rw [show M * M = M * Mᵀ by rw [hM]]
  simp [trace, mul_apply, sq]

theorem g69a2_dist_sq {k : ℕ} (t : ℝ) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : X.PosDef) (hS : S.IsHermitian) :
    (X * (t • S - X⁻¹) * X * (t • S - X⁻¹)).trace = centralPathDist t X S ^ 2 := by
  obtain ⟨h1, h2, h3⟩ := g69a2_sqrt_facts X hX
  set R := CFC.sqrt X
  set A := t • S - X⁻¹ with hA
  have hAT : Aᵀ = A := by
    have hS' : Sᵀ = S := by
      have := hS; rwa [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
    have hXi : (X⁻¹)ᵀ = X⁻¹ := by
      rw [transpose_nonsing_inv]
      have := hX.1; rw [IsHermitian, conjTranspose_eq_transpose_of_trivial] at this
      rw [this]
    rw [hA, transpose_sub, transpose_smul, hS', hXi]
  have hM : t • (R * S * R) - 1 = R * A * R := by
    rw [hA, Matrix.mul_sub, Matrix.sub_mul, ← h3, Matrix.mul_smul, Matrix.smul_mul]
  have hMT : (R * A * R)ᵀ = R * A * R := by
    rw [transpose_mul, transpose_mul, h2, hAT, Matrix.mul_assoc]
  rw [show centralPathDist t X S = frobNorm (R * A * R) by unfold centralPathDist; rw [hM]]
  rw [g69a2_frob_sq _ hMT]
  symm
  calc (R * A * R * (R * A * R)).trace = (R * (A * (R * R) * A * R)).trace := by
        simp only [Matrix.mul_assoc]
    _ = ((A * (R * R) * A * R) * R).trace := trace_mul_comm _ _
    _ = ((A * X * A) * X).trace := by
        rw [Matrix.mul_assoc (A * (R * R) * A) R R, h1]
    _ = (X * (A * X * A)).trace := trace_mul_comm _ _
    _ = _ := by simp only [Matrix.mul_assoc]


/-- Ben-Tal–Nemirovski, (6.4.11), p. 395: in the SDP case, for `t > 0` and positive definite
`X, S`, `Tr(X(tS − X⁻¹)X(tS − X⁻¹)) = ‖tX^{1/2}SX^{1/2} − I‖₂²`, `X^{1/2}` the positive
semidefinite square root of `X`, `‖·‖₂` the Frobenius norm. -/
theorem solution {k : ℕ} (t : ℝ) (ht : 0 < t) (X S : Matrix (Fin k) (Fin k) ℝ)
    (hX : X.PosDef) (hS : S.PosDef) :
    (X * (t • S - X⁻¹) * X * (t • S - X⁻¹)).trace = centralPathDist t X S ^ 2 := g69a2_dist_sq t X S hX hS.1

