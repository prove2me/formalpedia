-- Prove2me | solution 1 for MinRankRecovery.Recovery.lemma_2_3
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-07T09:16:48.733446+00:00
-- url     : https://prove2.me/submissions/e4cf2d18-e54d-4cf1-842f-fdba3dc355c9

import Mathlib
import Definitions.Def_HighDimStat_MatrixRank_Core

open Matrix HighDimStat.MatrixRank
open scoped MatrixOrder
set_option maxHeartbeats 40000

private theorem trace_sqrt {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosSemidef) :
    (CFC.sqrt A).trace = ∑ j, Real.sqrt (hA.1.eigenvalues₀
      ((finCongr (Fintype.card_fin n)).symm j)) := by
  classical
  rw [CFC.sqrt_eq_cfc, cfc_nnreal_eq_real _ A, hA.1.cfc_eq]
  simp only [IsHermitian.cfc, Unitary.conjStarAlgAut_apply]
  rw [Matrix.trace_mul_cycle]
  simp only [Unitary.star_mul_self_of_mem (SetLike.coe_mem _), Matrix.one_mul,
    Matrix.trace_diagonal]
  simp only [Function.comp_apply, Real.coe_sqrt, Real.coe_toNNReal', RCLike.ofReal_real_eq_id,
    id_eq, max_eq_left (hA.eigenvalues_nonneg _)]
  unfold Matrix.IsHermitian.eigenvalues
  rw [← (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin n)))).sum_comp]
  rw [← (finCongr (Fintype.card_fin n)).sum_comp]
  simp only [Equiv.symm_apply_apply]

private theorem sqrt_mul_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosSemidef) (h : A * B = 0) : CFC.sqrt A * B = 0 := by
  apply Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp
  have hs : (CFC.sqrt A)ᵀ = CFC.sqrt A :=
    (CFC.sqrt_nonneg A).posSemidef.1
  rw [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul, hs, Matrix.mul_assoc,
    ← Matrix.mul_assoc (CFC.sqrt A), CFC.sqrt_mul_sqrt_self A hA.nonneg,
    h, Matrix.mul_zero, Matrix.trace_zero]

theorem solution {m n : ℕ} (M N : Matrix (Fin m) (Fin n) ℝ) (h1 : M * Nᵀ = 0)
    (h2 : Mᵀ * N = 0) :
    nuclearNorm (M + N) = nuclearNorm M + nuclearNorm N := by
  classical
  let A := Mᵀ * M
  let B := Nᵀ * N
  have hA : A.PosSemidef := by simpa [A] using Matrix.posSemidef_conjTranspose_mul_self M
  have hB : B.PosSemidef := by simpa [B] using Matrix.posSemidef_conjTranspose_mul_self N
  have hab : A * B = 0 := by
    dsimp [A, B]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc M, h1, Matrix.zero_mul, Matrix.mul_zero]
  have hba : B * A = 0 := by
    have hh := congrArg Matrix.transpose hab
    have hAt : Aᵀ = A := hA.1
    have hBt : Bᵀ = B := hB.1
    rw [Matrix.transpose_mul, hAt, hBt, Matrix.transpose_zero] at hh
    exact hh
  have hsa := sqrt_mul_zero A B hA hab
  have hsb := sqrt_mul_zero B (CFC.sqrt A) hB (by
    have hh := congrArg Matrix.transpose hsa
    have hBt : Bᵀ = B := hB.1
    have hAt : (CFC.sqrt A)ᵀ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
    rw [Matrix.transpose_mul, hAt, hBt, Matrix.transpose_zero] at hh
    exact hh)
  have hsab : CFC.sqrt A * CFC.sqrt B = 0 := by
    have hh := congrArg Matrix.transpose hsb
    have hAt : (CFC.sqrt A)ᵀ = CFC.sqrt A := (CFC.sqrt_nonneg A).posSemidef.1
    have hBt : (CFC.sqrt B)ᵀ = CFC.sqrt B := (CFC.sqrt_nonneg B).posSemidef.1
    rw [Matrix.transpose_mul, hAt, hBt, Matrix.transpose_zero] at hh
    exact hh
  have hsum : CFC.sqrt (A + B) = CFC.sqrt A + CFC.sqrt B := by
    apply CFC.sqrt_unique
    · rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hsab, hsb,
        CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
      simp
    · exact add_nonneg (CFC.sqrt_nonneg A) (CFC.sqrt_nonneg B)
  have hgram : (M + N)ᵀ * (M + N) = A + B := by
    have hnm : Nᵀ * M = 0 := by
      simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero]
        using congrArg Matrix.transpose h2
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, h2, hnm, add_zero, zero_add]
    rfl
  have hnuc (X : Matrix (Fin m) (Fin n) ℝ) :
      nuclearNorm X = (CFC.sqrt (Xᵀ * X)).trace := by
    exact (trace_sqrt (Xᵀ * X)
      (by simpa using Matrix.posSemidef_conjTranspose_mul_self X)).symm
  rw [hnuc, hgram, hsum, Matrix.trace_add, hnuc M, hnuc N]

#print axioms solution
