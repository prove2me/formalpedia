-- Prove2me | solution 1 for IncentiveFinNet.trace_identity
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-11T21:05:14.272202+00:00
-- url     : https://prove2.me/submissions/9282002d-6e09-4400-878c-a2ca35751e07

import Mathlib
import Definitions.Def_IncentiveFinNet_matC

open Matrix

open IncentiveFinNet in
theorem solution {n : ℕ} (Q : Fin n → Matrix (Fin n) (Fin n) ℝ) (hQ : ∀ i, (Q i)ᵀ = Q i) (R P : Matrix (Fin n) (Fin n) ℝ) (hR : ∀ k l, ¬ k < l → R k l = 0) (hP : P = R - Rᵀ) (i j : Fin n) : (Q j * P - (Q i * P)ᵀ) i j = (Q j * P + P * Q i) i j ∧ (Q j * P + P * Q i) i j = (P * (vecMulVec (Pi.single j 1) (Pi.single i 1) * Q j + Q i * vecMulVec (Pi.single j 1) (Pi.single i 1))).trace ∧ (P * (vecMulVec (Pi.single j 1) (Pi.single i 1) * Q j + Q i * vecMulVec (Pi.single j 1) (Pi.single i 1))).trace = ((R - Rᵀ) * (matB Q j i + (matB Q i j)ᵀ)).trace ∧ ((R - Rᵀ) * (matB Q j i + (matB Q i j)ᵀ)).trace = (Rᵀ * matC Q i j).trace ∧ (Rᵀ * matC Q i j).trace = ∑ k, ∑ l, if k < l then R k l * matC Q i j k l else 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h1 : (Q i * P)ᵀ = -(P * Q i) := by
      rw [transpose_mul, hQ, hP, transpose_sub, transpose_transpose, ← neg_sub, Matrix.neg_mul]
    rw [h1, sub_neg_eq_add]
  · rw [← single_eq_single_vecMulVec_single, Matrix.mul_add, Matrix.trace_add, Matrix.add_apply]
    have e1 : (P * (single j i (1:ℝ) * Q j)).trace = (Q j * P) i j := by
      rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.trace_single_mul, one_smul]
    have e2 : (P * (Q i * single j i (1:ℝ))).trace = (P * Q i) i j := by
      rw [← Matrix.mul_assoc, Matrix.trace_mul_single]
      simp
    rw [e1, e2]
  · have h2 : (matB Q i j)ᵀ = Q i * vecMulVec (Pi.single j 1) (Pi.single i 1) := by
      unfold matB
      rw [transpose_mul, hQ, transpose_vecMulVec]
    rw [h2, hP]
    rfl
  · obtain ⟨X, hX⟩ : ∃ X, X = matB Q j i + (matB Q i j)ᵀ := ⟨_, rfl⟩
    have hC : matC Q i j = Xᵀ - X := by
      unfold matC
      rw [hX, transpose_sub, transpose_add, transpose_transpose]
      abel
    rw [← hX, hC, Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub, Matrix.trace_sub, ← Matrix.transpose_mul,
      Matrix.trace_transpose, Matrix.trace_mul_comm X R]
  · rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    refine Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => ?_))
    by_cases hkl : k < l
    · rw [if_pos hkl]
    · rw [if_neg hkl, hR k l hkl, zero_mul]
