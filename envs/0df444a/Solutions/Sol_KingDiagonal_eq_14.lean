-- Prove2me | solution 1 for KingDiagonal.eq_14
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T04:08:54.172471+00:00
-- url     : https://prove2.me/submissions/c27ba5c8-e2b7-4979-b0b9-9443fb75997a

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P48

open QAlgorithms QAlgorithms.Papers.Independent.Claimed50.P48
open scoped Matrix Kronecker

theorem solution {n k m : Type*} [Fintype n] [DecidableEq n] [Fintype k] [DecidableEq k]
    [Fintype m] [DecidableEq m] (Ψ : Superop k m) (hΨ : FiniteKrausCP Ψ)
    (A : Matrix n n ℂ) (τ : Matrix (n × k) (n × k) ℂ) :
    superopTensor (id : Superop n n) Ψ ((A ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix k k ℂ)) ⊙ τ) =
      (A ⊗ₖ (Matrix.of fun _ _ => (1 : ℂ) : Matrix m m ℂ)) ⊙
        superopTensor (id : Superop n n) Ψ τ := by
  ext ⟨i, p⟩ ⟨j, q⟩
  simp only [superopTensor, Matrix.hadamard_apply, Matrix.kronecker_apply, Matrix.of_apply,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, id]
  apply Finset.sum_congr rfl; intro a _
  apply Finset.sum_congr rfl; intro b _
  apply Finset.sum_congr rfl; intro c _
  apply Finset.sum_congr rfl; intro d _
  by_cases h : a = i ∧ c = j
  · obtain ⟨rfl, rfl⟩ := h
    ring
  · rw [Matrix.single_apply, if_neg h]
    ring
