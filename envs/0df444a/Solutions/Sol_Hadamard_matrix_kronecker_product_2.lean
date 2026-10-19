-- Prove2me | solution 2 for Hadamard_matrix_kronecker_product
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T20:09:48.085691+00:00
-- url     : https://prove2.me/submissions/75d92741-ab5b-4a23-b8e1-0344a7f189cb

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Fin.Basic

open Matrix
open scoped Kronecker

set_option autoImplicit false

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin n) (Fin n) ℝ)
    (hApm : ∀ i j, A i j = 1 ∨ A i j = -1)
    (hAorth : A * Aᵀ = ((m : ℕ) : ℝ) • (1 : Matrix (Fin m) (Fin m) ℝ))
    (hBpm : ∀ i j, B i j = 1 ∨ B i j = -1)
    (hBorth : B * Bᵀ = ((n : ℕ) : ℝ) • (1 : Matrix (Fin n) (Fin n) ℝ)) :
    ∃ M : Matrix (Fin (m * n)) (Fin (m * n)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((m * n : ℕ) : ℝ) • (1 : Matrix (Fin (m * n)) (Fin (m * n)) ℝ) := by
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  let K := A ⊗ₖ B
  have hK : K * Kᵀ = ((m * n : ℕ) : ℝ) •
      (1 : Matrix (Fin m × Fin n) (Fin m × Fin n) ℝ) := by
    change (A ⊗ₖ B) * (A ⊗ₖ B)ᵀ = _
    rw [← kroneckerMap_transpose, ← mul_kronecker_mul, hAorth, hBorth,
      smul_kronecker, kronecker_smul, one_kronecker_one, smul_smul, Nat.cast_mul]
  refine ⟨reindexLinearEquiv ℝ ℝ e e K, ?_, ?_⟩
  · intro i j
    change A (e.symm i).1 (e.symm j).1 * B (e.symm i).2 (e.symm j).2 = 1 ∨
      A (e.symm i).1 (e.symm j).1 * B (e.symm i).2 (e.symm j).2 = -1
    rcases hApm (e.symm i).1 (e.symm j).1 with ha | ha <;>
      rcases hBpm (e.symm i).2 (e.symm j).2 with hb | hb <;> simp [ha, hb]
  · change reindexLinearEquiv ℝ ℝ e e K * reindexLinearEquiv ℝ ℝ e e Kᵀ = _
    rw [reindexLinearEquiv_mul, hK, map_smul, reindexLinearEquiv_one]

#print axioms solution
