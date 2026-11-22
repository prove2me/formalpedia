-- Prove2me | solution 1 for HardyFLocal.prodOp_apply_kron
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-22T00:42:58.713346+00:00
-- url     : https://prove2.me/submissions/72bc89b4-8909-47a1-a9dd-4f659d229f32

import Mathlib
import Definitions.Def_HardyFLocal_Superoperator
open scoped Kronecker

namespace HardyFLocal
open scoped Matrix Kronecker ComplexOrder

private theorem matrix_unit_expansion {ι : Type} [Fintype ι] [DecidableEq ι]
    (Φ : Op ι) (A : Matrix ι ι ℂ) :
    Φ A = ∑ i, ∑ j, A i j • Φ (Matrix.single i j 1) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single A]
  simp only [map_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]

end HardyFLocal

open HardyFLocal

open Classical in
theorem solution {ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (Φ : Op ι) (Ψ : Op κ)
    (A : Matrix ι ι ℂ) (B : Matrix κ κ ℂ) :
    prodOp Φ Ψ (A ⊗ₖ B) = Φ A ⊗ₖ Ψ B := by
  apply Matrix.ext
  rintro ⟨r,s⟩ ⟨t,u⟩
  change (∑ i, ∑ i', ∑ j, ∑ j', (A i i' * B j j') •
    (Φ (Matrix.single i i' 1) ⊗ₖ Ψ (Matrix.single j j' 1))) (r,s) (t,u) =
      Φ A r t * Ψ B s u
  rw [matrix_unit_expansion Φ A, matrix_unit_expansion Ψ B]
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kronecker_apply,
    Finset.sum_mul]
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
    Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

