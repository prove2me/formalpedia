-- Prove2me | solution 1 for HarlowTASI.trace_mul_blockScalarOp
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:00:42.731824+00:00
-- url     : https://prove2.me/submissions/5732d8cf-7ace-48bf-9311-bb567d3c5163

import Mathlib
import Definitions.Def_HarlowTASI_OperatorAlgebras

open Matrix
open scoped Kronecker ComplexOrder

open HarlowTASI in
theorem solution {C : Type} [Fintype C] [DecidableEq C]
    {N : ℕ} {dr drb : Fin N → ℕ} (U : Matrix (BlockIndex N dr drb) C ℂ)
    (ρ : Matrix C C ℂ) (c : Fin N → ℂ) :
    (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U)).trace =
      ∑ a, c a * (diagBlock U ρ a).trace := by
  have h1 : (ρ * (Uᴴ * blockScalarOp (dr := dr) (drb := drb) c * U)).trace =
      ((U * ρ * Uᴴ) * blockScalarOp (dr := dr) (drb := drb) c).trace := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, trace_mul_comm, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc]
  rw [h1]
  set M := U * ρ * Uᴴ
  have h2 : ∀ ik : BlockIndex N dr drb, (M * blockScalarOp (dr := dr) (drb := drb) c) ik ik =
      M ik ik * c ik.1 := by
    rintro ⟨a, i⟩
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨a, i⟩]
    · simp [blockScalarOp, blockDiagonal'_apply_eq]
    · rintro ⟨b, j⟩ _ hne
      by_cases hab : b = a
      · subst hab
        have : j ≠ i := fun h => hne (by rw [h])
        simp [blockScalarOp, blockDiagonal'_apply_eq, Matrix.one_apply_ne this]
      · simp [blockScalarOp, blockDiagonal'_apply_ne _ _ _ hab]
    · simp
  simp only [Matrix.trace, Matrix.diag, h2, Fintype.sum_sigma, diagBlock, Matrix.submatrix_apply,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
  rw [mul_comm]
