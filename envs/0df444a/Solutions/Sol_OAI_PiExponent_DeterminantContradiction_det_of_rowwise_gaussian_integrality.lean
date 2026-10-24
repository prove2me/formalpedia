-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.det_of_rowwise_gaussian_integrality
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:24:31.197175+00:00
-- url     : https://prove2.me/submissions/bb2de2d9-408e-44da-99ac-c264a3aefbb4

import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_gaussian_int_det
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_row_scale_det
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_prod_scale_log

open scoped BigOperators

theorem solution
    {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α Complex) (scale : α → Nat)
    (hscale_pos : ∀ i, 0 < scale i)
    (hscale_int : ∀ i j, ∃ a b : Int,
      (scale i : Complex) * M i j = (a : Complex) + Complex.I * (b : Complex))
    (B : Real)
    (hbudget : (∑ i : α, Real.log (scale i : Real)) ≤ B) :
    ∃ D : Nat, 0 < D ∧
      ∃ a b : Int,
        (D : Complex) * M.det = (a : Complex) + Complex.I * (b : Complex) ∧
          Real.log (D : Real) ≤ B := by
  let D : Nat := ∏ i : α, scale i
  let A : Matrix α α Complex := fun i j => (scale i : Complex) * M i j
  have hD : 0 < D ∧ Real.log (D : Real) ≤ B := by
    simpa [D] using
      OAI.PiExponent.DeterminantContradiction.prod_scale_log
        scale hscale_pos B hbudget
  have hscaled : ∃ a b : Int,
      Matrix.det A = (a : Complex) + Complex.I * (b : Complex) := by
    apply OAI.PiExponent.DeterminantContradiction.gaussian_int_det
    intro i j
    exact hscale_int i j
  rcases hscaled with ⟨a, b, hab⟩
  have hrow : Matrix.det A = (D : Complex) * M.det := by
    simpa [A, D] using
      OAI.PiExponent.DeterminantContradiction.row_scale_det M scale
  refine ⟨D, hD.1, a, b, ?_, hD.2⟩
  rw [← hrow]
  exact hab