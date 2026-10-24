-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.row_scale_det
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T09:31:12.240077+00:00
-- url     : https://prove2.me/submissions/1a97715b-86bd-4c42-b03c-721aec58dc13

import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators

theorem solution
    {α : Type} [Fintype α] [DecidableEq α]
    (M : Matrix α α Complex) (scale : α → Nat) :
    (let A : Matrix α α Complex := fun i j => (scale i : Complex) * M i j; A.det) =
      ((∏ i : α, scale i : Nat) : Complex) * M.det := by
  change Matrix.det (Matrix.of fun i j => (scale i : Complex) * M i j) = _
  have h := Matrix.det_mul_column (fun i => (scale i : Complex)) M
  rw [h]
  norm_cast
