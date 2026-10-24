-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.independent_columns_implies_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:27:43.137334+00:00
-- url     : https://prove2.me/submissions/326c2acd-7b96-4549-8932-f9c0ff460f7f

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Nonsingular

theorem solution
    {α : Type*} [Fintype α] [DecidableEq α]
    {K : Type*} [Field K] (M : Matrix α α K)
    (h : LinearIndependent K (fun j : α => fun i : α => M i j)) :
    M.det ≠ 0 := by
  have hcol : LinearIndependent K M.col := h
  exact (Matrix.nonsingular_iff_det_ne_zero (A := M)).mp
    (Matrix.Nonsingular.of_linearIndependent_col hcol)