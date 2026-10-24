-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.matrix_surjective_has_full_row_minor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:24:29.867294+00:00
-- url     : https://prove2.me/submissions/7c84724c-ee22-48a6-872a-b58e142077c2

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_surjective_has_independent_columns
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_independent_columns_implies_det_ne_zero

theorem solution
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    {K : Type*} [Field K] (A : Matrix α β K)
    (h : Function.Surjective A.mulVecLin) :
    ∃ selection : α → β,
      Function.Injective selection ∧ (A.submatrix id selection).det ≠ 0 := by
  obtain ⟨selection, hselection, hcolumns⟩ :=
    OAI.PiExponent.DeterminantContradiction.surjective_has_independent_columns A h
  exact ⟨selection, hselection,
    OAI.PiExponent.DeterminantContradiction.independent_columns_implies_det_ne_zero
      (A.submatrix id selection) hcolumns⟩