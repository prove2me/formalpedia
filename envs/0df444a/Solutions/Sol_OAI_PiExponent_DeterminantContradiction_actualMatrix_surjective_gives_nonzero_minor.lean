-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualMatrix_surjective_gives_nonzero_minor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:20:26.653444+00:00
-- url     : https://prove2.me/submissions/ab688848-e651-4a21-9c24-673875de22d0

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_matrix_surjective_has_full_row_minor

open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    {nu : Real} (d : FixedData nu) (H : Real)
    (h : Function.Surjective (actualMatrix d H).mulVecLin) :
    ∃ selection : Row d H → Column d H,
      Function.Injective selection ∧ (actualMinor d H selection).det ≠ 0 := by
  simpa [actualMinor, MatrixArithmetic.selectedMinor, actualMatrix] using
    (OAI.PiExponent.DeterminantContradiction.matrix_surjective_has_full_row_minor
      (actualMatrix d H) h)
