-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.cofinal_nonzero_actual_minors
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:30:19.403719+00:00
-- url     : https://prove2.me/submissions/d697303f-5838-45a3-94b2-c897d81cecac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

/-- Cofinally many positive heights admit a nonzero actual interpolation minor.  This is the
direct consequence of cofinal surjectivity of the actual interpolation matrix together with the
existence of a full row minor with nonzero determinant for a surjective matrix. -/
theorem solution {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ 0 < H ∧
      ∃ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 := by
  have hsurj : ∀ L : ℝ, ∃ H : ℝ, L ≤ H ∧
      Function.Surjective (actualMatrix d H).mulVecLin :=
    OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation nu hnu d
  obtain ⟨H, hLH, hsurjH⟩ := hsurj (max L 1)
  have hHpos : 0 < H := lt_of_lt_of_le one_pos (le_trans (le_max_right L 1) hLH)
  obtain ⟨selection, -, hdet⟩ :=
    OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective
      (actualMatrix d H) hsurjH
  refine ⟨H, le_trans (le_max_left L 1) hLH, hHpos, selection, ?_⟩
  simpa [actualMinor, actualMatrix, MatrixArithmetic.selectedMinor] using hdet
