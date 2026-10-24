-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.surjective_actualMatrix_has_nonzero_minor
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T16:56:58.576287+00:00
-- url     : https://prove2.me/submissions/6982095e-fff9-4631-9341-4ffb6598513e

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_pos_of_height_pos
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_exists_nonzero_selected_minor_of_surjective_actualMatrix
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.FormalInterpolation
open Filter Topology
open scoped BigOperators

theorem solution
    (nu : Real) (d : FixedData nu) (H : Real) (hH : 0 < H)
    (hsurj : Function.Surjective (actualMatrix d H).mulVecLin) :
    0 < actualRowCount d H ∧
      ∃ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 := by
  have hrows :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_pos_of_height_pos
      nu d H hH
  have hselected :=
    OAI.PiExponent.DeterminantContradiction.exists_nonzero_selected_minor_of_surjective_actualMatrix
      (actualMatrix d H) hsurj
  obtain ⟨selection, hinjective, hdet⟩ := hselected
  refine ⟨hrows, selection, ?_⟩
  simpa [actualMinor, MatrixArithmetic.selectedMinor, actualMatrix] using hdet
