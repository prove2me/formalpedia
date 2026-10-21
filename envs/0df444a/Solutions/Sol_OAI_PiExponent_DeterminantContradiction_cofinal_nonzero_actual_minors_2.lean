-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.cofinal_nonzero_actual_minors
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T19:32:47.747526+00:00
-- url     : https://prove2.me/submissions/69b34f3d-8286-4ec0-a881-f98b1cd85485
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_AdmissibleMatrixInterpolation_globalInterpolation
import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_exists_full_row_minor_of_surjective

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 2 < nu) (L : ℝ) :
    ∃ H : ℝ, L ≤ H ∧ 0 < H ∧
      ∃ selection : Row d H → Column d H,
        (actualMinor d H selection).det ≠ 0 := by
  classical
  obtain ⟨H, hHge, hsurj⟩ :=
    OAI.PiExponent.AdmissibleMatrixInterpolation.globalInterpolation nu hnu d (max L 1)
  have hHpos : 0 < H := lt_of_lt_of_le one_pos (le_trans (le_max_right L 1) hHge)
  obtain ⟨selection, _hinj, hdet⟩ :=
    OAI.PiExponent.InterpolationMatrix.exists_full_row_minor_of_surjective
      (actualMatrix d H) hsurj
  exact ⟨H, le_trans (le_max_left L 1) hHge, hHpos, selection, hdet⟩
