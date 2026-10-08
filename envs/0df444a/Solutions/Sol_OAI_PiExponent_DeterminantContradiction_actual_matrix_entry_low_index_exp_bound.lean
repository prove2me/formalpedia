-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_matrix_entry_low_index_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-07T21:40:11.040291+00:00
-- url     : https://prove2.me/submissions/1c5e968b-2e78-45d6-a917-6bac89e0a5a0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_truncated_log_entry_low_index_exp_bound
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H)
    (rowIdx : Row d H) (colIdx : Column d H) :
    norm (actualMatrix d H rowIdx colIdx) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
        Real.log (actualRowCount d H : Real) / H)) := by
  simpa [actualMatrix] using
    actual_truncated_log_entry_low_index_exp_bound d hnu hH rowIdx colIdx
