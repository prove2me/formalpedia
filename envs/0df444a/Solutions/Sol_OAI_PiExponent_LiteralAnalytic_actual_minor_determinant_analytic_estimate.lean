-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.actual_minor_determinant_analytic_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:06:54.178825+00:00
-- url     : https://prove2.me/submissions/dde83d77-f036-47f9-81e5-c61b6542dd27
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_row_count_pos
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actual_minor_norm_exp_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) := by
  let B : ℝ :=
    d.analyticError + analyticRemainder d H +
      max (-collisionRate d H)
        (-nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H))
  have hden : 0 < (actualRowCount d H : ℝ) * H :=
    mul_pos (by exact_mod_cast
      OAI.PiExponent.LiteralAnalytic.actual_minor_row_count_pos d hH) hH
  have hnorm : 0 < ‖(actualMinor d H selection).det‖ :=
    norm_pos_iff.mpr hdet
  have hbound :=
    OAI.PiExponent.LiteralAnalytic.actual_minor_norm_exp_bound
      d hnu hH selection
  have hlog : Real.log ‖(actualMinor d H selection).det‖ ≤
      ((actualRowCount d H : ℝ) * H) * B := by
    exact (Real.log_le_iff_le_exp hnorm).2 (by simpa [B] using hbound)
  change Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤ B
  exact (div_le_iff₀' hden).2 hlog