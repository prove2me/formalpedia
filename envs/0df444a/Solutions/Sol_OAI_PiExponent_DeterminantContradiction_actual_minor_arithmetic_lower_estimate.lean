-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_minor_arithmetic_lower_estimate
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T22:16:33.888215+00:00
-- url     : https://prove2.me/submissions/f63a3b56-5965-4825-a913-ef304bc138f3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_selectedMinor_arithmetic_lower_bound_v2

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) (H : ℝ) (hH : 0 < H)
    (selection : Row d H → Column d H)
    (hdet : (actualMinor d H selection).det ≠ 0) :
    -(1 - actualMean d H) - d.arithmeticError ≤
      Real.log ‖(actualMinor d H selection).det‖ /
        ((actualRowCount d H : ℝ) * H) := by
  have hlogWeights (i : Fin d.m) :
      MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) := by
    simpa [MatrixArithmetic.logWeights, finiteDenominators] using (d.x_log i.val).symm
  have hh := MatrixArithmetic.selectedMinor_arithmetic_lower_bound_v2
    (finiteNumerators d) (finiteDenominators d)
    (fun i => (d.approximations i.val).1)
    (Nat.zero_lt_of_lt d.K_pos) d.w0_pos d.v0_pos d.base.theta_pos d.F0_pos.le hH
    d.wstar_pos (fun i => by rw [hlogWeights]; exact d.wstar_lower i)
    selection hdet
  simpa only [actualMinor, actualMean, actualRowCount,
    AdmissibleParameters.arithmeticError, hlogWeights] using hh