-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actual_truncated_log_entry_low_index_exp_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-08T06:14:48.541167+00:00
-- url     : https://prove2.me/submissions/4bd76f57-ad94-4e5c-93f8-0551fd749aa3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OAI_PiExponent_InterpolationMatrix_entry_eq_binomial_product
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_binomial_truncated_log_coefficient_exp_bound
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Algebra.BigOperators.Field

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem solution
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H)
    (rowIdx : Row d H) (colIdx : Column d H) :
    norm ((InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)) rowIdx colIdx) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
        Real.log (actualRowCount d H : Real) / H)) := by
  classical
  have hrow := (Finset.mem_filter.mp rowIdx.2.2).2
  change ∑ i : Fin (d.m + 1),
    InterpolationMatrix.rowWeights d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) i * (rowIdx.2.1 i : ℝ) < H at hrow
  rw [Fin.sum_univ_succ] at hrow
  simp only [InterpolationMatrix.rowWeights, Fin.cases_zero, Fin.cases_succ,
    div_mul_eq_mul_div, ← Finset.sum_div] at hrow
  have hcol := (Finset.mem_filter.mp colIdx.2).2
  change ∑ i : Fin (d.m + 1),
    InterpolationMatrix.columnWeights d.w0
      (MatrixArithmetic.logWeights (finiteDenominators d)) i * (colIdx.1 i : ℝ) ≤ H at hcol
  rw [Fin.sum_univ_succ] at hcol
  simp only [InterpolationMatrix.columnWeights, Fin.cases_zero, Fin.cases_succ] at hcol
  have hb := binomial_truncated_log_coefficient_exp_bound d hnu hH
    rowIdx.1.val (rowIdx.2.1 0) (colIdx.1 0)
    (fun i => rowIdx.2.1 i.succ) (fun i => colIdx.1 i.succ)
    rowIdx.1.isLt hrow hcol
  change ‖InterpolationMatrix.entry _ _ _ _ _ _ _‖ ≤ _
  rw [InterpolationMatrix.entry_eq_binomial_product]
  have henv : 0 < translationEnvelope d.m d.v0 H := by
    unfold translationEnvelope
    exact mul_pos (pow_pos (by linarith) _)
      (by have := div_pos hH d.v0_pos; linarith)
  have hexponent : H * (d.analyticError + analyticRemainder d H +
      -nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H) -
      Real.log (actualRowCount d H : ℝ) / H) =
      H * (d.analyticError - nu * ((d.base.A : ℝ) * (1 - d.base.eta) - actualMean d H)) +
        (Real.log 2 / 4 - Real.log (1 - Real.exp (-Real.log 2 / 2))) +
        Real.log (translationEnvelope d.m d.v0 H) := by
    unfold analyticRemainder
    field_simp [hH.ne']
    <;> ring
  rw [hexponent, Real.exp_add, Real.exp_add, Real.exp_log henv]
  exact hb
