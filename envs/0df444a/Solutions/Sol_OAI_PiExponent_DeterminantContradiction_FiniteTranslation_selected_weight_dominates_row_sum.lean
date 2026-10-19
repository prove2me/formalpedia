-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.FiniteTranslation.selected_weight_dominates_row_sum
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T13:00:47.774625+00:00
-- url     : https://prove2.me/submissions/24038440-7626-4ec2-b1d2-cf0e61c4672b

import Definitions.Def_OAI_PiExponent_FiniteActualTranslation
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_FiniteTranslation_row_weight_le_selected_index_weight

open scoped BigOperators
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.DeterminantContradiction.FiniteTranslation

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ}
    (f : Family d H)
    (hf : (∏ r : Row d H, scalar d r (f r)) ≠ 0) :
    MatrixArithmetic.rowWeightedSum d.K d.v0 d.base.theta
        (finiteDenominators d) H ≤
      ∑ r : Row d H, weight d (f r).1 := by
  classical
  unfold MatrixArithmetic.rowWeightedSum
  apply Finset.sum_le_sum
  intro r hr
  exact OAI.PiExponent.DeterminantContradiction.FiniteTranslation.row_weight_le_selected_index_weight
    d f hf r