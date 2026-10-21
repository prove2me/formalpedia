-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.low_index_count_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:15:11.526926+00:00
-- url     : https://prove2.me/submissions/2e61e4ba-e430-48ad-b9f5-821f4a59178c

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weighted_simplex_scaled_asymptotic

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

 theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto
      (fun H : ℝ => (lowIndexCount d H : ℝ) / H ^ d.m)
      atTop
      (𝓝 (((d.base.A : ℝ) ^ d.m) /
        ((Nat.factorial d.m : ℝ) *
          ∏ i : Fin d.m, d.x (i.val + 1)))) := by
  have hA : 0 < (d.base.A : ℝ) := d.base.theta_pos.trans d.base.theta_lt_A
  have hw : ∀ i : Fin d.m, 0 < MatrixArithmetic.logWeights (finiteDenominators d) i := by
    intro i
    have hx := d.x_one_le (i.val + 1)
    have heq : MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) := by
      simp [MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
    rw [heq]
    exact lt_of_lt_of_le (by norm_num) hx
  have hwx : ∀ i : Fin d.m,
      MatrixArithmetic.logWeights (finiteDenominators d) i = d.x (i.val + 1) := by
    intro i
    simp [MatrixArithmetic.logWeights, finiteDenominators, d.x_log]
  simpa [lowIndexCount] using
    (weighted_simplex_scaled_asymptotic d.m
      (MatrixArithmetic.logWeights (finiteDenominators d)) d.x
      (d.base.A : ℝ) hw hA hwx)