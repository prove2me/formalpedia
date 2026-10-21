-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.actualRowCount_eventually_polynomial_upper_core
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:32:27.400516+00:00
-- url     : https://prove2.me/submissions/142dc980-399f-4fd0-b00f-6ac68f507d05

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_weightedStrictRowCount_eventually_polynomial_bound

open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped Topology

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    ∃ C : ℝ,
      (∀ᶠ H : ℝ in atTop,
        (actualRowCount d H : ℝ) ≤ C * (H + 1) ^ (d.m + 1)) := by
  have hw : ∀ i : Fin (d.m + 1),
      0 < OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d)) i := by
    intro i
    induction i using Fin.cases with
    | zero =>
        simpa [OAI.PiExponent.InterpolationMatrix.rowWeights] using d.v0_pos
    | succ i =>
        have hq : 2 ≤ d.q i.val := (d.approximations i).1
        have hq' : (1 : ℝ) < (d.q i.val : ℝ) := by exact_mod_cast (by omega : 1 < d.q i.val)
        have hlog : 0 < Real.log (d.q i.val : ℝ) := Real.log_pos hq'
        have hceil : 0 < (Nat.ceil (Real.log (d.q i.val : ℝ)) : ℝ) := by
          exact_mod_cast (Nat.ceil_pos.mpr hlog)
        have htheta : 0 < (d.base.theta : ℝ) := d.base.theta_pos
        simpa [OAI.PiExponent.InterpolationMatrix.rowWeights,
          MatrixArithmetic.logWeights, finiteDenominators] using div_pos hceil htheta
  obtain ⟨C, hC⟩ :=
    OAI.PiExponent.DeterminantContradiction.weightedStrictRowCount_eventually_polynomial_bound
      d.K
      (OAI.PiExponent.InterpolationMatrix.rowWeights d.v0 d.base.theta
        (MatrixArithmetic.logWeights (finiteDenominators d))) hw
  refine ⟨C, ?_⟩
  simpa [actualRowCount, Row, OAI.PiExponent.InterpolationMatrix.Row] using hC