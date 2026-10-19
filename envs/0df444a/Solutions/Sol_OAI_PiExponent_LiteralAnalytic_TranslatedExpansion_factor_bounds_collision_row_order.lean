-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.TranslatedExpansion.factor_bounds_collision_row_order
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-18T17:26:50.024092+00:00
-- url     : https://prove2.me/submissions/b462b453-cf5e-4b30-9a16-a7a7e570191d

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_TranslatedExpansionTerms

open scoped BigOperators Topology
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic
open OAI.PiExponent.LiteralAnalytic.TranslatedExpansion

theorem solution
    {nu : ℝ} (d : FixedData nu) {H : ℝ} (hH : 0 < H)
    (r : Row d H) :
    (r.2.1 0 : ℝ) ≤ H / (d.v0 : ℝ) := by
  classical
  have hlt := (Finset.mem_filter.mp r.2.2).2
  have htail : 0 ≤ ∑ i : Fin d.m,
      (MatrixArithmetic.logWeights (finiteDenominators d) i / d.base.theta) *
        (r.2.1 i.succ : ℝ) := by
    apply Finset.sum_nonneg
    intro i hi
    apply mul_nonneg
    · unfold MatrixArithmetic.logWeights
      exact div_nonneg (Nat.cast_nonneg _) d.base.theta_pos.le
    · exact Nat.cast_nonneg _
  have hsplit :
      (d.v0 : ℝ) * (r.2.1 0 : ℝ) +
        (∑ i : Fin d.m,
          (MatrixArithmetic.logWeights (finiteDenominators d) i / d.base.theta) *
            (r.2.1 i.succ : ℝ)) < H := by
    simpa [InterpolationMatrix.rowWeights, Fin.sum_univ_succ] using hlt
  have hbound : (d.v0 : ℝ) * (r.2.1 0 : ℝ) ≤ H := by
    linarith
  rw [le_div_iff₀ d.v0_pos]
  simpa only [mul_comm] using hbound
