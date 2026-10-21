-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.collision_log_row_count_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:14:26.68003+00:00
-- url     : https://prove2.me/submissions/1e4e9c17-c773-4282-a84e-9f142761ea71

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_log_nat_div_tendsto_zero_of_polynomial_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_collisionRowCount_eventually_polynomial_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution
    {nu : ℝ} (d : FixedData nu) :
    Tendsto
      (fun H : ℝ => Real.log (actualRowCount d H : ℝ) / H)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hpos, hbound⟩ :=
    OAI.PiExponent.DeterminantContradiction.collisionRowCount_eventually_polynomial_bound d
  exact OAI.PiExponent.DeterminantContradiction.log_nat_div_tendsto_zero_of_polynomial_bound
    (fun H => actualRowCount d H) (d.m + 1) C hC hpos hbound