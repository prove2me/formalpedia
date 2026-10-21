-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.log_actualRowCount_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T23:10:19.820713+00:00
-- url     : https://prove2.me/submissions/f1634206-60a0-4b28-a2ef-51f5eadb6bb3

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actualRowCount_polynomial_bound

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => Real.log (actualRowCount d H : ℝ) / H) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    OAI.PiExponent.DeterminantContradiction.actualRowCount_polynomial_bound d
  exact OAI.PiExponent.log_nat_function_div_tendsto_zero_of_eventual_polynomial_bound
    (actualRowCount d) C (d.m + 1) hC hbound
