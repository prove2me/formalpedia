-- Prove2me | solution 1 for OAI.PiExponent.LiteralAnalytic.log_actualRowCount_div_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-13T15:32:25.377232+00:00
-- url     : https://prove2.me/submissions/9b50d264-e752-44e4-80f3-a0450237c8a8

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_LiteralAnalytic_actualRowCount_eventually_polynomial_bound
import Theorems.Thm_OAI_PiExponent_log_nat_polynomial_growth_div_tendsto

open scoped BigOperators Topology
open Filter
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction OAI.PiExponent.LiteralAnalytic

theorem solution {nu : ℝ} (d : FixedData nu) :
    Tendsto (fun H : ℝ => Real.log (actualRowCount d H : ℝ) / H) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    OAI.PiExponent.LiteralAnalytic.actualRowCount_eventually_polynomial_bound d
  apply OAI.PiExponent.log_nat_polynomial_growth_div_tendsto
      (fun H => actualRowCount d H) C (d.m + 1) hC
  filter_upwards [hbound] with H hH
  exact hH
