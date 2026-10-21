-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @polylog
-- created : 2026-10-20T16:17:26.712052+00:00
-- url     : https://prove2.me/submissions/c66b9929-f894-404a-a163-a2b830280a83

import Definitions.Def_OAI_NumberTheory_PiExponent_Analysis_AnalyticAggregate_RemainderData
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translationTermCount_log_div_eventually_nonneg
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_translationTermCount_log_div_eventually_lt

open scoped BigOperators Topology
open Filter
open OAI.PiExponent

theorem solution (m : ℕ) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun H : ℝ =>
      Real.log (translationTermCount m v H : ℝ) / H) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.2
  intro ε hε
  have hε' : 0 < ε / 2 := by linarith
  filter_upwards
    [OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_eventually_nonneg
       m hv,
     OAI.PiExponent.DeterminantContradiction.translationTermCount_log_div_eventually_lt
       m hv (ε / 2) hε'] with H hnonneg hlt
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  linarith
