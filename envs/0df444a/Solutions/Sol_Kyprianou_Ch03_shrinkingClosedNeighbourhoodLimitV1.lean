-- Prove2me | solution 1 for Kyprianou.Ch03.shrinkingClosedNeighbourhoodLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:45:13.260093+00:00
-- url     : https://prove2.me/submissions/2ad810d6-1414-463b-8838-73873683ce24

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (B : Set ℝ) (hB : IsClosed B) (z : ℕ → ℝ) (v : ℝ)
    (hz : Tendsto z atTop (𝓝 v))
    (hmem : ∀ n : ℕ, z n ∈ Metric.cthickening (1 / ((n : ℝ) + 1)) B) :
    v ∈ B := by
  have hm (r : ℝ) (hr : 0 < r) : v ∈ Metric.cthickening r B := by
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt hr
    apply Metric.isClosed_cthickening.mem_of_tendsto hz
    filter_upwards [eventually_ge_atTop k] with n hn
    exact Metric.cthickening_mono (le_trans (by gcongr <;> exact_mod_cast hn) hk.le) B (hmem n)
  have hc : v ∈ closure B := by
    rw [Metric.closure_eq_iInter_cthickening]
    simpa only [Set.mem_iInter] using hm
  rwa [hB.closure_eq] at hc
