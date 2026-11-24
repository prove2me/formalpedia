-- Prove2me | solution 1 for Kyprianou.Ch02.positiveNegativeSumLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:54:10.352687+00:00
-- url     : https://prove2.me/submissions/6ab9443c-b82b-421e-9cd2-342d2c026299

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (d : ℕ → ℕ → ℝ) (v z : ℝ)
    (hv : Tendsto (fun n => ∑ k : Fin (n+1), |d n k|) atTop (nhds v))
    (hz : ∀ n, ∑ k : Fin (n+1), d n k = z) :
    Tendsto (fun n => (∑ k : Fin (n+1), max (d n k) 0,
      ∑ k : Fin (n+1), max (-d n k) 0)) atTop
      (nhds ((v+z)/2, (v-z)/2)) := by
  have hpos (z : ℝ) : max z 0 = (|z|+z)/2 := by
    rcases le_total 0 z with h|h <;> simp [abs_of_nonneg, abs_of_nonpos, max_eq_left,
      max_eq_right, h] <;> linarith
  have hneg (z : ℝ) : max (-z) 0 = (|z|-z)/2 := by
    rw [hpos, abs_neg]
    ring
  have hp : Tendsto (fun n => ∑ k : Fin (n+1), max (d n k) 0)
      atTop (nhds ((v+z)/2)) := by
    simp_rw [hpos, ← Finset.sum_div, Finset.sum_add_distrib, hz]
    exact (hv.add tendsto_const_nhds).div_const 2
  have hn : Tendsto (fun n => ∑ k : Fin (n+1), max (-d n k) 0)
      atTop (nhds ((v-z)/2)) := by
    simp_rw [hneg, ← Finset.sum_div, Finset.sum_sub_distrib, hz]
    exact (hv.sub tendsto_const_nhds).div_const 2
  exact hp.prodMk_nhds hn

