-- Prove2me | solution 1 for LevyStochCalc.Analysis.tendsto_leftPt
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T02:57:00.605745+00:00
-- url     : https://prove2.me/submissions/9e223d8d-60e4-4b4d-a322-4b65b8c16b99

import Definitions.Def_LevyStochCalc_Analysis_DyadicGrid_F000

open Filter
open scoped Topology
open LevyStochCalc.Analysis

theorem solution {t : ℝ} (ht : 0 < t) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ => leftPt t n s) atTop (𝓝 s) := by
  have h0 : Tendsto (fun n : ℕ => t / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hlow : Tendsto (fun n : ℕ => s - t / (2 : ℝ) ^ n) atTop (𝓝 (s - 0)) :=
    tendsto_const_nhds.sub h0
  rw [sub_zero] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
    (fun n => ?_) (fun n => (leftPt_lt ht n hs).le)
  linarith [le_leftPt_add ht n hs]
