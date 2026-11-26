-- Prove2me | solution 1 for Kyprianou.Ch04.frozenPathLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:55.60058+00:00
-- url     : https://prove2.me/submissions/8944bf03-09fa-4e40-91ca-b29efed1ccc4

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Freezing a path at a deterministic horizon preserves all earlier strict left limits. -/
theorem solution (Y : NNReal → ℝ) (T u : NNReal) (l : ℝ)
    (hu : u ≤ T) (hL : Tendsto Y (𝓝[<] u) (𝓝 l)) :
    Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 l) := by
  apply hL.congr'
  filter_upwards [self_mem_nhdsWithin (a := u) (s := Iio u)] with v hv
  rw [min_eq_left (le_trans (le_of_lt hv) hu)]
