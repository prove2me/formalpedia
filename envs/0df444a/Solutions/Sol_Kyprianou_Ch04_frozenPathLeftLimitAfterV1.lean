-- Prove2me | solution 1 for Kyprianou.Ch04.frozenPathLeftLimitAfterV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:55.618464+00:00
-- url     : https://prove2.me/submissions/44cef4ee-4793-4c58-8d66-ae6022d236d5

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- After the freezing time the frozen path has a constant strict left limit. -/
theorem solution (Y : NNReal → ℝ) (T u : NNReal) (hu : T < u) :
    Tendsto (fun v => Y (min v T)) (𝓝[<] u) (𝓝 (Y T)) := by
  apply tendsto_const_nhds.congr'
  have he : ∀ᶠ v in 𝓝[<] u, T < v := nhdsWithin_le_nhds (Ioi_mem_nhds hu)
  filter_upwards [he] with v hv
  rw [min_eq_right (le_of_lt hv)]
