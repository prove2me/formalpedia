-- Prove2me | solution 1 for Kyprianou.Ch04.frozenPathRightContinuousV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T07:13:55.689099+00:00
-- url     : https://prove2.me/submissions/6f61efe6-1db0-4df8-a35a-5fa6537c52e3

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Deterministic freezing preserves right continuity. -/
theorem solution (Y : NNReal → ℝ) (T : NNReal)
    (hR : ∀ u, ContinuousWithinAt Y (Ici u) u) :
    ∀ u, ContinuousWithinAt (fun v => Y (min v T)) (Ici u) u := by
  intro u
  have hm : Tendsto (fun v : NNReal => min v T)
      (𝓝[Ici u] u) (𝓝[Ici (min u T)] (min u T)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_id.min continuous_const).continuousAt.tendsto).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin (a := u) (s := Ici u)] with v hv
    exact min_le_min (show u ≤ v from hv) le_rfl
  exact (hR (min u T)).tendsto.comp hm
