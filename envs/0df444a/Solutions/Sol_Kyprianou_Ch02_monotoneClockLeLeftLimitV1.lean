-- Prove2me | solution 1 for Kyprianou.Ch02.monotoneClockLeLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:48:22.464651+00:00
-- url     : https://prove2.me/submissions/36f8ed69-d68b-402a-a143-20fb881edf03

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Complex Filter Set Topology
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (g : ℝ≥0 → ℝ≥0) (hm : Monotone g) (t u : ℝ≥0)
    (hu : Tendsto g (nhdsWithin t (Set.Iio t)) (nhds u))
    (r : ℝ≥0) (hr : r < t) : g r ≤ u := by
  haveI : NeBot (nhdsWithin t (Set.Iio t)) :=
    nhdsLT_neBot_of_exists_lt ⟨r, hr⟩
  have hev : ∀ᶠ v in nhdsWithin t (Set.Iio t), r < v :=
    (eventually_gt_nhds hr).filter_mono nhdsWithin_le_nhds
  exact ge_of_tendsto hu (hev.mono fun v hv => hm hv.le)
