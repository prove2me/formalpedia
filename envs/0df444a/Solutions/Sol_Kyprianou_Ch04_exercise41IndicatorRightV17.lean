-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IndicatorRightV17
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:18:36.295681+00:00
-- url     : https://prove2.me/submissions/908d989f-abd5-441a-b4a4-4456a6073d83

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (s : NNReal)
    (hR : ContinuousWithinAt x (Ici s) s)
    (hdep : x s = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < e → 0 < x (s+u)) :
    ContinuousWithinAt (fun u => if x u < 0 then (-1 : ℝ) else 0) (Ici s) s := by
  by_cases hn : x s < 0
  · change Tendsto (fun u => if x u < 0 then (-1 : ℝ) else 0) (nhdsWithin s (Ici s)) (nhds (if x s < 0 then (-1 : ℝ) else 0))
    rw [if_pos hn]
    apply tendsto_const_nhds.congr'
    filter_upwards [hR.eventually (eventually_lt_nhds hn)] with u hu
    simp [hu]
  have hp : 0 ≤ x s := le_of_not_gt hn
  change Tendsto (fun u => if x u < 0 then (-1 : ℝ) else 0) (nhdsWithin s (Ici s)) (nhds (if x s < 0 then (-1 : ℝ) else 0))
  rw [if_neg hn]
  apply tendsto_const_nhds.congr'
  by_cases hz : x s = 0
  · obtain ⟨e,he,h⟩ := hdep hz
    have hmem : Iio (s+e) ∈ nhdsWithin s (Ici s) :=
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by simpa using add_lt_add_right he s))
    filter_upwards [self_mem_nhdsWithin (s := Ici s) (a := s),hmem] with v hv hve
    by_cases hv' : v = s
    · simp [hv',hz]
    have hvs : s < v := lt_of_le_of_ne hv (Ne.symm hv')
    have hu : 0 < v-s := tsub_pos_of_lt hvs
    have hlt : v-s < e := (tsub_lt_iff_left hv).mpr hve
    have H := h (v-s) hu hlt
    rw [add_tsub_cancel_of_le hv] at H
    simp [not_lt_of_ge H.le]
  · have hpos := lt_of_le_of_ne hp (Ne.symm hz)
    filter_upwards [hR.eventually (eventually_gt_nhds hpos)] with v hv
    simp [not_lt_of_ge hv.le]
