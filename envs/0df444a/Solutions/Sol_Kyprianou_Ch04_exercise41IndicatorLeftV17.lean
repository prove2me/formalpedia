-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41IndicatorLeftV17
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T13:16:34.310596+00:00
-- url     : https://prove2.me/submissions/a5a4adc8-9bc1-4553-ad3c-c887dd237ecb

import Mathlib
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    (x : NNReal → ℝ) (s : NNReal) (hs : 0 < s) (l : ℝ)
    (hL : Tendsto x (nhdsWithin s (Iio s)) (nhds l))
    (harr : l = 0 → ∃ e : NNReal, 0 < e ∧
      ∀ u : NNReal, 0 < u → u < min e s → x (s-u) < 0) :
    Tendsto (fun u => if x u < 0 then (-1 : ℝ) else 0)
      (nhdsWithin s (Iio s)) (nhds (if 0 < l then 0 else -1)) := by
  by_cases hp : 0 < l
  · rw [if_pos hp]
    apply tendsto_const_nhds.congr'
    filter_upwards [hL.eventually (eventually_gt_nhds hp)] with v hv
    simp [not_lt_of_ge hv.le]
  rw [if_neg hp]
  apply tendsto_const_nhds.congr'
  by_cases hz : l = 0
  · obtain ⟨e,he,h⟩ := harr hz
    let d := min e s
    have hd : 0 < d := lt_min he hs
    have hmem : Ioi (s-d) ∈ nhdsWithin s (Iio s) :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (tsub_lt_self hs hd))
    filter_upwards [self_mem_nhdsWithin (s := Iio s) (a := s),hmem] with v hv hve
    have hv' : v < s := hv
    have hdv : s-d < v := hve
    have hlt : s-v < d := (tsub_lt_iff_left hv'.le).mpr
      (by simpa only [add_comm] using (tsub_lt_iff_left (min_le_right e s)).mp hdv)
    have H := h (s-v) (tsub_pos_of_lt hv') hlt
    rw [tsub_tsub_cancel_of_le hv'.le] at H
    simp [H]
  · have hn : l < 0 := lt_of_le_of_ne (le_of_not_gt hp) hz
    filter_upwards [hL.eventually (eventually_lt_nhds hn)] with v hv
    simp [hv]
