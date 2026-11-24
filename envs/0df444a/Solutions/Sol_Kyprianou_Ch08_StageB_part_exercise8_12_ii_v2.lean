-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_12_ii_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T14:44:26.695834+00:00
-- url     : https://prove2.me/submissions/620a6009-10a6-4131-90ea-82bf39d22ec0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_12_i_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m812_overshoot_scaled_integral
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m812_overshoot_integral_difference
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal

theorem solution : exercise8_12_ii := by
  intro Ω mΩ P hP D α x y ha hb hx hx1 hy hψ
  rw [part_exercise8_12_i_v2 Ω P D α x y ha hb hx hx1 hy hψ]
  unfold stableOvershootCDF
  let r := α-1
  have hr : 0 < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hs := p2m812_overshoot_scaled_integral r x y hr hr1 hx hy
  have hd := p2m812_overshoot_integral_difference r x y hr hr1 hx hy
  change Real.sin (Real.pi*r)/Real.pi * (∫ t in (0 : ℝ)..y/x, t^(-r)/(1+t)) -
    x^r * (Real.sin (Real.pi*r)/Real.pi * ∫ t in (0 : ℝ)..y, t^(-r)/(1+t)) = _
  rw [hs]
  simp only [add_comm (1 : ℝ)] at *
  dsimp [r] at *
  linear_combination (Real.sin (Real.pi*(α-1))/Real.pi * x^(α-1)) * hd
