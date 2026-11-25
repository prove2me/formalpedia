-- Prove2me | solution 1 for Newton.ennreal_sub_div_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:24:15.972171+00:00
-- url     : https://prove2.me/submissions/79f6d492-6517-4af0-a793-cb7911446a22

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_ennreal_div_mul_right
import Theorems.Thm_Newton_ennreal_div_mul_left

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    (r - p) / (p * r) = 1/p - 1/r := by
  have hpr_pos : p * r ≠ 0 := mul_ne_zero hp_pos hr_pos
  have h1 : r / (p * r) = 1 / p := ennreal_div_mul_right hp_pos hp_ne_top hr_pos hr_ne_top
  have h2 : p / (p * r) = 1 / r := ennreal_div_mul_left hp_pos hp_ne_top hr_pos hr_ne_top
  have h_sub : (r - p) / (p * r) = r / (p * r) - p / (p * r) := by
    apply ENNReal.sub_div
    intro _ _
    exact hpr_pos
  rw [h_sub, h1, h2]
end Newton
