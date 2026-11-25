-- Prove2me | solution 1 for Newton.ennreal_div_mul_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:27.593247+00:00
-- url     : https://prove2.me/submissions/2d065edf-9fb2-4e64-bd83-c9b0fb71210f

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary
import Theorems.Thm_Newton_ennreal_div_mul_right

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    p / (p * r) = 1 / r := by
  rw [mul_comm p r]
  exact ennreal_div_mul_right hr_pos hr_ne_top hp_pos hp_ne_top
end Newton
