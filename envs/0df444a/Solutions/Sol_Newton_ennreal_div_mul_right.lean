-- Prove2me | solution 1 for Newton.ennreal_div_mul_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T00:53:59.509482+00:00
-- url     : https://prove2.me/submissions/4da9b31b-72b9-4517-816b-555111c1e112

import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Topology.MetricSpace.Holder
import Definitions.Def_Newton_MeasureTheory_Integral_Tonelli
import Definitions.Def_Newton_Analysis_Convolution_Auxiliary

set_option autoImplicit false
open MeasureTheory Complex NNReal
open scoped ENNReal Topology ContDiff ComplexConjugate
open Newton
variable {n : ℕ}
namespace Newton
theorem _root_.solution {p r : ℝ≥0∞}
    (hp_pos : p ≠ 0) (hp_ne_top : p ≠ ⊤) (hr_pos : r ≠ 0) (hr_ne_top : r ≠ ⊤) :
    r / (p * r) = 1 / p := by
  rw [one_div, ENNReal.div_eq_inv_mul]
  rw [ENNReal.mul_inv (Or.inl hp_pos) (Or.inl hp_ne_top)]
  rw [mul_assoc, ENNReal.inv_mul_cancel hr_pos hr_ne_top, mul_one]
end Newton
