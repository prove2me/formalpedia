-- Prove2me | solution 1 for Newton.decomposition_exponents_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:31.325744+00:00
-- url     : https://prove2.me/submissions/1be23ff8-ba5b-4cbe-8b64-f9e7334acb0a

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
theorem _root_.solution
    {p q r : ℝ≥0∞}
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hr_ne_top : r ≠ ⊤) :
    0 < p/r ∧ 0 < q/r ∧ 0 ≤ 1 - p/r ∧ 0 ≤ 1 - q/r := by
  -- Positivity of p, q, r
  have hp_pos : p ≠ 0 := (one_pos.trans_le hp).ne'
  have hq_pos : q ≠ 0 := (one_pos.trans_le hq).ne'
  -- 0 < p/r and 0 < q/r since numerators are positive and denominator is finite
  have hp_div_pos : 0 < p / r := ENNReal.div_pos hp_pos hr_ne_top
  have hq_div_pos : 0 < q / r := ENNReal.div_pos hq_pos hr_ne_top
  -- 1 - p/r and 1 - q/r are automatically ≥ 0 in ℝ≥0∞
  have h_one_sub_p : (0 : ℝ≥0∞) ≤ 1 - p / r := zero_le
  have h_one_sub_q : (0 : ℝ≥0∞) ≤ 1 - q / r := zero_le
  exact ⟨hp_div_pos, hq_div_pos, h_one_sub_p, h_one_sub_q⟩
end Newton
