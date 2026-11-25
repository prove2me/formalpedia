-- Prove2me | solution 1 for Newton.young_exponent_r_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T01:21:20.260863+00:00
-- url     : https://prove2.me/submissions/62917022-2d42-42d7-844a-c2da0722fbe3

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
    {p q r : ℝ≥0∞} (hp : 1 ≤ p) (hq : 1 ≤ q) (hpqr : 1 / p + 1 / q = 1 + 1 / r) :
    1 ≤ r := by
  have hp_inv : 1/p ≤ 1 := by rw [one_div, ENNReal.inv_le_one]; exact hp
  have hq_inv : 1/q ≤ 1 := by rw [one_div, ENNReal.inv_le_one]; exact hq
  have h_sum_le : 1/p + 1/q ≤ 2 := by
    calc 1/p + 1/q ≤ 1 + 1 := add_le_add hp_inv hq_inv
      _ = 2 := by norm_num
  rw [hpqr] at h_sum_le
  -- 1 + 1/r ≤ 2 → 1/r ≤ 1 → r ≥ 1
  have h_inv_r : 1/r ≤ 1 := by
    have h2 : (2 : ℝ≥0∞) = 1 + 1 := by norm_num
    rw [h2] at h_sum_le
    exact (ENNReal.add_le_add_iff_left (by simp : (1 : ℝ≥0∞) ≠ ⊤)).mp h_sum_le
  rw [one_div, ENNReal.inv_le_one] at h_inv_r
  exact h_inv_r
end Newton
