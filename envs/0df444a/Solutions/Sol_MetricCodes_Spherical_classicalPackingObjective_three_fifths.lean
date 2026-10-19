-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingObjective_three_fifths
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/89af3254-b458-45be-8549-bcb4c9ec4c7b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    classicalPackingObjective ((3 : ℝ) / 5) =
      3 + ((1 / 2 : ℝ) * Real.log 5 -
        (9 / 4 : ℝ) * Real.log 3) / Real.log 2 := by
  have hroot :
      Real.sqrt (1 - ((3 : ℝ) / 5) ^ 2) = (4 : ℝ) / 5 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).2
    norm_num
  have hdegree : MetricCodes.classicalThreshold ((3 : ℝ) / 5) =
      (1 : ℝ) / 8 := by
    unfold MetricCodes.classicalThreshold
    rw [hroot]
    norm_num
  have hthree : Real.logb 2 ((9 : ℝ) / 8) =
      2 * Real.logb 2 3 - 3 := by
    calc
      Real.logb 2 ((9 : ℝ) / 8) =
          Real.logb 2 ((3 : ℝ) ^ 2 / (2 : ℝ) ^ 3) := by norm_num
      _ = Real.logb 2 ((3 : ℝ) ^ 2) -
          Real.logb 2 ((2 : ℝ) ^ 3) := by
            rw [Real.logb_div] <;> norm_num
      _ = 2 * Real.logb 2 3 - 3 := by
            rw [Real.logb_pow, Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
  have height : Real.logb 2 ((1 : ℝ) / 8) = -3 := by
    calc
      Real.logb 2 ((1 : ℝ) / 8) =
          Real.logb 2 (((2 : ℝ) ^ 3)⁻¹) := by norm_num
      _ = -Real.logb 2 ((2 : ℝ) ^ 3) := by
            rw [Real.logb_inv]
      _ = -3 := by
            rw [Real.logb_pow,
              Real.logb_self_eq_one (by norm_num)]
            norm_num
  unfold classicalPackingObjective
  rw [hdegree]
  unfold MetricCodes.sphericalEntropy
  norm_num
  rw [hthree, height]
  unfold Real.logb
  ring
end MetricCodes.Spherical
