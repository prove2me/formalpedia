-- Prove2me | solution 1 for MetricCodes.Spherical.sphericalEntropy_lower_logb_add_fraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/a2f3d869-8284-42a7-8f42-9e3800dddc16

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_sphericalEntropy_eq_logb_add_mul_logb

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {a : ℝ} (ha : 0 < a) :
    Real.logb 2 (1 + a) +
        (a / (1 + a)) / Real.log 2 ≤ MetricCodes.sphericalEntropy a := by
  rw [sphericalEntropy_eq_logb_add_mul_logb ha]
  have hlog := Real.one_sub_inv_le_log_of_pos
    (show 0 < (1 + a) / a by positivity)
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Real.logb
  have hlower :
      a / (1 + a) ≤ a * Real.log ((1 + a) / a) := by
    have haux : a * (1 - ((1 + a) / a)⁻¹) =
        a / (1 + a) := by
      field_simp
      ring
    rw [← haux]
    exact mul_le_mul_of_nonneg_left hlog ha.le
  have hfraction : a / (1 + a) / Real.log 2 ≤
      a * (Real.log ((1 + a) / a) / Real.log 2) := by
    rw [← mul_div_assoc]
    exact (div_le_div_iff_of_pos_right hlogtwo).mpr hlower
  linarith
end MetricCodes.Spherical
