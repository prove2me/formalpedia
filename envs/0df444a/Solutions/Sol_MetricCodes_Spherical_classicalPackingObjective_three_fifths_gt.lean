-- Prove2me | solution 1 for MetricCodes.Spherical.classicalPackingObjective_three_fifths_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/c8b3e07b-fa9e-4cb9-a4e0-6839689291e0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_two_interval
import Theorems.Thm_MetricCodes_Spherical_log_three_lt_1099_thousandths
import Theorems.Thm_MetricCodes_Spherical_log_five_gt_1609_thousandths
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_three_fifths

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    (29 : ℝ) / 50 < classicalPackingObjective ((3 : ℝ) / 5) := by
  rw [classicalPackingObjective_three_fifths]
  have htwo := MetricCodes.Numerics.log_two_interval.1
  have hthree := log_three_lt_1099_thousandths
  have hfive := log_five_gt_1609_thousandths
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : (29 : ℝ) / 50 - 3 <
      ((1 / 2 : ℝ) * Real.log 5 - (9 / 4 : ℝ) * Real.log 3) /
        Real.log 2 := by
    apply (lt_div_iff₀ hlogtwo).mpr
    nlinarith [htwo, hthree, hfive]
  linarith
end MetricCodes.Spherical
