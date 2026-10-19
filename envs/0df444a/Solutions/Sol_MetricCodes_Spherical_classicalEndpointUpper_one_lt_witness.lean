-- Prove2me | solution 1 for MetricCodes.Spherical.classicalEndpointUpper_one_lt_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.916513+00:00
-- url     : https://prove2.me/submissions/f9571c4c-56fd-4186-95ab-09026d6e2184

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Numerics_log_two_interval
import Theorems.Thm_MetricCodes_Spherical_classicalPackingObjective_three_fifths_gt

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution :
    classicalEndpointUpper 1 <
      classicalPackingObjective ((3 : ℝ) / 5) := by
  rw [classicalEndpointUpper_one]
  have htwo := MetricCodes.Numerics.log_two_interval.2
  have hpositive : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hupper : 2 - 1 / Real.log 2 < (29 : ℝ) / 50 := by
    have hinv : (71 : ℝ) / 50 < 1 / Real.log 2 := by
      apply (lt_div_iff₀ hpositive).mpr
      nlinarith [htwo]
    linarith
  exact hupper.trans classicalPackingObjective_three_fifths_gt
end MetricCodes.Spherical
