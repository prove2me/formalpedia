-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sliceCost_sub_zero_le_neg_linear
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/87b65bfa-9cc5-4ab1-9a3d-0d415b466b87

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sliceCost_sub_zero

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {s t : ℝ}
    (hs : s < 1) (ht : t < 1) :
    MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
        MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 ≤
      -t / (2 * Real.log 2) := by
  rw [sliceCost_sub_zero hs ht]
  have hlog : Real.log (1 - t) ≤ -t := by
    simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 - t)
  have hbase : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold Real.logb
  calc
    (1 / 2 : ℝ) * (Real.log (1 - t) / Real.log 2) =
        Real.log (1 - t) / (2 * Real.log 2) := by
          field_simp
    _ ≤ -t / (2 * Real.log 2) :=
      (div_le_div_iff_of_pos_right (by positivity)).2 hlog
end MetricCodes.Spherical.HigherHierarchy
