-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.classicalThreshold_entropy_lt_neg_logb_of_compactified_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/05f53677-fa0c-478b-8193-405c7ec3cdd3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_classicalThreshold_entropy_lt_half_neg_logb
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_compactified_zero_residual_cost_le

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
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s c : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hc : 0 < c) (hfeasible : s ≤ 1 - c ^ 2) :
    MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) <
      -Real.logb 2 c :=
  (classicalThreshold_entropy_lt_half_neg_logb hs hs').trans_le
    (compactified_zero_residual_cost_le hs hs' hc hfeasible)
end MetricCodes.Spherical.HigherHierarchy
