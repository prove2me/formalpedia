-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.localizedLevelRate_one_lt_localizedRowRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/ea0e8007-599d-485b-8ca5-e072a77fef29

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_localized_level_one_lt_row_of_lowerSemicontinuous
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_variationalRate_lowerSemicontinuousOn_Icc

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    localizedLevelRate 1 s < localizedRowRate s := by
  unfold localizedLevelRate localizedRowRate
  exact localized_level_one_lt_row_of_lowerSemicontinuous hs hs'
    (variationalRate_lowerSemicontinuousOn_Icc hs hs')
end MetricCodes.Spherical.HigherHierarchy
