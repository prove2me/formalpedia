-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.oneRowBoundaryObjective_classicalThreshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/ff9744b3-1e18-4c36-bdcb-60294e9c480e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_boundaryDegree_classicalThreshold_eq_zero

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
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    oneRowBoundaryObjective s (MetricCodes.classicalThreshold s) =
      MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  simp [oneRowBoundaryObjective,
    boundaryDegree_classicalThreshold_eq_zero hs hs']
end MetricCodes.Spherical.HigherHierarchy
