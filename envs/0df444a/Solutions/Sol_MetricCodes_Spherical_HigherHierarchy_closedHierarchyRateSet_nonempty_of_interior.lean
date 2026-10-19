-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.closedHierarchyRateSet_nonempty_of_interior
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/87908ab5-419a-48a9-bacd-ebc35ae2b964

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_subset_closedHierarchyRateSet

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
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    (closedHierarchyRateSet s).Nonempty :=
  (hierarchyRateSet_nonempty_of_interior hs hs').mono
    (hierarchyRateSet_subset_closedHierarchyRateSet s)
end MetricCodes.Spherical.HigherHierarchy
