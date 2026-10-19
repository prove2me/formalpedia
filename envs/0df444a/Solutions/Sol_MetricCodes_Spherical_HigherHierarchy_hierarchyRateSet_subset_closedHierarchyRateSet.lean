-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyRateSet_subset_closedHierarchyRateSet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/df89bdb6-d70d-41ed-bb17-a7dfd00da6ba

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
theorem _root_.solution (s : ℝ) :
    hierarchyRateSet s ⊆ closedHierarchyRateSet s := by
  rintro z ⟨r, a, b, hinterlacing, hspectral, rfl⟩
  exact ⟨r, a, b, hinterlacing, hspectral.le, rfl⟩
end MetricCodes.Spherical.HigherHierarchy
