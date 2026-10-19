-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.closedHierarchyVariationalRate_eq_hierarchyVariationalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/49329bb0-7fa0-47b9-9a09-cb17053a332f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_subset_closedHierarchyRateSet
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_closedHierarchyRateSet_bddBelow
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_closedHierarchyRateSet_nonempty_of_interior
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_strict_hierarchy_refinement_of_closed

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
    closedHierarchyVariationalRate s = hierarchyVariationalRate s := by
  apply le_antisymm
  · exact csInf_le_csInf (closedHierarchyRateSet_bddBelow s)
      (hierarchyRateSet_nonempty_of_interior hs hs')
      (hierarchyRateSet_subset_closedHierarchyRateSet s)
  · unfold closedHierarchyVariationalRate
    apply le_csInf (closedHierarchyRateSet_nonempty_of_interior hs hs')
    rintro z ⟨r, a, b, hinterlacing, hspectral, rfl⟩
    obtain ⟨r', A, B, hAB, hGamma, hPhi⟩ :=
      exists_strict_hierarchy_refinement_of_closed
        hs a b hinterlacing hspectral
    exact (hierarchyVariationalRate_le_of_feasible hAB hGamma).trans hPhi.le
end MetricCodes.Spherical.HigherHierarchy
