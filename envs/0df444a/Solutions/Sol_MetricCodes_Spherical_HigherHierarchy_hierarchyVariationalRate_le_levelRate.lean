-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_le_levelRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/da596a85-e9d0-48a2-aea2-18e9cdfb70ca

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_le_of_feasible
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRateSet_nonempty_of_interior

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
set_option autoImplicit false
open Set Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {r : ℕ} {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    hierarchyVariationalRate s ≤ levelRate r s := by
  unfold levelRate
  apply le_csInf (levelRateSet_nonempty_of_interior r hs hs')
  rintro _ ⟨a, b, h, hgap, rfl⟩
  exact hierarchyVariationalRate_le_of_feasible h hgap
end MetricCodes.Spherical.HigherHierarchy
