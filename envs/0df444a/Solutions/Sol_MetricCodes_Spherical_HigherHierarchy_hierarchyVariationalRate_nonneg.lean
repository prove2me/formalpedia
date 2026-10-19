-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.hierarchyVariationalRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/4d4ce07c-26d9-41ca-ada7-3340fc679d14

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_Phi_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyRateSet_nonempty_of_interior

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
    0 ≤ hierarchyVariationalRate s := by
  unfold hierarchyVariationalRate
  apply le_csInf (hierarchyRateSet_nonempty_of_interior hs hs')
  rintro z ⟨r, a, b, h, _, rfl⟩
  exact h.Phi_nonneg
end MetricCodes.Spherical.HigherHierarchy
