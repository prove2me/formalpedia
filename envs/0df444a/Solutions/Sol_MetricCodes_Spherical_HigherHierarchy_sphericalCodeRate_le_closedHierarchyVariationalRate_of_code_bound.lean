-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.sphericalCodeRate_le_closedHierarchyVariationalRate_of_code_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/2292399e-e0ba-4a6a-a96a-27f04e93c835

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_hierarchyVariationalRate_nonneg
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_closedHierarchyVariationalRate_eq_hierarchyVariationalRate
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sphericalCodeRate_le_of_eventually_exponential
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_eventually_sphericalCodeNumber_lt_hierarchyVariationalRate_of_code_bound

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
    (hcode : FixedLevelHierarchyCodeBound)
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    sphericalCodeRate s ≤ closedHierarchyVariationalRate s := by
  rw [closedHierarchyVariationalRate_eq_hierarchyVariationalRate hs hs']
  apply le_of_forall_pos_le_add
  intro ε hε
  exact sphericalCodeRate_le_of_eventually_exponential
    (by linarith [hierarchyVariationalRate_nonneg hs hs'])
    (eventually_sphericalCodeNumber_lt_hierarchyVariationalRate_of_code_bound
      hcode hs hs' hε)
end MetricCodes.Spherical.HigherHierarchy
