-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_sphericalCodeNumber_lt_hierarchyVariationalRate_of_code_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:40.232469+00:00
-- url     : https://prove2.me/submissions/6ebcac64-487a-4e3d-89f3-08e0e67e437f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_MaximalCodeBounds_sphericalCodeNumber_toNat_lt_iff
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
    (hcode : FixedLevelHierarchyCodeBound)
    {s ε : ℝ} (hs : 0 < s) (hs' : s < 1) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((SpherePacking.sphericalCodeNumber n s).toNat : ℝ) <
        (2 : ℝ) ^ ((hierarchyVariationalRate s + ε) * (n : ℝ)) := by
  have hnonempty := hierarchyRateSet_nonempty_of_interior hs hs'
  have hlt :
      sInf (hierarchyRateSet s) < hierarchyVariationalRate s + ε := by
    change hierarchyVariationalRate s < hierarchyVariationalRate s + ε
    linarith
  obtain ⟨z, ⟨r, a, b, hinterlacing, hspectral, rfl⟩, hrate⟩ :=
    exists_lt_of_csInf_lt hnonempty hlt
  filter_upwards [hcode hs hs' a b hinterlacing hspectral hrate]
    with n hn
  exact
    (MetricCodes.Spherical.MaximalCodeBounds.sphericalCodeNumber_toNat_lt_iff
      hs').2 hn
end MetricCodes.Spherical.HigherHierarchy
