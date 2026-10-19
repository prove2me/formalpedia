-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.levelRate_one_lt_variationalRate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/de705fee-7d71-4d9a-85d9-31c83e50deed

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_levelRate_one_lt_variationalRate_of_boundary_minimizer
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_variationalRate_boundary_minimizer

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
    levelRate 1 s < MetricCodes.Spherical.variationalRate s := by
  obtain ⟨a, ha, hmin, _⟩ :=
    exists_variationalRate_boundary_minimizer hs hs'
  exact levelRate_one_lt_variationalRate_of_boundary_minimizer
    hs hs' ha hmin
end MetricCodes.Spherical.HigherHierarchy
