-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_variationalRate_boundary_minimizer_of_boundary_limit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/3ad84f20-2f67-4844-9364-dc100dcbe085

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_classicalThreshold_entropy_lt_half_neg_logb
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_variationalRate_boundary_minimizer_of_limit

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
    {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hlimit : Tendsto (fun a : ℝ => oneRowBoundaryObjective s a)
      atTop (𝓝 (-(1 / 2 : ℝ) * Real.logb 2 (1 - s)))) :
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t :=
  exists_variationalRate_boundary_minimizer_of_limit hs hs' hlimit
    (classicalThreshold_entropy_lt_half_neg_logb hs hs')
end MetricCodes.Spherical.HigherHierarchy
