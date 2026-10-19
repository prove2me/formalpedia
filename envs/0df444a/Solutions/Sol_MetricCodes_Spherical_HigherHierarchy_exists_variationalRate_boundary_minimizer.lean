-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_variationalRate_boundary_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:39.667497+00:00
-- url     : https://prove2.me/submissions/4c6bcad1-720f-496b-b891-d1081dd1ec00

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_CompactificationEntropy_tendsto_entropy_sub_boundaryDegree
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_exists_variationalRate_boundary_minimizer_of_boundary_limit

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
    ∃ a : ℝ, MetricCodes.classicalThreshold s < a ∧
      MetricCodes.Spherical.variationalRate s = oneRowBoundaryObjective s a ∧
      ∀ t : ℝ, MetricCodes.classicalThreshold s < t →
        oneRowBoundaryObjective s a ≤ oneRowBoundaryObjective s t := by
  apply exists_variationalRate_boundary_minimizer_of_boundary_limit hs hs'
  simpa [oneRowBoundaryObjective] using
    (CompactificationEntropy.tendsto_entropy_sub_boundaryDegree hs hs')
end MetricCodes.Spherical.HigherHierarchy
