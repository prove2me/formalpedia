-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_norm_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/2f4fd8ea-e0bf-4850-9e1d-405bc1de7cf1

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
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxPerron
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyBoxPerron
theorem _root_.solution (r m : ℕ) :
    ‖constantVector r m‖ ^ 2 =
      (Fintype.card (BoxVertex r m) : ℝ) := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [constantVector]
end MetricCodes.Spherical.HigherHierarchyBoxPerron
