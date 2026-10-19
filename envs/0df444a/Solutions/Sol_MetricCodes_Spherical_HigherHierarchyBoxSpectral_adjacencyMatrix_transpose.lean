-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.adjacencyMatrix_transpose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/29d589bd-f7b3-4467-8998-1cbd6354bc38

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
open scoped BigOperators Matrix Topology
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchyBoxSpectral
theorem _root_.solution {r m : ℕ}
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    (adjacencyMatrix edge)ᵀ = adjacencyMatrix edge := by
  simp [adjacencyMatrix, add_comm]
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
