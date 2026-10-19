-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.trueGrid_matrix_eq_rectangular
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/09283847-aa9c-47f8-bf71-1e4897b54293

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
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ) :
    HigherHierarchyTrueGridAdjacency.matrix (m := m) a b n =
      adjacencyMatrix
        (HigherHierarchy.RectangularVertices.edgeWeight
          (m := m) a b n) := by
  rfl
end MetricCodes.Spherical.HigherHierarchyBoxPerron
