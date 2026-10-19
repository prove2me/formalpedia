-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.eventually_matrix_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/190f2800-be21-41ab-95eb-46ee3c24b013

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_edgeWeight_pos_all
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_matrix_irreducible

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
set_option maxHeartbeats 800000
open Filter Topology
open scoped BigOperators InnerProductSpace Matrix Topology
open MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
open MetricCodes.Spherical.HigherChannel
open MetricCodes.Spherical.HigherHierarchy
open MetricCodes.Spherical.HigherHierarchyBoxSpectral
namespace MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (ha : ∀ i, 0 < a i)
    (hm : 0 < m) :
    ∀ᶠ n : ℕ in atTop, (matrix (m := m) a b n).IsIrreducible := by
  filter_upwards
    [MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_edgeWeight_pos_all
      (m := m) a b h ha] with n hn
  apply matrix_irreducible a b n hm
  intro v i _
  exact hn v i
end MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
