-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency.matrix_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/ae138351-7724-4279-9cb0-3e74f1d9924d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyTrueGridAdjacency_edgeWeight_nonneg

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
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (n : ℕ)
    (v w : Vertex r m) : 0 ≤ matrix a b n v w := by
  change
    0 ≤ forwardMatrix (edgeWeight (m := m) a b n) v w +
      forwardMatrix (edgeWeight (m := m) a b n) w v
  apply add_nonneg
  · unfold forwardMatrix
    exact Finset.sum_nonneg fun i _ => by
      split_ifs <;> first | exact edgeWeight_nonneg a b n v i | exact le_rfl
  · unfold forwardMatrix
    exact Finset.sum_nonneg fun i _ => by
      split_ifs <;> first | exact edgeWeight_nonneg a b n w i | exact le_rfl
end MetricCodes.Spherical.HigherHierarchyTrueGridAdjacency
