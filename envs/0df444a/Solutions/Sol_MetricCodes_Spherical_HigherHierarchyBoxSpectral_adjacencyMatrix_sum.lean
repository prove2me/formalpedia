-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.adjacencyMatrix_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/de59fe70-baee-407d-89ef-0cc3ffdec8c7

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_forwardMatrix_sum

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
    (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
      adjacencyMatrix edge v w) =
      2 * ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0 := by
  classical
  have htranspose :
      (∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
        (forwardMatrix edge)ᵀ v w) =
        ∑ v : BoxVertex r m, ∑ w : BoxVertex r m,
          forwardMatrix edge v w := by
    simp only [Matrix.transpose_apply]
    exact Finset.sum_comm
  simp_rw [adjacencyMatrix, Matrix.add_apply]
  simp_rw [Finset.sum_add_distrib]
  rw [htranspose, forwardMatrix_sum]
  ring
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
