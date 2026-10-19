-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxSpectral.constantRayleigh_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/46b42661-9f5c-4e23-9268-1293c4b25300

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxSpectral_adjacencyMatrix_sum

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
    constantRayleigh edge =
      (2 * ∑ v : BoxVertex r m, ∑ i : Fin (r + 1),
        if (v i).val < m then edge v i else 0) /
          (Fintype.card (BoxVertex r m) : ℝ) := by
  rw [constantRayleigh, adjacencyMatrix_sum]
end MetricCodes.Spherical.HigherHierarchyBoxSpectral
