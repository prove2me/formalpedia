-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.constantRayleigh_le_top
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/9f7e014f-a0ee-49b6-a875-60919ee1ae5f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyFinitePerron_rayleigh_le_top
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_constantVector_ne_zero
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_constantVector_rayleigh

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
    (edge : BoxVertex r m → Fin (r + 1) → ℝ) :
    constantRayleigh edge ≤
      HigherHierarchyFinitePerron.topEigenvalue (adjacencyMatrix edge) := by
  rw [← constantVector_rayleigh]
  exact HigherHierarchyFinitePerron.rayleigh_le_top (adjacencyMatrix edge)
    (constantVector r m) (constantVector_ne_zero r m)
end MetricCodes.Spherical.HigherHierarchyBoxPerron
