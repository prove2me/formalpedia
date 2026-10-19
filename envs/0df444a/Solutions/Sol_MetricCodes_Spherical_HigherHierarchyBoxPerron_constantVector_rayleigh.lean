-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.constantVector_rayleigh
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/0e9111f5-d330-42f0-844e-9507e755858a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_constantVector_norm_sq

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
    HigherHierarchyFinitePerron.rayleigh
      (adjacencyMatrix edge) (constantVector r m) =
      constantRayleigh edge := by
  change
    @inner ℝ (HigherHierarchyFinitePerron.Space (BoxVertex r m)) _
      (HigherHierarchyFinitePerron.operator
        (adjacencyMatrix edge) (constantVector r m))
      (constantVector r m) /
        ‖constantVector r m‖ ^ 2 = constantRayleigh edge
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ v : BoxVertex r m,
      (∑ w : BoxVertex r m,
        adjacencyMatrix edge v w * (1 : ℝ)) * (1 : ℝ)) /
          ‖constantVector r m‖ ^ 2 = constantRayleigh edge
  simp only [mul_one]
  rw [constantVector_norm_sq]
  rfl
end MetricCodes.Spherical.HigherHierarchyBoxPerron
