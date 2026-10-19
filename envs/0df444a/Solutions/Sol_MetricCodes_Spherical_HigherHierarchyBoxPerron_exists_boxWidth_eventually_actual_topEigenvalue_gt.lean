-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchyBoxPerron.exists_boxWidth_eventually_actual_topEigenvalue_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:42.304385+00:00
-- url     : https://prove2.me/submissions/cf524cb0-082d-457e-b738-a5f7d5edacda

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_edgeWeight
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_exists_boxWidth_spectral_gap
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchyBoxPerron_eventually_topEigenvalue_gt_of_edge_limits

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
theorem _root_.solution {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {s : ℝ}
    (hspectral : s < 2 * HigherHierarchy.Gamma a b) :
    ∃ m : ℕ, 0 < m ∧
      ∀ᶠ n : ℕ in atTop,
        s < HigherHierarchyFinitePerron.topEigenvalue
          (adjacencyMatrix
            (HigherHierarchy.RectangularVertices.edgeWeight
              (m := m) a b n)) := by
  obtain ⟨m, hm, hmargin⟩ :=
    exists_boxWidth_spectral_gap hspectral
  refine ⟨m, hm, ?_⟩
  apply eventually_topEigenvalue_gt_of_edge_limits
    (HigherHierarchy.RectangularVertices.edgeWeight (m := m) a b)
    (fun i => lagrangeWeight a b i * spectralAtom (a i))
    (fun v i =>
      HigherHierarchy.RectangularVertices.tendsto_edgeWeight a b h v i)
  simpa [HigherHierarchy.Gamma] using hmargin
end MetricCodes.Spherical.HigherHierarchyBoxPerron
