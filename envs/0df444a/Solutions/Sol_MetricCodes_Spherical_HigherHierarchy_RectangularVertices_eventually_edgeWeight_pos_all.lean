-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_edgeWeight_pos_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/2811d803-84bc-41a1-ab7f-3f05fdd3c673

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Interlacing_lagrangeWeight_pos
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_edgeWeight

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
open scoped BigOperators Topology
open MetricCodes.Spherical.HigherHierarchy MetricCodes.Spherical.HigherHierarchy.RectangularVertices
open MetricCodes.Spherical.HigherChannel
namespace MetricCodes.Spherical.HigherHierarchy.RectangularVertices
theorem _root_.solution {r m : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (h : Interlacing a b) (ha : ∀ i, 0 < a i) :
    ∀ᶠ n : ℕ in atTop, ∀ (v : Vertex r m) (i : Fin (r + 1)),
      0 < edgeWeight a b n v i := by
  apply eventually_all.2
  intro v
  apply eventually_all.2
  intro i
  have hai : 0 < a i := ha i
  have hquad : 0 < quadraticCoordinate (a i) := by
    unfold quadraticCoordinate
    exact mul_pos hai (by linarith)
  have hatom : 0 < spectralAtom (a i) := by
    unfold spectralAtom
    exact div_pos (Real.sqrt_pos.mpr hquad) (by linarith)
  exact (tendsto_edgeWeight a b h v i).eventually
    (Ioi_mem_nhds (mul_pos (h.lagrangeWeight_pos i) hatom))
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
