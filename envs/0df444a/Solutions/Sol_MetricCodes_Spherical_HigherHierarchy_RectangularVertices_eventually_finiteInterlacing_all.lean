-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.eventually_finiteInterlacing_all
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/62d11102-c8a5-4f4e-9467-a714cf83b56d

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherRepresentationGraph_StrictInterlaces_interlaces
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_strictInterlaces_all

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
    (h : Interlacing a b) :
    ∀ᶠ n : ℕ in atTop, ∀ v : Vertex r m,
      FiniteInterlacing n (signature a n v) (flooredCoordinates b n) := by
  filter_upwards [eventually_strictInterlaces_all (m := m) a b h,
    eventually_ge_atTop (2 * r + 4)] with n hn hstable
  intro v
  exact ⟨hstable, (hn v).interlaces⟩
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
