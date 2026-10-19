-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_correctedSignature_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/891ac3b7-8a32-40e5-9bea-91f4810c613a

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_eventually_correctedSignature_eq

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
    (a : Fin (r + 1) → ℝ)
    (ha : ∀ i, 0 < a i) (hanti : StrictAnti a)
    (v : ℕ → Vertex r m) (i : Fin (r + 1)) :
    Tendsto (fun n : ℕ => correctedSignature a v n i) atTop atTop := by
  have hfloor :
      Tendsto (fun n : ℕ => flooredCoordinates a n i) atTop atTop := by
    exact tendsto_nat_floor_mul_atTop (a i) (ha i)
  apply tendsto_atTop_mono' atTop _ hfloor
  filter_upwards [eventually_correctedSignature_eq a
    (fun j => (ha j).le) hanti v] with n hn
  rw [hn]
  exact Nat.le_add_right _ _
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
