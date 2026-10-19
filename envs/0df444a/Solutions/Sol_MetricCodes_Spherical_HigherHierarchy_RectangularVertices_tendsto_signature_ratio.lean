-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.tendsto_signature_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/543f1365-8982-41f7-a98d-c8b3ab055e1c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherChannel_tendsto_flooredCoordinates_ratio
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_RectangularVertices_tendsto_offset_div

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
    (a : Fin (r + 1) → ℝ) (v : ℕ → Vertex r m)
    (i : Fin (r + 1)) (ha : 0 ≤ a i) :
    Tendsto (fun n : ℕ => (signature a n (v n) i : ℝ) / (n : ℝ))
      atTop (𝓝 (a i)) := by
  have hfloor := tendsto_flooredCoordinates_ratio a i ha
  have hoffset := tendsto_offset_div v i
  convert hfloor.add hoffset using 1
  · ext n
    simp [signature, Nat.cast_add, add_div]
  · simp
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
