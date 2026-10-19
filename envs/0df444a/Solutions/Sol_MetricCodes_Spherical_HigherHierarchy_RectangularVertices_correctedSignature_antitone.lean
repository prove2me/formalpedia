-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.RectangularVertices.correctedSignature_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:41.72687+00:00
-- url     : https://prove2.me/submissions/c32bd780-d034-4df0-bf94-6d7fad57ce07

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Weyl_flooredWeight_antitone

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
    (a : Fin (r + 1) → ℝ) (hanti : Antitone a)
    (v : ℕ → Vertex r m) (n : ℕ) :
    Antitone (correctedSignature a v n) := by
  classical
  unfold correctedSignature
  split_ifs with h
  · exact h
  · exact Weyl.flooredWeight_antitone hanti n
end MetricCodes.Spherical.HigherHierarchy.RectangularVertices
