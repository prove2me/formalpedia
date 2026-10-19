-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_tail_of_head_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/a65a7fe7-18e6-416b-81fe-4f8aac299d6f

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_Phi_prepend

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
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 4000000
open scoped BigOperators
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution {r : ℕ}
    (a : Fin (r + 2) → ℝ) (b : Fin (r + 1) → ℝ)
    (hcollision : a 0 = b 0) :
    Phi a b = Phi (Fin.tail a) (Fin.tail b) := by
  conv_lhs =>
    rw [← Fin.cons_self_tail a, ← Fin.cons_self_tail b]
  change Phi (prependAmbient (a 0) (Fin.tail a))
    (prependStabilizer (b 0) (Fin.tail b)) = _
  rw [Phi_prepend]
  simp [hcollision]
end MetricCodes.Spherical.HigherHierarchy
