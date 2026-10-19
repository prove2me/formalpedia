-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.Phi_drop_second_of_collision
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:38.99809+00:00
-- url     : https://prove2.me/submissions/a9e4e9a1-8eed-4547-8ed9-ee3a2a895c85

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (hcollision : b 0 = a (1 : Fin (r + 2))) :
    Phi a b =
      Phi (Fin.cons (a 0) (Fin.tail (Fin.tail a))) (Fin.tail b) := by
  simp [Phi, Fin.sum_univ_succ, Fin.tail, hcollision]
  ring
end MetricCodes.Spherical.HigherHierarchy
