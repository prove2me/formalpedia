-- Prove2me | solution 1 for MetricCodes.spherical_dist_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/be1d95c5-3924-4726-b486-662d340b5830

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
noncomputable section
open scoped BigOperators InnerProductSpace
open MetricCodes
namespace MetricCodes
theorem _root_.solution {n : ℕ} (x y : Sphere n) :
    ‖(x : Ambient n) - (y : Ambient n)‖ ^ 2 =
      2 * (1 - sphericalInner x y) := by
  rw [norm_sub_sq_real]
  simp [x.property, y.property, sphericalInner]
  ring
end MetricCodes
