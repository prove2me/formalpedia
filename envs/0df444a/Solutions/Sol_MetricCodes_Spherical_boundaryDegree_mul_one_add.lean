-- Prove2me | solution 1 for MetricCodes.Spherical.boundaryDegree_mul_one_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/6f6f130f-784f-4e3d-97b3-e5dcd9cbe222

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
open MetricCodes
open MetricCodes.Spherical
noncomputable section
namespace MetricCodes.Spherical
theorem _root_.solution {s a : ℝ}
    (hQ : 0 ≤ boundaryQuadratic s a) :
    boundaryDegree s a * (1 + boundaryDegree s a) =
      boundaryQuadratic s a := by
  have hrad : 0 ≤ 1 + 4 * boundaryQuadratic s a := by linarith
  have hsquare := Real.sq_sqrt hrad
  unfold boundaryDegree
  nlinarith
end MetricCodes.Spherical
