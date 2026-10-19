-- Prove2me | solution 1 for MetricCodes.Spherical.quadratic_iff_boundaryDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:35.361684+00:00
-- url     : https://prove2.me/submissions/523e2ceb-4958-4859-9fc7-cdfc9b6e0fd3

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_pos
import Theorems.Thm_MetricCodes_Spherical_boundaryDegree_mul_one_add

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
theorem _root_.solution {s a b : ℝ}
    (hb : 0 ≤ b) (hQ : 0 < boundaryQuadratic s a) :
    b * (1 + b) < boundaryQuadratic s a ↔ b < boundaryDegree s a := by
  have hroot := boundaryDegree_mul_one_add hQ.le
  have hpositive := boundaryDegree_pos hQ
  constructor
  · intro h
    by_contra hnot
    have hge : boundaryDegree s a ≤ b := le_of_not_gt hnot
    nlinarith [sq_nonneg (b - boundaryDegree s a)]
  · intro h
    nlinarith [sq_nonneg (b - boundaryDegree s a)]
end MetricCodes.Spherical
