-- Prove2me | solution 1 for MetricCodes.Spherical.boundaryDegree_lt_longitudinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/29dc70c7-3471-41be-ac93-3298e8046fae

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
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s a : ℝ} (hs : 0 < s) (ha : 0 < a)
    (hquadratic : 0 < boundaryQuadratic s a) :
    boundaryDegree s a < a := by
  have hb := boundaryDegree_pos hquadratic
  have heq := boundaryDegree_mul_one_add hquadratic.le
  have hroot : 0 < Real.sqrt (a * (1 + a)) := by positivity
  have hstrict : boundaryQuadratic s a < a * (1 + a) := by
    unfold boundaryQuadratic
    have hterm : 0 < (s / 2) * (1 + 2 * a) *
        Real.sqrt (a * (1 + a)) := by positivity
    linarith
  nlinarith [sq_nonneg (a - boundaryDegree s a)]
end MetricCodes.Spherical
