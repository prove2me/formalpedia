-- Prove2me | solution 1 for MetricCodes.Boolean.deleteChannel_orthogonal_addChannel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/7bd8abdc-682b-43a7-b422-a0b0f963cbfb

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
open scoped BigOperators Matrix
open MetricCodes.Boolean
variable {n : ℕ}
namespace MetricCodes.Boolean
theorem _root_.solution (i j : ℕ)
    (f g : Function n) :
    coordinateDot (deleteChannel i f) (addChannel j g) = 0 := by
  classical
  unfold coordinateDot deleteChannel addChannel
  apply Finset.sum_eq_zero
  intro a _
  rw [dot_smul_left, dot_smul_right, dot_lowerAt_raiseAt]
  simp
end MetricCodes.Boolean
