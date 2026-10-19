-- Prove2me | solution 1 for MetricCodes.Boolean.sum_dot_twist_raiseAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/7f8f1b8f-c692-4c3e-870e-dc27c0d209c8

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
theorem _root_.solution
    (x : BinaryWord n) (f g : Function n) :
    (∑ a : Fin n, dot f (twist x (raiseAt a g))) =
      dot f (twist x (raise g)) := by
  classical
  unfold dot twist raise
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
end MetricCodes.Boolean
