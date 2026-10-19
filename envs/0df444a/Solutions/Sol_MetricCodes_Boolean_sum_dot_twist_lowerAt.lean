-- Prove2me | solution 1 for MetricCodes.Boolean.sum_dot_twist_lowerAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/59f40645-8b2b-4116-b7f4-90768a0cb15a

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
    (∑ a : Fin n, dot f (twist x (lowerAt a g))) =
      dot f (twist x (lower g)) := by
  classical
  unfold dot twist lower
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum]
end MetricCodes.Boolean
