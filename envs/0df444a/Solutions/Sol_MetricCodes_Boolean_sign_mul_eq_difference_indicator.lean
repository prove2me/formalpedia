-- Prove2me | solution 1 for MetricCodes.Boolean.sign_mul_eq_difference_indicator
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/a876b51c-aad8-4c04-9e59-8ba39382505b

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
theorem _root_.solution (b c : Bool) :
    sign b * sign c =
      1 - 2 * (if b ≠ c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> norm_num [sign]
end MetricCodes.Boolean
