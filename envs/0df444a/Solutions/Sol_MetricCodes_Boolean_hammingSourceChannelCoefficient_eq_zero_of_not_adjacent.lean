-- Prove2me | solution 1 for MetricCodes.Boolean.hammingSourceChannelCoefficient_eq_zero_of_not_adjacent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/1a5d2a74-3364-42ac-925c-43c4bb7a7b5e

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
    (n k L : ℕ)
    (source target : Fin (L - k + 1))
    (hnot : ¬ (target.val + 1 = source.val ∨
      source.val + 1 = target.val)) :
    hammingSourceChannelCoefficient n k L source target = 0 := by
  have hforward : source.val + 1 ≠ target.val := by
    intro h
    exact hnot (Or.inr h)
  have hbackward : target.val + 1 ≠ source.val := by
    intro h
    exact hnot (Or.inl h)
  simp [hammingSourceChannelCoefficient,
    MetricCodes.hammingJacobiMatrix, hforward, hbackward]
end MetricCodes.Boolean
