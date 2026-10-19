-- Prove2me | solution 1 for MetricCodes.Boolean.dot_hammingWindowBasis_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/ebf91f3e-031a-421e-9313-6ad69d975a84

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
    (n k L : ℕ) (Q : HammingWindowIndex n k L)
    (f : Function n) :
    dot (hammingWindowBasis n k L Q) f = f Q.2.val := by
  classical
  unfold dot hammingWindowBasis
  rw [Finset.sum_eq_single Q.2.val]
  · rw [if_pos rfl, one_mul]
  · intro S _ hS
    rw [if_neg hS, zero_mul]
  · simp
end MetricCodes.Boolean
