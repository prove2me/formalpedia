-- Prove2me | solution 1 for MetricCodes.Boolean.dot_hammingWindowBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:27.702855+00:00
-- url     : https://prove2.me/submissions/b38049f5-5fa4-40c3-84cf-37919f0dca7e

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
theorem _root_.solution (n k L : ℕ)
    (S T : HammingWindowIndex n k L) :
    dot (hammingWindowBasis n k L S)
        (hammingWindowBasis n k L T) =
      if S.2.val = T.2.val then 1 else 0 := by
  classical
  by_cases h : S.2.val = T.2.val
  · unfold dot hammingWindowBasis
    rw [if_pos h, Finset.sum_eq_single S.2.val]
    · rw [if_pos rfl, if_pos h]
      norm_num
    · intro U _ hU
      rw [if_neg hU, zero_mul]
    · simp
  · have h' : T.2.val ≠ S.2.val := Ne.symm h
    simp [dot, hammingWindowBasis, h, h']
end MetricCodes.Boolean
