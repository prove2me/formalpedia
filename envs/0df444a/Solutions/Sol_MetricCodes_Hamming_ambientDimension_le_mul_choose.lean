-- Prove2me | solution 1 for MetricCodes.Hamming.ambientDimension_le_mul_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/8424c55d-bf04-489b-87c2-73c57db3a7b6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_choose_monotone_to_half

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    (n k L : ℕ) (hkL : k ≤ L) (hL : L ≤ n / 2) :
    ambientDimension n k L ≤ (n + 1) * n.choose L := by
  calc
    ambientDimension n k L =
        ∑ j ∈ Finset.range (L - k + 1), n.choose (k + j) := rfl
    _ ≤ ∑ _j ∈ Finset.range (L - k + 1), n.choose L := by
      apply Finset.sum_le_sum
      intro j hj
      have hj' : j < L - k + 1 := Finset.mem_range.mp hj
      apply MetricCodes.choose_monotone_to_half n (by omega) hL
    _ = (L - k + 1) * n.choose L := by simp
    _ ≤ (n + 1) * n.choose L := by
      apply Nat.mul_le_mul_right
      omega
end MetricCodes.Hamming
