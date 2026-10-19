-- Prove2me | solution 1 for MetricCodes.Hamming.complement_longitudinalDegree_floor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/d2079cd6-7bb6-4bef-a81c-95ef0d2fe7b8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (n : ℕ) :
    longitudinalDegree (1 - a) n ≤ n - longitudinalDegree a n := by
  have hk := longitudinalDegree_le_dimension ha' n
  have hfloor : (longitudinalDegree a n : ℝ) ≤ a * (n : ℝ) := by
    unfold longitudinalDegree
    exact Nat.floor_le (mul_nonneg ha (Nat.cast_nonneg n))
  change Nat.floor ((1 - a) * (n : ℝ)) ≤
    n - longitudinalDegree a n
  apply Nat.floor_le_of_le
  change (1 - a) * (n : ℝ) ≤
    ((n - longitudinalDegree a n : ℕ) : ℝ)
  rw [Nat.cast_sub hk]
  nlinarith
end MetricCodes.Hamming
