-- Prove2me | solution 1 for MetricCodes.Hamming.longitudinalDegree_le_dimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/1d500f21-7225-41de-937a-61005e8063ff

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

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
    (ha : a ≤ 1) (n : ℕ) :
    longitudinalDegree a n ≤ n := by
  unfold longitudinalDegree
  apply Nat.floor_le_of_le
  simpa using mul_le_mul_of_nonneg_right ha (Nat.cast_nonneg n)
end MetricCodes.Hamming
