-- Prove2me | solution 1 for MetricCodes.Hamming.hammingFibreDimension_le_choose
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/25d78c1e-6792-45f8-8d32-56f8622dda0d

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
theorem _root_.solution (n k : ℕ) :
    MetricCodes.hammingFibreDimension n k ≤ n.choose k := by
  cases k with
  | zero => simp [MetricCodes.hammingFibreDimension, MetricCodes.booleanHarmonicDimension]
  | succ j =>
      change n.choose (j + 1) - n.choose j ≤ n.choose (j + 1)
      exact Nat.sub_le _ _
end MetricCodes.Hamming
