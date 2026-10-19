-- Prove2me | solution 1 for MetricCodes.Hamming.choose_le_ambientDimension
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/1fdf022b-598b-44b2-abb6-5f7402ae5bfb

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
theorem _root_.solution (n k L : ℕ) (hkL : k ≤ L) :
    n.choose L ≤ ambientDimension n k L := by
  unfold ambientDimension
  have hindex : L - k ∈ Finset.range (L - k + 1) := by
    simp
  have hterm := Finset.single_le_sum
    (s := Finset.range (L - k + 1))
    (f := fun j => n.choose (k + j))
    (fun j _ => Nat.zero_le _) hindex
  have hdegree : k + (L - k) = L := by omega
  simpa [hdegree] using hterm
end MetricCodes.Hamming
