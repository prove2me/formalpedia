-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_complement_longitudinalDegree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/fab19c5d-8753-4d6e-ae88-30f480598735

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_complement_longitudinalDegree_floor_le

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
    (ha : 0 ≤ a) (ha' : a < 1) :
    Tendsto (fun n : ℕ => n - longitudinalDegree a n) atTop atTop := by
  have hcomp : Tendsto (longitudinalDegree (1 - a)) atTop atTop := by
    change Tendsto
      (fun n : ℕ => Nat.floor ((1 - a) * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop (1 - a) (sub_pos.mpr ha')
  exact tendsto_atTop_mono
    (fun n => complement_longitudinalDegree_floor_le ha ha'.le n)
    hcomp
end MetricCodes.Hamming
