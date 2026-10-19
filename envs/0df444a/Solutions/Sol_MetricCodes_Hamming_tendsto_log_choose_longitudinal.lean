-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_log_choose_longitudinal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/d4640544-f9dd-42fd-8735-29cd8b7918b6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_add_choose_div
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension
import Theorems.Thm_MetricCodes_Hamming_tendsto_complement_longitudinalDegree
import Theorems.Thm_MetricCodes_Hamming_tendsto_complement_longitudinal_ratio

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
    (ha : 0 < a) (ha' : a < 1) :
    Tendsto
      (fun n : ℕ =>
        Real.log (n.choose (longitudinalDegree a n) : ℝ) / (n : ℝ))
      atTop (nhds (Real.binEntropy a)) := by
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  have hcomplement := tendsto_complement_longitudinalDegree ha.le ha'
  have hratio := tendsto_longitudinal_ratio ha.le
  have hcomplementratio :=
    tendsto_complement_longitudinal_ratio ha.le ha'.le
  have hchoose := SpherePacking.tendsto_log_add_choose_div
    (longitudinalDegree a)
    (fun n : ℕ => n - longitudinalDegree a n)
    a (1 - a)
    hgrowth hcomplement hratio hcomplementratio ha (sub_pos.mpr ha')
  have hlimit :
      (a + (1 - a)) * Real.log (a + (1 - a)) -
        a * Real.log a - (1 - a) * Real.log (1 - a) =
        Real.binEntropy a := by
    simp [Real.binEntropy, Real.log_inv]
    ring
  rw [hlimit] at hchoose
  refine hchoose.congr' (Filter.Eventually.of_forall fun n => ?_)
  have hk := longitudinalDegree_le_dimension ha'.le n
  have hsum :
      longitudinalDegree a n + (n - longitudinalDegree a n) = n := by
    omega
  rw [hsum]
end MetricCodes.Hamming
