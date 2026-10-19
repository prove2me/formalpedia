-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_terminal_degree_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/79b099f0-07de-46c6-959c-0cd854875531

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio

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
    (ha : 0 < a) (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((longitudinalDegree a n - r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  have hoffset := tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have hmain := (tendsto_longitudinal_ratio ha.le).sub hoffset
  rw [sub_zero] at hmain
  have hgrowth : Tendsto (longitudinalDegree a) atTop atTop := by
    change Tendsto (fun n : ℕ => Nat.floor (a * (n : ℝ))) atTop atTop
    exact tendsto_nat_floor_mul_atTop a ha
  refine hmain.congr' ?_
  filter_upwards [hgrowth.eventually (eventually_ge_atTop r)] with n hn
  rw [Nat.cast_sub hn]
  ring
end MetricCodes.Hamming
