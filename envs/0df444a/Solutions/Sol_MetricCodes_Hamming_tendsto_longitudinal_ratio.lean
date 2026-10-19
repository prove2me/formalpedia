-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_longitudinal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/b4651cea-4bb4-4ca6-8db8-59a8eed6e553

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
theorem _root_.solution {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (fun n : ℕ => (longitudinalDegree a n : ℝ) / (n : ℝ))
      atTop (nhds a) := by
  simpa [longitudinalDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
end MetricCodes.Hamming
