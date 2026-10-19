-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_ceil_distance_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/fb1ca2ba-6f53-482a-8b90-a85427ded7d7

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
theorem _root_.solution {δ : ℝ} (hδ : 0 ≤ δ) :
    Tendsto
      (fun n : ℕ => (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ))
      atTop (nhds δ) := by
  simpa [Function.comp_def] using
    (tendsto_nat_ceil_mul_div_atTop hδ).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
end MetricCodes.Hamming
