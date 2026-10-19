-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_transverse_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/1ad435a5-42be-4dde-8d8a-4be32b669915

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
theorem _root_.solution {b : ℝ} (hb : 0 ≤ b) :
    Tendsto (fun n : ℕ => (transverseDegree b n : ℝ) / (n : ℝ))
      atTop (nhds b) := by
  simpa [transverseDegree, Function.comp_def] using
    (tendsto_nat_floor_mul_div_atTop hb).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
end MetricCodes.Hamming
