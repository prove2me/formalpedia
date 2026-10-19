-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_threshold_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/5a5f6558-5af2-4ea6-9db8-96ff94b1c7f0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_ceil_distance_ratio

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
      (fun n : ℕ => threshold n (Nat.ceil (δ * (n : ℝ))))
      atTop (nhds (1 - 2 * δ)) := by
  have hratio := tendsto_ceil_distance_ratio hδ
  have hlimit :=
    (tendsto_const_nhds (x := (1 : ℝ))).sub
      ((tendsto_const_nhds (x := (2 : ℝ))).mul hratio)
  refine hlimit.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold threshold
  ring
end MetricCodes.Hamming
