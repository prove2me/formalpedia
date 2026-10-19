-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_complement_longitudinal_ratio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/4ab0fd0e-efe9-4913-8b66-88e8ef1232cd

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_tendsto_longitudinal_ratio
import Theorems.Thm_MetricCodes_Hamming_longitudinalDegree_le_dimension

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
    (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ => ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  have hone : Tendsto
      (fun n : ℕ => (n : ℝ) / (n : ℝ)) atTop (nhds 1) := by
    have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
      tendsto_const_nhds
    refine hconst.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    simp [hn]
  have hmain := hone.sub (tendsto_longitudinal_ratio ha)
  refine hmain.congr' (Filter.Eventually.of_forall fun n => ?_)
  change
    (n : ℝ) / (n : ℝ) -
      (longitudinalDegree a n : ℝ) / (n : ℝ) =
        ((n - longitudinalDegree a n : ℕ) : ℝ) / (n : ℝ)
  rw [Nat.cast_sub (longitudinalDegree_le_dimension ha' n)]
  ring
end MetricCodes.Hamming
