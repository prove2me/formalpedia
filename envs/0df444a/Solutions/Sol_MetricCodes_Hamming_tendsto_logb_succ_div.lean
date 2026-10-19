-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_succ_div
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/ec522bbc-d84c-45b4-9fa3-cc8091df428c

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_SpherePacking_tendsto_log_two_mul_natCast_div_natCast

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution :
    Tendsto
      (fun n : ℕ => Real.logb 2 ((n + 1 : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0) :=
    tendsto_const_nhds
  have hupper := SpherePacking.tendsto_log_two_mul_natCast_div_natCast
  have hnonneg :
      ∀ᶠ n : ℕ in atTop,
        (0 : ℝ) ≤ Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    apply div_nonneg
    · apply Real.log_nonneg
      exact_mod_cast (show 1 ≤ n + 1 by omega)
    · exact Nat.cast_nonneg n
  have hle :
      ∀ᶠ n : ℕ in atTop,
        Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ) ≤
          Real.log (2 * (n : ℝ)) / (n : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    apply (div_le_div_iff_of_pos_right hnreal).2
    apply Real.log_le_log
    · positivity
    · have hnat : n + 1 ≤ 2 * n := by omega
      exact_mod_cast hnat
  have hnatural :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      hzero hupper hnonneg hle
  have hbase := hnatural.div_const (Real.log 2)
  have hbase' :
      Tendsto
        (fun n : ℕ =>
          (Real.log ((n + 1 : ℕ) : ℝ) / (n : ℝ)) / Real.log 2)
        atTop (nhds 0) := by
    simpa using hbase
  refine hbase'.congr' (Filter.Eventually.of_forall fun n => ?_)
  unfold Real.logb
  ring
end MetricCodes.Hamming
