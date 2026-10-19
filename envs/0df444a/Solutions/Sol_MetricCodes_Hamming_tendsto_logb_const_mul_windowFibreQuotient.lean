-- Prove2me | solution 1 for MetricCodes.Hamming.tendsto_logb_const_mul_windowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/6b9323e5-2147-410e-8eea-15c1877e67c2

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_windowFibreQuotient_pos
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_windowFibreQuotient

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution
    {a b C : ℝ} (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C) :
    Tendsto
      (fun n : ℕ =>
        Real.logb 2 (C * windowFibreQuotient a b n) / (n : ℝ))
      atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
  have hconst :=
    tendsto_const_div_atTop_nhds_zero_nat (Real.logb 2 C)
  have hquot := tendsto_logb_windowFibreQuotient hb hba ha
  have hsum :
      Tendsto
        (fun n : ℕ =>
          Real.logb 2 C / (n : ℝ) +
            Real.logb 2 (windowFibreQuotient a b n) / (n : ℝ))
        atTop (nhds (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b)) := by
    simpa using hconst.add hquot
  refine hsum.congr' ?_
  filter_upwards [eventually_windowFibreQuotient_pos hb.le hba ha]
    with n hpos
  rw [Real.logb_mul hC.ne' hpos.ne']
  ring
end MetricCodes.Hamming
