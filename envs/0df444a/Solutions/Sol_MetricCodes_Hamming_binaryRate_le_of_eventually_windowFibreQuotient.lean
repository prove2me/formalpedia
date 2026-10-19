-- Prove2me | solution 1 for MetricCodes.Hamming.binaryRate_le_of_eventually_windowFibreQuotient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/349d3aa7-c3b4-48a5-8009-1af12a10fb87

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_codeNumber_pos
import Theorems.Thm_MetricCodes_Hamming_tendsto_logb_const_mul_windowFibreQuotient
import Theorems.Thm_MetricCodes_Hamming_binaryRate_le_of_eventually

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
    {δ a b C : ℝ}
    (hb : 0 < b) (hba : b < a)
    (ha : a ≤ (1 : ℝ) / 2) (hC : 0 < C)
    (hbound : ∀ᶠ n : ℕ in atTop,
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) ≤
        C * windowFibreQuotient a b n) :
    binaryRate δ ≤ MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b := by
  refine binaryRate_le_of_eventually
    (tendsto_logb_const_mul_windowFibreQuotient hb hba ha hC) ?_
  filter_upwards [hbound, eventually_gt_atTop (0 : ℕ)]
    with n hncode hn
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcode :
      0 < (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) := by
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  apply (div_le_div_iff_of_pos_right hnreal).2
  exact Real.logb_le_logb_of_le
    (by norm_num : (1 : ℝ) < 2) hcode hncode
end MetricCodes.Hamming
