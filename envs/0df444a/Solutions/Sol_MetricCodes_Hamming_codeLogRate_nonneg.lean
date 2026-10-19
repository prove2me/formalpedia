-- Prove2me | solution 1 for MetricCodes.Hamming.codeLogRate_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/d1c8dab7-da35-4a5a-a8d0-00fce9b90652

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_codeNumber_pos

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution (δ : ℝ) (n : ℕ) :
    0 ≤ Real.logb 2
      (codeNumber n (Nat.ceil (δ * (n : ℝ))) : ℝ) / (n : ℝ) := by
  apply div_nonneg
  · apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
    exact_mod_cast codeNumber_pos n (Nat.ceil (δ * (n : ℝ)))
  · exact Nat.cast_nonneg n
end MetricCodes.Hamming
