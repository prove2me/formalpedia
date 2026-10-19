-- Prove2me | solution 1 for MetricCodes.Hamming.threshold_ceil_numerator_le_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/76a13727-1d88-41e5-af0b-43853991fe93

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_ceil_distance_le_dimension

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ : ℝ}
    (hδ : δ ≤ 1) {n : ℕ} (hn : 0 < n) :
    1 - threshold n (Nat.ceil (δ * (n : ℝ))) ≤ 2 := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdreal : (Nat.ceil (δ * (n : ℝ)) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast ceil_distance_le_dimension hδ n
  have hquot :
      2 * (Nat.ceil (δ * (n : ℝ)) : ℝ) / (n : ℝ) ≤ 2 := by
    apply (div_le_iff₀ hnreal).2
    exact mul_le_mul_of_nonneg_left hdreal (by norm_num)
  unfold threshold
  linarith
end MetricCodes.Hamming
