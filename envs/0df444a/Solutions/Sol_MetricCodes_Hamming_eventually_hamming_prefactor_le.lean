-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_hamming_prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/f2b47f71-f636-4b6f-81b4-389a501bbb12

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_threshold_ceil_numerator_le_two
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos
import Theorems.Thm_MetricCodes_Hamming_eventually_topEigenvalue_uniform_gap_ceil

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ a b : ℝ}
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 1) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      ((1 - threshold n (Nat.ceil (δ * (n : ℝ)))) /
        (topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))))) ≤
        spectralPrefactor δ a b := by
  have hgap : 0 < spectralGap δ a b := spectralGap_pos h
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_topEigenvalue_uniform_gap_ceil hδ h]
      with n hn heigen
  unfold spectralPrefactor
  apply div_le_div₀ (by norm_num : (0 : ℝ) ≤ 2)
  · exact threshold_ceil_numerator_le_two hδ' hn
  · exact hgap
  · exact heigen.le
end MetricCodes.Hamming
