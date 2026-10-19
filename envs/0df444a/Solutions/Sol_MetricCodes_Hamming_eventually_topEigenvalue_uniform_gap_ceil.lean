-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_topEigenvalue_uniform_gap_ceil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/296047af-2cab-4ce7-9f09-8f21126e4f64

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_eventually_topEigenvalue_gt
import Theorems.Thm_MetricCodes_Hamming_tendsto_threshold_ceil
import Theorems.Thm_MetricCodes_Hamming_spectralGap_pos

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
    (hδ : 0 ≤ δ) (h : Feasible δ a b) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap δ a b <
        topEigenvalue n (transverseDegree b n)
          (longitudinalDegree a n) -
            threshold n (Nat.ceil (δ * (n : ℝ))) := by
  obtain ⟨hb, hba, ha, hgamma⟩ := h
  have hgap : 0 < spectralGap δ a b :=
    spectralGap_pos ⟨hb, hba, ha, hgamma⟩
  have hstrict :
      1 - 2 * δ + 2 * spectralGap δ a b <
        MetricCodes.hammingGamma a b := by
    unfold spectralGap
    linarith
  have heigen :=
    eventually_topEigenvalue_gt hb hba ha hstrict
  have hthreshold :
      ∀ᶠ n : ℕ in atTop,
        threshold n (Nat.ceil (δ * (n : ℝ))) <
          1 - 2 * δ + spectralGap δ a b :=
    (tendsto_threshold_ceil hδ).eventually
      (gt_mem_nhds (by linarith))
  filter_upwards [heigen, hthreshold] with n he hn
  linarith
end MetricCodes.Hamming
