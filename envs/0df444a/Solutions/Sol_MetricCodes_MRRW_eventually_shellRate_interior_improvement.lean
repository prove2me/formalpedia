-- Prove2me | solution 1 for MetricCodes.MRRW.eventually_shellRate_interior_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/5c810ad3-e5eb-4123-8444-3c13330387de

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_rankPenalty_interior
import Theorems.Thm_MetricCodes_MRRW_tendsto_interiorWeight_zero
import Theorems.Thm_MetricCodes_MRRW_eventually_binaryEntropy_inward_improvement

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.MRRW
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped Topology
namespace MetricCodes.MRRW
theorem _root_.solution
    {a u : ℝ} (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hentropy := eventually_binaryEntropy_inward_improvement
    ha (ha'.trans (by norm_num)) (interiorSlope a u)
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds ha)
  have hless :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < 1 :=
    hweight.eventually
      (gt_mem_nhds (ha'.trans (by norm_num : (1 : ℝ) / 2 < 1)))
  filter_upwards [hentropy, hpositive, hless]
    with e he hpos hlt
  rw [MetricCodes.Johnson.shellRate, rankPenalty_interior hpos hlt,
    MetricCodes.Johnson.shellRate_zero_fibre]
  change
    1 - MetricCodes.binaryEntropy (a - interiorSlope a u * e) +
        MetricCodes.binaryEntropy u - MetricCodes.binaryEntropy e <
      1 - MetricCodes.binaryEntropy a + MetricCodes.binaryEntropy u
  linarith
end MetricCodes.MRRW
