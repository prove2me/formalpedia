-- Prove2me | solution 1 for MetricCodes.Hamming.exists_strict_improving_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/c1ee5149-162d-40b6-933f-1d5b535c95a6

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_classicalParameter_lt_half
import Theorems.Thm_MetricCodes_Hamming_classicalParameter_pos
import Theorems.Thm_MetricCodes_Hamming_hammingGamma_classicalParameter
import Theorems.Thm_MetricCodes_Hamming_improvementSlope_gt_one
import Theorems.Thm_MetricCodes_Hamming_tendsto_improvementPath_zero
import Theorems.Thm_MetricCodes_Hamming_eventually_hammingGamma_improvement
import Theorems.Thm_MetricCodes_Hamming_eventually_binaryEntropy_improvement

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
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2) :
    ∃ a b : ℝ, Feasible δ a b ∧
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy b < classicalRate δ := by
  let a₀ : ℝ := classicalParameter δ
  have ha₀ : 0 < a₀ := classicalParameter_pos hδ hδ'
  have ha₀half : a₀ < (1 : ℝ) / 2 :=
    classicalParameter_lt_half hδ hδ'
  have hgamma := eventually_hammingGamma_improvement ha₀ ha₀half
  have hentropy := eventually_binaryEntropy_improvement ha₀ ha₀half
  have hhalf :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        improvementPath a₀ b < (1 : ℝ) / 2 :=
    (tendsto_improvementPath_zero a₀).eventually
      (gt_mem_nhds ha₀half)
  have hc : 1 < improvementSlope a₀ :=
    improvementSlope_gt_one ha₀half
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible δ (improvementPath a₀ b) b ∧
          MetricCodes.binaryEntropy (improvementPath a₀ b) -
            MetricCodes.binaryEntropy b < classicalRate δ := by
    filter_upwards [hgamma, hentropy, hhalf, self_mem_nhdsWithin]
      with b hgamma' hentropy' hhalf' (hb : 0 < b)
    have hbpath : b < improvementPath a₀ b := by
      unfold improvementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb.le, hbpath, hhalf'.le, ?_⟩
      have hboundary : MetricCodes.hammingGamma a₀ 0 = 1 - 2 * δ := by
        dsimp [a₀]
        exact hammingGamma_classicalParameter hδ hδ'
      rwa [hboundary] at hgamma'
    · simpa [classicalRate, a₀] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨improvementPath a₀ b, b, hb⟩
end MetricCodes.Hamming
