-- Prove2me | solution 1 for MetricCodes.Hamming.exists_positive_feasible_of_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:29.660979+00:00
-- url     : https://prove2.me/submissions/c90f1bc4-0633-47ac-a6fa-bcff17f95d7e

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {δ a : ℝ}
    (h : Feasible δ a 0) :
    ∃ b : ℝ, 0 < b ∧ Feasible δ a b := by
  obtain ⟨_, ha, hahalf, hgamma⟩ := h
  have hcontinuous :
      Continuous (fun b : ℝ => MetricCodes.hammingGamma a b) := by
    unfold MetricCodes.hammingGamma
    fun_prop
  have hnear :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        1 - 2 * δ < MetricCodes.hammingGamma a b := by
    exact nhdsWithin_le_nhds
      ((hcontinuous.continuousAt (x := (0 : ℝ))).tendsto.eventually
        (lt_mem_nhds hgamma))
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < a :=
    nhdsWithin_le_nhds (gt_mem_nhds ha)
  have htotal :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < b ∧ Feasible δ a b := by
    filter_upwards [hnear, hsmall, self_mem_nhdsWithin]
      with b hgamma' hba (hb : 0 < b)
    exact ⟨hb, hb.le, hba, hahalf, hgamma'⟩
  exact htotal.exists
end MetricCodes.Hamming
