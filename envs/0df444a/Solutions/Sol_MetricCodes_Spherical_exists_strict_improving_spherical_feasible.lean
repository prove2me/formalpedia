-- Prove2me | solution 1 for MetricCodes.Spherical.exists_strict_improving_spherical_feasible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/f4bf86b8-48b5-4ab5-817a-ec5e13e5c3f8

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_classicalThreshold_pos
import Theorems.Thm_MetricCodes_Spherical_classicalThreshold_spectral
import Theorems.Thm_MetricCodes_Spherical_sphericalImprovementSlope_gt_one
import Theorems.Thm_MetricCodes_Spherical_eventually_Gamma_improvement
import Theorems.Thm_MetricCodes_Spherical_eventually_sphericalEntropy_improvement

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ a b : ℝ, Feasible s a b ∧
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  let a₀ : ℝ := MetricCodes.classicalThreshold s
  have ha₀ : 0 < a₀ := MetricCodes.classicalThreshold_pos hs hs'
  have hgamma := eventually_Gamma_improvement ha₀
  have hentropy := eventually_sphericalEntropy_improvement ha₀
  have hc : 1 < sphericalImprovementSlope a₀ :=
    sphericalImprovementSlope_gt_one ha₀
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible s (sphericalImprovementPath a₀ b) b ∧
          MetricCodes.sphericalEntropy (sphericalImprovementPath a₀ b) -
            MetricCodes.sphericalEntropy b <
              MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hgamma' hentropy' (hb : 0 < b)
    have hbpath : b < sphericalImprovementPath a₀ b := by
      unfold sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb, hbpath, ?_⟩
      have hboundary : 2 * MetricCodes.Gamma a₀ 0 = s := by
        dsimp [a₀]
        exact classicalThreshold_spectral hs hs'
      nlinarith
    · simpa [a₀] using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨sphericalImprovementPath a₀ b, b, hb⟩
end MetricCodes.Spherical
