-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.exists_sliceCost_endpoint_improvement_of_smallEntropy
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:37.685478+00:00
-- url     : https://prove2.me/submissions/963d9a7d-f7ac-4cc5-9bc3-d1aa0d2b0d1b

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_tendsto_sphericalEntropy_sq_div
import Theorems.Thm_MetricCodes_Spherical_HigherHierarchy_sliceCost_sub_zero_le_neg_linear

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
set_option autoImplicit false
open MetricCodes
open MetricCodes.Spherical
open MetricCodes.Spherical.HigherHierarchy
noncomputable section
open Set Filter Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {κ : ℝ → ℝ} {s : ℝ} (hs : 0 < s) (hs' : s < 1)
    (hzero : κ 0 = 0)
    (hsmall : ∀ᶠ t : ℝ in 𝓝[>] 0,
      κ t ≤ MetricCodes.sphericalEntropy (t ^ 2)) :
    ∃ u ∈ Set.Icc (0 : ℝ) s,
      κ u + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s u <
        κ 0 + MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 := by
  have hbase : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hquarter : 0 < 1 / (4 * Real.log 2) := by positivity
  have hentropy : ∀ᶠ t : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (t ^ 2) / t < 1 / (4 * Real.log 2) :=
    tendsto_sphericalEntropy_sq_div.eventually (Iio_mem_nhds hquarter)
  have hupper : ∀ᶠ t : ℝ in 𝓝[>] 0, t < s :=
    (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hs)
  have hpositive : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t :=
    self_mem_nhdsWithin
  obtain ⟨t, htpos, htupper, hκ, hent⟩ :=
    (hpositive.and (hupper.and (hsmall.and hentropy))).exists
  refine ⟨t, ⟨htpos.le, htupper.le⟩, ?_⟩
  have hent' : MetricCodes.sphericalEntropy (t ^ 2) <
      t / (4 * Real.log 2) := by
    calc
      MetricCodes.sphericalEntropy (t ^ 2) <
          (1 / (4 * Real.log 2)) * t := (div_lt_iff₀ htpos).mp hent
      _ = t / (4 * Real.log 2) := by ring
  have hcost := sliceCost_sub_zero_le_neg_linear hs' (lt_trans htupper hs')
  have hcost' :
      MetricCodes.Spherical.SidelnikovLocalization.sliceCost s t -
          MetricCodes.Spherical.SidelnikovLocalization.sliceCost s 0 ≤
        -(t / (2 * Real.log 2)) := by
    simpa only [neg_div] using hcost
  have hlinear : t / (4 * Real.log 2) < t / (2 * Real.log 2) := by
    exact (div_lt_div_iff_of_pos_left htpos (by positivity) (by positivity)).2
      (by nlinarith)
  rw [hzero]
  linarith
end MetricCodes.Spherical.HigherHierarchy
