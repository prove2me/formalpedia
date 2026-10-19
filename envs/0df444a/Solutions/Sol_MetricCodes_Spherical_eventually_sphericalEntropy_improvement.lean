-- Prove2me | solution 1 for MetricCodes.Spherical.eventually_sphericalEntropy_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:32.365393+00:00
-- url     : https://prove2.me/submissions/023f75ca-f14c-49f0-834a-8e3ea5348ca0

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_hasDerivAt_sphericalEntropy
import Theorems.Thm_MetricCodes_Spherical_neg_mul_logb_le_sphericalEntropy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
open MetricCodes.Spherical
noncomputable section
open Filter Topology
open scoped Topology
namespace MetricCodes.Spherical
theorem _root_.solution {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.sphericalEntropy (sphericalImprovementPath a b)
  have hinner : DifferentiableAt ℝ (sphericalImprovementPath a) 0 := by
    unfold sphericalImprovementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (sphericalImprovementPath a 0) := by
    simpa [sphericalImprovementPath] using
      (hasDerivAt_sphericalEntropy ha).differentiableAt
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.sphericalEntropy
          (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, sphericalImprovementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with b hbound hlogb (hb : 0 < b)
  have houter_bound :
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy a < b * M := by
    calc
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
          MetricCodes.sphericalEntropy a =
        b * (b⁻¹ *
          (MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a)) := by
          field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_sphericalEntropy hb.le
  linarith
end MetricCodes.Spherical
