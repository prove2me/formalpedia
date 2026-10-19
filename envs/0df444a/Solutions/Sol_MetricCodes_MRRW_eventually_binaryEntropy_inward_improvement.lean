-- Prove2me | solution 1 for MetricCodes.MRRW.eventually_binaryEntropy_inward_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/db2ec06d-2563-4b5e-94ff-514e664d3817

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_differentiableAt_binaryEntropy
import Theorems.Thm_MetricCodes_Hamming_neg_mul_logb_le_binaryEntropy

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
    {a : ℝ} (ha : 0 < a) (ha' : a < 1) (C : ℝ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        MetricCodes.binaryEntropy e := by
  let f : ℝ → ℝ := fun e =>
    MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)
  have hinner :
      DifferentiableAt ℝ (fun e : ℝ => a - C * e) 0 := by
    fun_prop
  have houter : DifferentiableAt ℝ MetricCodes.binaryEntropy a :=
    MetricCodes.Hamming.differentiableAt_binaryEntropy ha ha'
  have houter0 :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (a - C * (0 : ℝ)) := by
    simpa using houter
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp [f]
    exact (houter0.comp 0 hinner).const_sub (MetricCodes.binaryEntropy a)
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ e : ℝ in 𝓝[>] 0,
        e⁻¹ *
          (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with e he
    simpa [f, smul_eq_mul] using he
  have hloglim :
      Tendsto (fun e : ℝ => -Real.logb 2 e) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ e : ℝ in 𝓝[>] 0, M < -Real.logb 2 e :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with e hbound hlog' heone (he : 0 < e)
  have houter_bound :
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        e * M := by
    calc
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) =
          e * (e⁻¹ *
            (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e))) := by
            field_simp [he.ne']
      _ < e * M := mul_lt_mul_of_pos_left hbound he
  have hsingular : e * M < e * (-Real.logb 2 e) :=
    mul_lt_mul_of_pos_left hlog' he
  have hentropy :=
    MetricCodes.Hamming.neg_mul_logb_le_binaryEntropy he.le heone.le
  linarith
end MetricCodes.MRRW
