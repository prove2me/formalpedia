-- Prove2me | solution 1 for MetricCodes.Hamming.eventually_binaryEntropy_improvement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:28.946406+00:00
-- url     : https://prove2.me/submissions/a4913e5e-8957-412f-a448-5f1ba344c9c5

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Hamming_differentiableAt_binaryEntropy
import Theorems.Thm_MetricCodes_Hamming_neg_mul_logb_le_binaryEntropy

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
open MetricCodes
noncomputable section
set_option autoImplicit false
open Filter Metric Topology
open scoped BigOperators InnerProductSpace Topology
open MetricCodes.Hamming
namespace MetricCodes.Hamming
theorem _root_.solution {a : ℝ}
    (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy b < MetricCodes.binaryEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.binaryEntropy (improvementPath a b)
  have hinner : DifferentiableAt ℝ (improvementPath a) 0 := by
    unfold improvementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (improvementPath a 0) := by
    simpa [improvementPath] using
      differentiableAt_binaryEntropy ha (ha'.trans (by norm_num))
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, improvementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with b hbound hlogb hb1 (hb : 0 < b)
  have houter_bound :
      MetricCodes.binaryEntropy (improvementPath a b) -
        MetricCodes.binaryEntropy a < b * M := by
    calc
      MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a =
        b * (b⁻¹ * (MetricCodes.binaryEntropy (improvementPath a b) -
          MetricCodes.binaryEntropy a)) := by
            field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_binaryEntropy hb.le hb1.le
  linarith
end MetricCodes.Hamming
