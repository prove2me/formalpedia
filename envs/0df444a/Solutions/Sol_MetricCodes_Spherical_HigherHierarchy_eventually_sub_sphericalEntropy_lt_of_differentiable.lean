-- Prove2me | solution 1 for MetricCodes.Spherical.HigherHierarchy.eventually_sub_sphericalEntropy_lt_of_differentiable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:36.631864+00:00
-- url     : https://prove2.me/submissions/e900136c-7561-4bd4-b9a3-45ab7ff48854

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_Spherical_neg_mul_logb_le_sphericalEntropy

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
open Filter Topology
open scoped BigOperators Topology
namespace MetricCodes.Spherical.HigherHierarchy
theorem _root_.solution
    {f : ℝ → ℝ} (hf : DifferentiableAt ℝ f 0) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      f ε - MetricCodes.sphericalEntropy ε < f 0 := by
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ ε : ℝ in 𝓝[>] 0, ε⁻¹ * (f ε - f 0) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with ε hε
    simpa [smul_eq_mul] using hε
  have hloglim : Tendsto (fun ε : ℝ => -Real.logb 2 ε)
      (𝓝[>] 0) atTop := by
    simpa [Function.comp_def] using
      tendsto_neg_atBot_atTop.comp
        (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ ε : ℝ in 𝓝[>] 0, M < -Real.logb 2 ε :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with ε hbound hlogε (hε : 0 < ε)
  have hold : f ε - f 0 < ε * M := by
    calc
      f ε - f 0 = ε * (ε⁻¹ * (f ε - f 0)) := by
        field_simp [hε.ne']
      _ < ε * M := mul_lt_mul_of_pos_left hbound hε
  have hnew : ε * M < ε * (-Real.logb 2 ε) :=
    mul_lt_mul_of_pos_left hlogε hε
  have hentropy :=
    MetricCodes.Spherical.neg_mul_logb_le_sphericalEntropy hε.le
  linarith
end MetricCodes.Spherical.HigherHierarchy
