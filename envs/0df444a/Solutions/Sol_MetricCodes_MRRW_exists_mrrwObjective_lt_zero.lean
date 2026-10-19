-- Prove2me | solution 1 for MetricCodes.MRRW.exists_mrrwObjective_lt_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:30.949776+00:00
-- url     : https://prove2.me/submissions/d49eaf04-6aec-44a4-983c-8362ce3ca1db

import Definitions.Def_SpherePacking
import Definitions.Def_MetricCodes
import Theorems.Thm_MetricCodes_MRRW_lowerEndpointDerivative_pos
import Theorems.Thm_MetricCodes_MRRW_hasDerivAt_mrrwObjective_zero

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
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 - 2 * δ ∧
      MetricCodes.Johnson.mrrwObjective δ r <
        MetricCodes.Johnson.mrrwObjective δ 0 := by
  have hderivative := lowerEndpointDerivative_pos hδ hhalf
  have hslope :=
    (hasDerivAt_mrrwObjective_zero hδ hhalf).tendsto_slope_zero_right
  have hnegative :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        r⁻¹ *
          (MetricCodes.Johnson.mrrwObjective δ r -
            MetricCodes.Johnson.mrrwObjective δ 0) < 0 := by
    have h :=
      hslope.eventually
        (gt_mem_nhds (by linarith :
          -lowerEndpointDerivative δ < 0))
    filter_upwards [h] with r hr
    simpa [smul_eq_mul] using hr
  have hupper :
      ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 - 2 * δ :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - 2 * δ))
  have hwitness :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        0 < r ∧ r < 1 - 2 * δ ∧
          MetricCodes.Johnson.mrrwObjective δ r <
            MetricCodes.Johnson.mrrwObjective δ 0 := by
    filter_upwards [hnegative, hupper, self_mem_nhdsWithin]
      with r hquotient hrupper (hr : 0 < r)
    refine ⟨hr, hrupper, ?_⟩
    apply sub_neg.mp
    calc
      MetricCodes.Johnson.mrrwObjective δ r -
          MetricCodes.Johnson.mrrwObjective δ 0 =
        r *
          (r⁻¹ *
            (MetricCodes.Johnson.mrrwObjective δ r -
              MetricCodes.Johnson.mrrwObjective δ 0)) := by
          field_simp [hr.ne']
      _ < 0 := mul_neg_of_pos_of_neg hr hquotient
  exact hwitness.exists
end MetricCodes.MRRW
