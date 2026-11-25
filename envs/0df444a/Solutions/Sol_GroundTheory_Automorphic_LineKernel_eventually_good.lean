-- Prove2me | solution 1 for GroundTheory.Automorphic.LineKernel.eventually_good
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:09:41.684059+00:00
-- url     : https://prove2.me/submissions/ee7f90a1-6ce9-40f8-bfe8-bd150e15cf61

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineBounds
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLineLimit
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavinLine
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_weight_pos
import Theorems.Thm_GroundTheory_Automorphic_LineKernel_eventually_norm_iteratedDeriv_rem_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open MeasureTheory Set Filter Topology Real Function ContinuousLinearMap
open scoped ContDiff Convolution Pointwise FourierTransform
set_option linter.unusedSectionVars false
noncomputable section
open GroundTheory.Automorphic.LineKernel
namespace GroundTheory.Automorphic.LineKernel
theorem _root_.solution (M : ℕ → ℝ) {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∀ᶠ x in atTop, Good M ε j x := by
  have hr := radii_pos hε j
  refine (eventually_gt_atTop 0).and (((eventually_all_finset _).2 fun p _ => ?_).and
    (((eventually_all_finset _).2 fun q _ => ?_).and ?_))
  · have hc : 0 < (1 / 2 : ℝ) ^ (j + 1) * weight M p := by
      have := weight_pos M p; positivity
    filter_upwards [eventually_ge_atTop (weight M (p - 1) / ((1 / 2) ^ (j + 1) * weight M p)),
      eventually_gt_atTop 0] with x hx hx0 _
    rw [inv_mul_le_iff₀ hx0]
    rw [div_le_iff₀ hc] at hx; linarith
  · exact eventually_norm_iteratedDeriv_rem_le hr q (by positivity)
  · have ht : Tendsto (fun x : ℝ => exp (-x * radii ε j)) atTop (𝓝 0) := by
      have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_mul_const hr)
      refine this.congr fun x => ?_
      simp [neg_mul]
    exact ht.eventually (ge_mem_nhds (by positivity))
end GroundTheory.Automorphic.LineKernel
