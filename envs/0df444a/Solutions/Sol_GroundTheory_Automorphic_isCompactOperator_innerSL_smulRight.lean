-- Prove2me | solution 1 for GroundTheory.Automorphic.isCompactOperator_innerSL_smulRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:02:59.138849+00:00
-- url     : https://prove2.me/submissions/660fc794-bd85-4293-beaa-adb049d31f9e

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidt
import Definitions.Def_GroundTheory_AutomorphicForms_HilbertSchmidtCompact
import Theorems.Thm_GroundTheory_Automorphic_IsHilbertSchmidt_smul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open scoped ENNReal InnerProductSpace InnerProduct
open ContinuousLinearMap Filter Topology
noncomputable section
variable {𝕜 : Type*} [RCLike 𝕜]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] [CompleteSpace H]
  {K : Type*} [NormedAddCommGroup K] [InnerProductSpace 𝕜 K] [CompleteSpace K]
omit [CompleteSpace H] [CompleteSpace K]
namespace GroundTheory.Automorphic
theorem _root_.solution (e : H) (y : K) :
    IsCompactOperator ((innerSL 𝕜 e).smulRight y) := by
  refine ⟨(fun c : 𝕜 => c • y) '' Metric.closedBall 0 ‖e‖,
    (isCompact_closedBall 0 ‖e‖).image (continuous_id.smul continuous_const), ?_⟩
  refine Filter.mem_of_superset (Metric.ball_mem_nhds (0 : H) one_pos) fun x hx => ?_
  refine ⟨⟪e, x⟫_𝕜, ?_, by simp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Metric.mem_ball, dist_zero_right] at hx
  calc ‖⟪e, x⟫_𝕜‖ ≤ ‖e‖ * ‖x‖ := norm_inner_le_norm e x
    _ ≤ ‖e‖ * 1 := by gcongr
    _ = ‖e‖ := mul_one _
end GroundTheory.Automorphic
