-- Prove2me | solution 1 for GlobalTheory.tendstoUniformlyOn_doublingLog_of_contraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:59:27.122971+00:00
-- url     : https://prove2.me/submissions/cf99ce98-50e3-4b29-a046-e24b10465fdc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_dist_doublingLog_le_of_contraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable {ε : V → V} {r C : ℝ}
variable [CompleteSpace V]
namespace GlobalTheory
theorem _root_.solution
    (hc : ∀ x ∈ ball (0 : V) r, ‖ε x‖ ≤ 5 / 8 * ‖x‖)
    (hC0 : 0 ≤ C) (hC : ∀ x ∈ ball (0 : V) r, ‖ε x - (2 : ℂ)⁻¹ • x‖ ≤ C * ‖x‖ ^ 2) :
    TendstoUniformlyOn (fun (j : ℕ) x => (2 : ℂ) ^ j • ε^[j] x) (doublingLog ε) atTop
      (ball 0 r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro η hη
  have h0 : Tendsto (fun j : ℕ => 64 / 7 * C * r ^ 2 * (25 / 32 : ℝ) ^ j) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (r := (25 / 32 : ℝ)) (by norm_num)
      (by norm_num)).const_mul (64 / 7 * C * r ^ 2)
  filter_upwards [h0.eventually (gt_mem_nhds hη)] with j hj x hx
  rw [dist_comm]
  refine ((dist_doublingLog_le_of_contraction hc hC0 hC hx j).trans ?_).trans_lt hj
  have := (mem_ball_zero_iff.mp hx).le
  gcongr
end GlobalTheory
