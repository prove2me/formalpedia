-- Prove2me | solution 1 for GlobalTheory.SCV.hasSum_taylorSeries_ball
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:32:59.525496+00:00
-- url     : https://prove2.me/submissions/59168ad3-fa1c-4702-b546-836e26692ba1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Theorems.Thm_GlobalTheory_SCV_iteratedDeriv_line

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter
open scoped Topology ContDiff Nat
open GlobalTheory GlobalTheory.SCV
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace GlobalTheory.SCV
theorem _root_.solution {f : E → V} {c : E} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball c R)) {y : E} (hy : ‖y‖ < R) :
    HasSum (fun n : ℕ => (n ! : ℂ)⁻¹ • iteratedFDeriv ℂ n f c (fun _ => y)) (f (c + y)) := by
  have hy0 := norm_nonneg y
  have hR : 0 < R := hy0.trans_lt hy
  have hp : 0 < R + ‖y‖ := by linarith
  have hg : DifferentiableOn ℂ (fun t : ℂ => f (c + t • y)) (ball 0 (2 * R / (R + ‖y‖))) := by
    refine hf.comp (by fun_prop) fun t ht => ?_
    rw [mem_ball_zero_iff, lt_div_iff₀ hp] at ht
    rw [mem_ball_iff_norm, add_sub_cancel_left, norm_smul]
    have := norm_nonneg t
    nlinarith [mul_nonneg this (sub_nonneg.mpr hy.le)]
  have h1 : (1 : ℂ) ∈ ball (0 : ℂ) (2 * R / (R + ‖y‖)) := by
    rw [mem_ball_zero_iff, norm_one, lt_div_iff₀ hp]
    linarith
  have key := Complex.hasSum_taylorSeries_on_ball hg h1
  simpa only [iteratedDeriv_line isOpen_ball hf (mem_ball_self hR), sub_zero, one_pow, one_smul]
    using key
end GlobalTheory.SCV
