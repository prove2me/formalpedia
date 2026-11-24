-- Prove2me | solution 1 for GlobalTheory.hasSum_of_dominated_of_eq_near_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:59:02.209581+00:00
-- url     : https://prove2.me/submissions/ddf99e38-006f-40b8-98aa-12b0a7a172c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumOfDominatedOfEqNearZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} (b : ι → ℂ) (c : ι → ℝ) (n : ι → ℕ)
    (R : ℂ → ℂ) (r ε : ℝ)
    (hbc : ∀ i, ‖b i‖ ≤ c i)
    (hc : ∀ x : ℝ, 0 ≤ x → x < r → Summable (fun i => c i * x ^ n i)) (hε : 0 < ε)
    (hR : DifferentiableOn ℂ R (Metric.ball 0 r))
    (hnear : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ε → HasSum (fun i => b i * z ^ n i) (R z)) :
    ∀ z : ℂ, ‖z‖ < r → HasSum (fun i => b i * z ^ n i) (R z) := by
  intro z hz
  have hr : 0 < r := lt_of_le_of_lt (norm_nonneg z) hz
  have hbound : ∀ i (w : ℂ), ‖b i * w ^ n i‖ ≤ c i * ‖w‖ ^ n i := by
    intro i w
    rw [norm_mul, norm_pow]
    exact mul_le_mul_of_nonneg_right (hbc i) (pow_nonneg (norm_nonneg w) _)
  have hsum : ∀ w : ℂ, ‖w‖ < r → Summable (fun i => b i * w ^ n i) := by
    intro w hw
    exact Summable.of_norm_bounded (hc ‖w‖ (norm_nonneg w) hw) (fun i => hbound i w)
  let F : ℂ → ℂ := fun w => ∑' i, b i * w ^ n i
  have hFd : DifferentiableOn ℂ F (ball 0 r) := by
    intro w hw
    have hw' : ‖w‖ < r := by simpa using hw
    obtain ⟨s, hws, hsr⟩ := exists_between hw'
    have hs0 : 0 ≤ s := le_trans (norm_nonneg w) hws.le
    have hd : DifferentiableOn ℂ F (ball 0 s) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (u := fun i => c i * s ^ n i) (hc s hs0 hsr)
        (fun i => ?_) isOpen_ball (fun i v hv => ?_)
      · exact ((differentiable_const _).mul (differentiable_id.pow _)).differentiableOn
      · refine (hbound i v).trans ?_
        have hv' : ‖v‖ < s := by simpa using hv
        have hci : 0 ≤ c i := (norm_nonneg _).trans (hbc i)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg v) hv'.le _) hci
    exact (hd.differentiableAt (isOpen_ball.mem_nhds (by simpa using hws))).differentiableWithinAt
  have hFa : AnalyticOnNhd ℂ F (ball 0 r) := hFd.analyticOnNhd isOpen_ball
  have hRa : AnalyticOnNhd ℂ R (ball 0 r) := hR.analyticOnNhd isOpen_ball
  have hfreq : ∃ᶠ w in 𝓝[≠] (0:ℂ), F w = R w := by
    apply Eventually.frequently
    have h1 : ∀ᶠ w in 𝓝 (0:ℂ), w ∈ ball (0:ℂ) ε := isOpen_ball.mem_nhds (mem_ball_self hε)
    filter_upwards [nhdsWithin_le_nhds h1, self_mem_nhdsWithin] with w hw hw0
    have hw0' : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hwε : ‖w‖ < ε := by simpa using hw
    exact (hnear w hw0' hwε).tsum_eq
  have heq := hFa.eqOn_of_preconnected_of_frequently_eq hRa (convex_ball (0:ℂ) r).isPreconnected
    (mem_ball_self hr) hfreq
  have hzb : z ∈ ball (0:ℂ) r := by simpa using hz
  rw [← heq hzb]
  exact (hsum z hz).hasSum
end GlobalTheory
