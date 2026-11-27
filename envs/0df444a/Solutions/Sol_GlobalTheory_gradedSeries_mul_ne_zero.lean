-- Prove2me | solution 1 for GlobalTheory.gradedSeries_mul_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:38:37.467846+00:00
-- url     : https://prove2.me/submissions/6a6fe4a5-d37b-499f-a206-f35f726f7b4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_GradedSeriesMulNeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Metric Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution : ∀ (ι : Type) (deg : ι → ℕ) (a : ι → ℂ) (ρ δ : ℝ) (P Q : ℂ → ℂ), 0 < δ → Differentiable ℂ P → Differentiable ℂ Q → (∀ r : ℝ, 0 < r → r < ρ → Summable fun i => ‖a i‖ * r ^ deg i) → (∀ x : ℝ, 0 < x → x < δ → (∑' i, a i * (x : ℂ) ^ deg i) * P x = Q x) → ∀ X : ℂ, ‖X‖ < ρ → Q X ≠ 0 → P X ≠ 0 := by
  intro ι deg a ρ δ P Q hδ hP hQ hsum hid X hX hQX
  have hρ : 0 < ρ := lt_of_le_of_lt (norm_nonneg _) hX
  set F : ℂ → ℂ := fun z => ∑' i, a i * z ^ deg i with hFdef
  have hFd : ∀ z ∈ ball (0 : ℂ) ρ, DifferentiableAt ℂ F z := by
    intro z hz
    rw [mem_ball_zero_iff] at hz
    have hr0 : 0 < (‖z‖ + ρ) / 2 := by positivity
    have hrρ : (‖z‖ + ρ) / 2 < ρ := by linarith
    have hD : DifferentiableOn ℂ F (ball 0 ((‖z‖ + ρ) / 2)) := by
      refine Complex.differentiableOn_tsum_of_summable_norm (hsum _ hr0 hrρ)
        (fun i => (differentiable_const _ |>.mul (differentiable_id.pow _)).differentiableOn)
        isOpen_ball (fun i w hw => ?_)
      rw [mem_ball_zero_iff] at hw
      rw [norm_mul, norm_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hw.le _) (norm_nonneg _)
    exact hD.differentiableAt (isOpen_ball.mem_nhds (by rw [mem_ball_zero_iff]; linarith))
  set G : ℂ → ℂ := fun z => F z * P z - Q z with hGdef
  have hGan : AnalyticOnNhd ℂ G (ball 0 ρ) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    exact (((hFd z hz).mul (hP z)).sub (hQ z)).differentiableWithinAt
  have hs0 : 0 < min δ ρ := lt_min hδ hρ
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) (𝓝[>] 0) (𝓝[≠] 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun x hx => by simpa using (ne_of_gt hx))
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), G z = 0 := by
    refine ht.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [Ioo_mem_nhdsGT hs0] with x hx
    have h1 := hid x hx.1 (lt_of_lt_of_le hx.2 (min_le_left _ _))
    simp only [G, F, h1, sub_self]
  have heq := hGan.eqOn_zero_of_preconnected_of_frequently_eq_zero
    (convex_ball _ _).isPreconnected (mem_ball_self hρ) hfreq
  have hGX : G X = 0 := heq (by rw [mem_ball_zero_iff]; exact hX)
  intro hPX
  apply hQX
  simp only [G, hPX, mul_zero, zero_sub, neg_eq_zero] at hGX
  exact hGX
end GlobalTheory
