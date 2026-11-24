-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.DigammaLimit.tendsto_deriv_GammaSeq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:00:05.022221+00:00
-- url     : https://prove2.me/submissions/bc968600-5c14-4682-9872-92429126ce2b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaTendstoLogSubHarmonic
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_norm_GammaSeq_le
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_ne_neg_natCast_of_re_pos
import Theorems.Thm_GlobalTheory_CompanionTheory_DigammaLimit_differentiableAt_GammaSeq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Metric Set
open scoped Nat Real
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaLimit
namespace GlobalTheory.CompanionTheory.DigammaLimit
theorem _root_.solution {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun n : ℕ => deriv (fun w => GammaSeq w n) z) atTop (𝓝 (deriv Gamma z)) := by
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = z.re / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  obtain ⟨U, hU_def⟩ : ∃ U : Set ℂ, U = {w : ℂ | 0 < w.re} := ⟨_, rfl⟩
  have hUo : IsOpen U := by
    rw [hU_def]
    exact isOpen_lt continuous_const Complex.continuous_re
  have hre : ∀ w ∈ closedBall z r, z.re / 2 ≤ w.re ∧ w.re ≤ 3 * z.re / 2 := by
    intro w hw
    have h1 : ‖w - z‖ ≤ r := by rwa [mem_closedBall, dist_eq_norm] at hw
    have h2 := Complex.abs_re_le_norm (w - z)
    have h3 : |w.re - z.re| ≤ r := by
      have := h2.trans h1
      simpa only [sub_re] using this
    rw [abs_le] at h3
    constructor <;> linarith [h3.1, h3.2]
  have hsub : closedBall z r ⊆ U := fun w hw => by
    have := (hre w hw).1
    rw [hU_def]
    show 0 < w.re
    linarith
  have hGd : DifferentiableOn ℂ Gamma U := fun w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_Gamma w (ne_neg_natCast_of_re_pos hw)).differentiableWithinAt
  have hFd : ∀ n : ℕ, n ≠ 0 → DifferentiableOn ℂ (fun w => GammaSeq w n) U := fun n hn w hw => by
    rw [hU_def] at hw
    exact (differentiableAt_GammaSeq hw hn).differentiableWithinAt
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ Icc (z.re / 2) (3 * z.re / 2), ‖Real.Gamma x‖ ≤ M := by
    refine isCompact_Icc.exists_bound_of_continuousOn fun x hx => ?_
    have hx0 : 0 < x := by linarith [hx.1]
    refine (Real.differentiableAt_Gamma fun m h => ?_).continuousAt.continuousWithinAt
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have hbd : ∀ n : ℕ, n ≠ 0 → ∀ w ∈ closedBall z r, ‖GammaSeq w n‖ ≤ M := by
    intro n hn w hw
    have h1 := hre w hw
    have h0 : 0 < w.re := by linarith [h1.1]
    exact (norm_GammaSeq_le h0 hn).trans ((le_abs_self _).trans (hM _ ⟨h1.1, h1.2⟩))
  have hc : ∀ θ, circleMap z r θ ∈ closedBall z r := fun θ =>
    sphere_subset_closedBall (circleMap_mem_sphere z hr.le θ)
  have key : Tendsto (fun n : ℕ => ∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • GammaSeq w n) atTop
      (𝓝 (∮ w in C(z, r), ((w - z) ^ 2)⁻¹ • Gamma w)) := by
    simp only [circleIntegral]
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun _ => r * ((r ^ 2)⁻¹ * M)) ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [eventually_ne_atTop 0] with n hn
      apply Continuous.aestronglyMeasurable
      have hcont : Continuous fun θ : ℝ => GammaSeq (circleMap z r θ) n :=
        (hFd n hn).continuousOn.comp_continuous (continuous_circleMap z r)
          (fun θ => hsub (hc θ))
      have h0 : ∀ θ, (circleMap z r θ - z) ^ 2 ≠ 0 := fun θ =>
        pow_ne_zero 2 (sub_ne_zero.2 (circleMap_ne_center hr.ne'))
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 r).mul continuous_const).smul
        (((((continuous_circleMap z r).sub continuous_const).pow 2).inv₀ h0).smul hcont)
    · filter_upwards [eventually_ne_atTop 0] with n hn
      refine Eventually.of_forall fun θ _ => ?_
      simp only [deriv_circleMap, circleMap_sub_center, norm_smul, norm_mul, norm_circleMap_zero,
        Complex.norm_I, norm_inv, norm_pow, abs_of_pos hr, mul_one]
      gcongr
      exact hbd n hn _ (hc θ)
    · refine Eventually.of_forall fun θ _ => ?_
      exact ((GammaSeq_tendsto_Gamma _).const_smul _).const_smul _
  have h2 := key.const_smul ((2 * π * I : ℂ)⁻¹)
  have e : cderiv r Gamma z = deriv Gamma z := cderiv_eq_deriv hUo hGd hr hsub
  rw [← e]
  refine Tendsto.congr' ?_ h2
  filter_upwards [eventually_ne_atTop 0] with n hn
  exact cderiv_eq_deriv hUo (hFd n hn) hr hsub
end GlobalTheory.CompanionTheory.DigammaLimit
