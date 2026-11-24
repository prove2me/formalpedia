-- Prove2me | solution 1 for GlobalTheory.holomorphic_extension_of_exp_two_pi_I_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:00:07.478615+00:00
-- url     : https://prove2.me/submissions/302f2714-7726-49e0-b6ff-daf51f57a3ca

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExtensionAcrossZeroOfExpTwoPiIBound
import Theorems.Thm_GlobalTheory_PuncturedDiscExtension_analyticAt_update_of_bdd
import Theorems.Thm_GlobalTheory_PuncturedDiscExtension_bdd_of_re_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Filter Topology Set
open GlobalTheory
open GlobalTheory.PuncturedDiscExtension
namespace GlobalTheory
theorem _root_.solution :
    ∀ (H : ℂ → ℂ) (r C : ℝ) (N : ℕ), 0 < r →
      DifferentiableOn ℂ H (Metric.ball (0 : ℂ) r \ {0}) →
      (∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 →
        ‖Complex.exp (2 * Real.pi * Complex.I * H t)‖ * ‖t‖ ^ N ≤ C) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball (0 : ℂ) r) ∧
        ∀ t ∈ Metric.ball (0 : ℂ) r, t ≠ 0 → G t = H t := by
  intro H r C N hr hH hC
  have hball : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ∈ ball (0:ℂ) r ∧ z ≠ 0 := by
    filter_upwards [nhdsWithin_le_nhds (ball_mem_nhds (0:ℂ) hr), self_mem_nhdsWithin]
      with z h1 h2
    exact ⟨h1, h2⟩
  have hHd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ H z := by
    filter_upwards [hball] with z hz
    exact hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz.1, hz.2⟩)
  set f : ℂ → ℂ := fun z => 2 * (Real.pi:ℂ) * Complex.I * H z with hf
  have hfd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ f z := by
    filter_upwards [hHd] with z hz
    exact hz.const_mul _
  have hfb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖f z‖ ≤ B := by
    set Gf : ℂ → ℂ := fun z => z ^ N * Complex.exp (f z) with hGf
    have hGd : ∀ᶠ z in 𝓝[≠] (0:ℂ), DifferentiableAt ℂ Gf z := by
      filter_upwards [hfd] with z hz
      exact (differentiableAt_id.pow N).mul hz.cexp
    have hGb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖Gf z‖ ≤ B := ⟨C, by
      filter_upwards [hball] with z hz
      have h := hC z hz.1 hz.2
      show ‖z ^ N * Complex.exp (f z)‖ ≤ C
      rw [norm_mul, norm_pow, mul_comm]
      exact h⟩
    have ha := analyticAt_update_of_bdd hGd hGb
    set G' := Function.update Gf 0 (limUnder (𝓝[≠] (0:ℂ)) Gf) with hG'
    have hG'eq : ∀ z, z ≠ 0 → G' z = Gf z := fun z hz => Function.update_of_ne hz _ _
    have hnz : ¬ ∀ᶠ z in 𝓝 (0:ℂ), G' z = 0 := by
      intro h
      have hF : ∀ᶠ z in 𝓝[≠] (0:ℂ), False := by
        filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with z h1 h2
        rw [hG'eq z h2] at h1
        exact mul_ne_zero (pow_ne_zero _ h2) (Complex.exp_ne_zero _) h1
      exact hF.exists.elim fun _ h => h
    obtain ⟨k, u, hu, hu0, hGu⟩ := (ha.exists_eventuallyEq_pow_smul_nonzero_iff).2 hnz
    have hpos : 0 < ‖u 0‖ := norm_pos_iff.2 hu0
    have huc : ContinuousAt u 0 := hu.continuousAt
    have hup : ∀ᶠ z in 𝓝 (0:ℂ), ‖u z‖ < ‖u 0‖ + 1 :=
      huc.norm.eventually (gt_mem_nhds (by linarith))
    have hlo : ∀ᶠ z in 𝓝 (0:ℂ), ‖u 0‖ / 2 < ‖u z‖ :=
      huc.norm.eventually (lt_mem_nhds (by linarith))
    have h1 : ∀ᶠ z in 𝓝 (0:ℂ), ‖z‖ < 1 := by
      filter_upwards [ball_mem_nhds (0:ℂ) one_pos] with z hz
      simpa using hz
    have hrel : ∀ᶠ z in 𝓝[≠] (0:ℂ), z ≠ 0 ∧ ‖z‖ < 1 ∧ ‖u z‖ < ‖u 0‖ + 1 ∧
        ‖u 0‖ / 2 < ‖u z‖ ∧ z ^ N * Complex.exp (f z) = z ^ k * u z := by
      filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (h1.and (hup.and (hlo.and hGu)))]
        with z hz hh
      obtain ⟨ha1, ha2, ha3, ha4⟩ := hh
      refine ⟨hz, ha1, ha2, ha3, ?_⟩
      have := hG'eq z hz
      rw [ha4, sub_zero, smul_eq_mul] at this
      exact this.symm
    rcases le_or_gt N k with hk | hk
    · refine bdd_of_re_le hfd (M := Real.log (‖u 0‖ + 1)) ?_
      filter_upwards [hrel] with z hh
      obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
      have hk' : z ^ k = z ^ N * z ^ (k - N) := by rw [← pow_add, Nat.add_sub_cancel' hk]
      rw [hk', mul_assoc] at he
      have he2 : Complex.exp (f z) = z ^ (k - N) * u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
      have hn : ‖Complex.exp (f z)‖ ≤ ‖u 0‖ + 1 := by
        rw [he2, norm_mul, norm_pow]
        have : ‖z‖ ^ (k - N) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
        nlinarith [norm_nonneg (u z)]
      rw [Complex.norm_exp] at hn
      have := Real.log_le_log (Real.exp_pos _) hn
      rwa [Real.log_exp] at this
    · obtain ⟨B, hB⟩ := bdd_of_re_le (F := fun z => -f z)
        (by filter_upwards [hfd] with z hz; exact hz.neg) (M := -Real.log (‖u 0‖ / 2)) (by
        filter_upwards [hrel] with z hh
        obtain ⟨hz, hz1, hu1, hu2, he⟩ := hh
        have hN : z ^ N = z ^ k * z ^ (N - k) := by rw [← pow_add, Nat.add_sub_cancel' hk.le]
        rw [hN, mul_assoc] at he
        have he2 : z ^ (N - k) * Complex.exp (f z) = u z := mul_left_cancel₀ (pow_ne_zero _ hz) he
        have hn : ‖u 0‖ / 2 ≤ ‖Complex.exp (f z)‖ := by
          have : ‖u z‖ ≤ ‖Complex.exp (f z)‖ := by
            rw [← he2, norm_mul, norm_pow]
            have : ‖z‖ ^ (N - k) ≤ 1 := pow_le_one₀ (norm_nonneg _) hz1.le
            nlinarith [norm_nonneg (Complex.exp (f z))]
          linarith
        rw [Complex.norm_exp] at hn
        have := Real.log_le_log (by positivity) hn
        rw [Real.log_exp] at this
        simp only [Complex.neg_re]
        linarith)
      exact ⟨B, by filter_upwards [hB] with z hz; simpa only [norm_neg] using hz⟩
  obtain ⟨B, hB⟩ := hfb
  have hHb : ∃ B : ℝ, ∀ᶠ z in 𝓝[≠] (0:ℂ), ‖H z‖ ≤ B := ⟨B / (2 * Real.pi), by
    filter_upwards [hB] with z hz
    have hf' : ‖f z‖ = 2 * Real.pi * ‖H z‖ := by
      simp only [hf, norm_mul, Complex.norm_ofNat, Complex.norm_real, Complex.norm_I,
        Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      ring
    rw [hf'] at hz
    rw [le_div_iff₀ (by positivity)]
    linarith⟩
  have haH := analyticAt_update_of_bdd hHd hHb
  refine ⟨Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H), ?_,
    fun t _ ht => Function.update_of_ne ht _ _⟩
  intro z hz
  by_cases h0 : z = 0
  · subst h0
    exact haH.differentiableAt.differentiableWithinAt
  · have hzd : DifferentiableAt ℂ H z :=
      hH.differentiableAt ((isOpen_ball.sdiff isClosed_singleton).mem_nhds ⟨hz, h0⟩)
    have heq : Function.update H 0 (limUnder (𝓝[≠] (0:ℂ)) H) =ᶠ[𝓝 z] H := by
      filter_upwards [isOpen_ne.mem_nhds h0] with w hw
      exact Function.update_of_ne hw _ _
    exact (hzd.congr_of_eventuallyEq heq).differentiableWithinAt
end GlobalTheory
