-- Prove2me | solution 1 for MasulloRH.regularized_spectral_analytic
-- status  : ACCEPTED   (prove)
-- author  : @Ismael Correa
-- created : 2026-11-20T22:07:54.885167+00:00
-- url     : https://prove2.me/submissions/6891d840-8ca2-4961-8a22-e0d3ee4341ab

import Definitions.Def_MasulloRH_RegularizedTrace
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.CauchyIntegral

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff
open MasulloRH

/-- Elementary real inequality behind the uniform bound. -/
lemma masullo_real_key (P1 P2 g δ B : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (h1 : δ ≤ P1) (h2 : |g| - B ≤ P1) (h3 : 3 / 2 ≤ P2) (h4 : |g| ≤ P2) :
    1 + g ^ 2 ≤ (4 + (1 + (2 * B + 2) ^ 2) / δ) * (P1 * P2) := by
  have hP1 : 0 < P1 := lt_of_lt_of_le hδ h1
  have hP2 : 0 < P2 := by linarith
  have hPP : 0 ≤ P1 * P2 := by positivity
  have hg2 : g ^ 2 = |g| ^ 2 := (sq_abs g).symm
  have hga : 0 ≤ |g| := abs_nonneg g
  set Q : ℝ := 1 + (2 * B + 2) ^ 2 with hQ
  have hQpos : 0 ≤ Q := by positivity
  rw [add_mul]
  rcases le_or_gt (2 * B + 2) |g| with hg | hg
  · -- large height
    have hA : |g| / 2 ≤ P1 := by linarith
    have hprod : |g| / 2 * |g| ≤ P1 * P2 :=
      mul_le_mul hA h4 hga hP1.le
    have hextra : 0 ≤ Q / δ * (P1 * P2) := by positivity
    have hge1 : 1 ≤ |g| ^ 2 := by nlinarith
    nlinarith
  · -- bounded height
    have hprod : δ * (3 / 2) ≤ P1 * P2 := mul_le_mul h1 h3 (by norm_num) hP1.le
    have hgq : 1 + g ^ 2 ≤ Q := by
      rw [hg2, hQ]
      have : |g| ^ 2 ≤ (2 * B + 2) ^ 2 := by
        exact pow_le_pow_left₀ hga hg.le 2
      linarith
    have hx : Q / δ * (δ * (3 / 2)) = Q * (3 / 2) := by
      field_simp
    have hy : Q / δ * (δ * (3 / 2)) ≤ Q / δ * (P1 * P2) :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    nlinarith

/-- Uniform domination of the resolvent terms on a vertical-strip-type region. -/
lemma masullo_term_bound (α δ B A : ℝ) (hδ : 0 < δ) (hB : 0 ≤ B)
    (w : ℂ) (hw : 1 / 2 + α + δ ≤ w.re) (hwim : |w.im| ≤ B)
    (hwA : ‖(5 / 2 : ℂ) - w‖ ≤ A) (ρ : ZetaZerosInTraceStrip α) :
    ‖zeroResolventTerm α w ρ‖ ≤
      (A * (4 + (1 + (2 * B + 2) ^ 2) / δ)) * zeroDecayWeight α ρ := by
  obtain ⟨r, hz, hr0, hr1, hstrip⟩ := ρ
  simp only [zeroResolventTerm, zeroDecayWeight]
  set m : ℕ := analyticOrderNatAt riemannZeta r
  have hrre : r.re < 1 / 2 + α := by
    have := (abs_lt.mp hstrip).2; linarith
  -- basic norm bounds
  have hP1a : δ ≤ ‖w - r‖ := by
    have h := Complex.abs_re_le_norm (w - r)
    rw [Complex.sub_re] at h
    have : δ ≤ |w.re - r.re| := by rw [abs_of_pos (by linarith)]; linarith
    linarith
  have hP1b : |r.im| - B ≤ ‖w - r‖ := by
    have h := Complex.abs_im_le_norm (w - r)
    rw [Complex.sub_im] at h
    have : |r.im| ≤ |w.im - r.im| + |w.im| := by
      have := abs_sub_abs_le_abs_sub w.im r.im
      have := abs_sub_comm w.im r.im
      have := abs_sub (r.im) (w.im)
      linarith [abs_sub_abs_le_abs_sub r.im w.im, abs_sub_comm r.im w.im]
    linarith
  have hP2a : 3 / 2 ≤ ‖(5 / 2 : ℂ) - r‖ := by
    have h := Complex.abs_re_le_norm ((5 / 2 : ℂ) - r)
    have hre : ((5 / 2 : ℂ) - r).re = 5 / 2 - r.re := by simp
    rw [hre] at h
    have : 3 / 2 ≤ |5 / 2 - r.re| := by rw [abs_of_pos (by linarith)]; linarith
    linarith
  have hP2b : |r.im| ≤ ‖(5 / 2 : ℂ) - r‖ := by
    have h := Complex.abs_im_le_norm ((5 / 2 : ℂ) - r)
    have him : ((5 / 2 : ℂ) - r).im = - r.im := by simp
    rw [him, abs_neg] at h
    exact h
  have hkey := masullo_real_key ‖w - r‖ ‖(5 / 2 : ℂ) - r‖ r.im δ B hδ hB hP1a hP1b hP2a hP2b
  have hne1 : w - r ≠ 0 := by
    intro h; rw [h, norm_zero] at hP1a; linarith
  have hne2 : (5 / 2 : ℂ) - r ≠ 0 := by
    intro h; rw [h, norm_zero] at hP2a; linarith
  have hid : (m : ℂ) * (1 / (w - r) - 1 / ((5 / 2 : ℂ) - r)) =
      (m : ℂ) * ((5 / 2 : ℂ) - w) / ((w - r) * ((5 / 2 : ℂ) - r)) := by
    rw [div_sub_div _ _ hne1 hne2]
    ring
  rw [hid, norm_div, norm_mul, norm_mul, Complex.norm_natCast]
  set P := ‖w - r‖ * ‖(5 / 2 : ℂ) - r‖ with hP
  have hPpos : 0 < P := by
    rw [hP]; exact mul_pos (norm_pos_iff.mpr hne1) (norm_pos_iff.mpr hne2)
  set M : ℝ := 4 + (1 + (2 * B + 2) ^ 2) / δ
  have hden : 0 < 1 + r.im ^ 2 := by positivity
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hA0 : 0 ≤ A := le_trans (norm_nonneg _) hwA
  rw [div_le_iff₀ hPpos]
  -- goal: m * ‖5/2 - w‖ ≤ A * M * (m / (1 + im^2)) * P
  have h1 : (m : ℝ) * ‖(5 / 2 : ℂ) - w‖ ≤ m * A := mul_le_mul_of_nonneg_left hwA hm
  have h2 : (m : ℝ) * A * (1 + r.im ^ 2) ≤ m * A * (M * P) :=
    mul_le_mul_of_nonneg_left hkey (mul_nonneg hm hA0)
  have h3 : A * M * ((m : ℝ) / (1 + r.im ^ 2)) * P = (m * A * (M * P)) / (1 + r.im ^ 2) := by
    field_simp
  rw [h3, le_div_iff₀ hden]
  nlinarith [mul_le_mul_of_nonneg_right h1 hden.le]

theorem solution (α : ℝ) (hα : 0 < α)
    (hαsmall : α < 1 / 2) (s : ℂ) (hs : 1 / 2 + α < s.re) :
    Summable (zeroResolventTerm α s) ∧ AnalyticAt ℂ (regularizedSpectral α) s := by
  have hsum := weighted_zero_summability α hα
  set δ : ℝ := (s.re - (1 / 2 + α)) / 2 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  set B : ℝ := |s.im| + δ
  have hB : 0 ≤ B := by positivity
  set A : ℝ := ‖(5 / 2 : ℂ) - s‖ + δ
  set C : ℝ := A * (4 + (1 + (2 * B + 2) ^ 2) / δ)
  set U : Set ℂ := Metric.ball s δ
  have hU : IsOpen U := Metric.isOpen_ball
  have hbound : ∀ (ρ : ZetaZerosInTraceStrip α) (w : ℂ), w ∈ U →
      ‖zeroResolventTerm α w ρ‖ ≤ C * zeroDecayWeight α ρ := by
    intro ρ w hw
    have hd : ‖w - s‖ < δ := by simpa [U, dist_eq_norm] using hw
    have hre : 1 / 2 + α + δ ≤ w.re := by
      have h := Complex.abs_re_le_norm (w - s)
      rw [Complex.sub_re] at h
      have := (abs_le.mp (le_trans h hd.le)).1
      rw [hδdef] at this ⊢; linarith
    have him : |w.im| ≤ B := by
      have h := Complex.abs_im_le_norm (w - s)
      rw [Complex.sub_im] at h
      have := abs_sub_abs_le_abs_sub w.im s.im
      linarith
    have hA : ‖(5 / 2 : ℂ) - w‖ ≤ A := by
      have : (5 / 2 : ℂ) - w = ((5 / 2 : ℂ) - s) - (w - s) := by ring
      rw [this]
      exact le_trans (norm_sub_le _ _) (by linarith)
    exact masullo_term_bound α δ B A hδ hB w hre him hA ρ
  have hsumC : Summable (fun ρ => C * zeroDecayWeight α ρ) := hsum.mul_left C
  have hsU : s ∈ U := Metric.mem_ball_self hδ
  refine ⟨?_, ?_⟩
  · exact Summable.of_norm_bounded hsumC (fun ρ => hbound ρ s hsU)
  · have hdiff : ∀ ρ : ZetaZerosInTraceStrip α,
        DifferentiableOn ℂ (fun w => zeroResolventTerm α w ρ) U := by
      intro ρ w hw
      have hd : ‖w - s‖ < δ := by simpa [U, dist_eq_norm] using hw
      have hne : w - (ρ : ℂ) ≠ 0 := by
        obtain ⟨r, hz, hr0, hr1, hstrip⟩ := ρ
        have hrre : r.re < 1 / 2 + α := by
          have := (abs_lt.mp hstrip).2; linarith
        have h := Complex.abs_re_le_norm (w - s)
        rw [Complex.sub_re] at h
        have := (abs_le.mp (le_trans h hd.le)).1
        intro h0
        have : w.re = r.re := by
          have := congrArg Complex.re h0; simp at this; linarith
        rw [hδdef] at *; linarith
      unfold zeroResolventTerm
      apply DifferentiableAt.differentiableWithinAt
      fun_prop (disch := exact hne)
    have hD : DifferentiableOn ℂ (fun w => ∑' ρ : ZetaZerosInTraceStrip α,
        zeroResolventTerm α w ρ) U :=
      Complex.differentiableOn_tsum_of_summable_norm hsumC hdiff hU hbound
    have hAn : AnalyticOnNhd ℂ (fun w => ∑' ρ : ZetaZerosInTraceStrip α,
        zeroResolventTerm α w ρ) U :=
      (Complex.analyticOnNhd_iff_differentiableOn hU).mpr hD
    exact hAn s hsU
