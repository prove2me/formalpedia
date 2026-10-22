-- Prove2me | solution 1 for JHolomorphic.enorm_le_of_contDiff_tsupport_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-21T21:07:17.719738+00:00
-- url     : https://prove2.me/submissions/8f25e743-dcc9-47da-a221-0da280dee15f

import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Theorems.Thm_JHolomorphic_lintegral_enorm_comp_smul_add_le
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations



namespace JHolomorphic

open MeasureTheory Metric Set
open scoped ContDiff

theorem enorm_le_of_contDiff_tsupport_ball_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hexp : -1 < -2 / p := by
    rw [neg_div, neg_lt_neg_iff, div_lt_one hp0]; exact hp
  -- the one-dimensional integral
  set I0 : ℝ := ∫ t in Ioc (0 : ℝ) 1, t ^ (-2 / p) with hI0
  have hIint : IntegrableOn (fun t : ℝ => t ^ (-2 / p)) (Ioc 0 1) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
      (intervalIntegral.intervalIntegrable_rpow' hexp)
  have hI : ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (t ^ (-2 / p)) = ENNReal.ofReal I0 := by
    rw [hI0, ofReal_integral_eq_lintegral_ofReal hIint]
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact Real.rpow_nonneg ht.1.le _
  have hI0nn : 0 ≤ I0 := setIntegral_nonneg measurableSet_Ioc fun t ht => Real.rpow_nonneg ht.1.le _
  refine ⟨4 * I0 * Real.pi ^ (-1 / p), ?_⟩
  intro c r hr g hg hsub z
  set q := ENNReal.ofReal p with hq
  set Fs : ℂ → E := fun y => fderiv ℝ g y 1 with hFs
  set Ft : ℂ → E := fun y => fderiv ℝ g y Complex.I with hFt
  set M := eLpNorm Fs q volume + eLpNorm Ft q volume with hM
  have hDg : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by norm_num)
  have hFsc : Continuous Fs := hDg.clm_apply continuous_const
  have hFtc : Continuous Ft := hDg.clm_apply continuous_const
  have hgd : Differentiable ℝ g := hg.differentiable (by norm_num)
  by_cases hz : z ∈ ball c r
  swap
  · rw [image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), enorm_zero]
    exact bot_le
  -- the disc where `g` vanishes
  set c' : ℂ := c + ((2 * r : ℝ) : ℂ) with hc'
  set B := ball c' r with hB
  have hdc : dist c' c = 2 * r := by
    rw [hc', dist_eq_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hgw : ∀ w ∈ B, g w = 0 := by
    intro w hw
    refine image_eq_zero_of_notMem_tsupport fun h => ?_
    have h1 := hsub h
    rw [mem_ball] at h1 hw
    have := dist_triangle c' w c
    rw [dist_comm c' w] at this
    linarith
  have hwz : ∀ w ∈ B, ‖w - z‖ < 4 * r := by
    intro w hw
    rw [mem_ball] at hw hz
    have h1 := dist_triangle w c' z
    have h2 := dist_triangle c' c z
    rw [dist_comm c z] at h2
    rw [← dist_eq_norm]
    linarith
  -- pointwise bound for one `w`
  have hpt : ∀ w ∈ B, ‖g z‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (4 * r) * (‖Fs (t • w + (1 - t) • z)‖ₑ + ‖Ft (t • w + (1 - t) • z)‖ₑ) := by
    intro w hw
    set γ : ℝ → ℂ := fun t => t • w + (1 - t) • z with hγ
    have hγd : ∀ t, HasDerivAt γ (w - z) t := by
      intro t
      have h := ((hasDerivAt_id t).smul_const w).add (((hasDerivAt_id t).const_sub 1).smul_const z)
      exact h.congr_deriv (by simp [sub_eq_add_neg])
    have hγc : Continuous γ := by fun_prop
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (g ∘ γ) (fderiv ℝ g (γ t) (w - z)) t :=
      fun t _ => (hgd (γ t)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    have hint : IntervalIntegrable (fun t => fderiv ℝ g (γ t) (w - z)) volume 0 1 :=
      ((hDg.comp hγc).clm_apply continuous_const).intervalIntegrable _ _
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    have h1 : (g ∘ γ) 1 = 0 := by simp [hγ, hgw w hw]
    have h0 : (g ∘ γ) 0 = g z := by simp [hγ]
    rw [h1, h0, zero_sub, intervalIntegral.integral_of_le zero_le_one] at hftc
    have hgz : ‖g z‖ₑ = ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ g (γ t) (w - z)‖ₑ := by
      rw [hftc, enorm_neg]
    rw [hgz]
    refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun t => ?_)
    -- split the direction into its real and imaginary parts
    set a := w - z with ha
    have hdec : a = a.re • (1 : ℂ) + a.im • Complex.I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one]; exact (Complex.re_add_im a).symm
    have hnorm : ‖fderiv ℝ g (γ t) a‖ ≤ 4 * r * (‖Fs (γ t)‖ + ‖Ft (γ t)‖) := by
      rw [hdec, map_add, map_smul, map_smul]
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hre : |a.re| ≤ 4 * r := (Complex.abs_re_le_norm a).trans (hwz w hw).le
      have him : |a.im| ≤ 4 * r := (Complex.abs_im_le_norm a).trans (hwz w hw).le
      rw [mul_add]
      exact add_le_add (mul_le_mul_of_nonneg_right hre (norm_nonneg _))
        (mul_le_mul_of_nonneg_right him (norm_nonneg _))
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hnorm
  -- integrate over `w ∈ B`
  set P := volume B ^ (1 - 1 / p) with hP
  have hμB : volume B = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [hB, Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, mul_comm,
      ENNReal.ofReal_pow hr.le]
    congr 1
    exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm.trans (by simp)
  have hμB0 : volume B ≠ 0 := by rw [hμB]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hμBt : volume B ≠ ⊤ := by rw [hμB]; exact ENNReal.ofReal_ne_top
  have hmeas : ∀ (F : ℂ → E), Continuous F →
      Measurable (Function.uncurry fun (w : ℂ) (t : ℝ) => ‖F (t • w + (1 - t) • z)‖ₑ) := by
    intro F hF
    exact (continuous_enorm.comp (hF.comp (by fun_prop))).measurable
  have hstep : ‖g z‖ₑ * volume B ≤ ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal I0 := by
    calc ‖g z‖ₑ * volume B = ∫⁻ _w in B, ‖g z‖ₑ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ w in B, ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (4 * r) * (‖Fs (t • w + (1 - t) • z)‖ₑ +
            ‖Ft (t • w + (1 - t) • z)‖ₑ) := setLIntegral_mono' measurableSet_ball hpt
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ w in B,
          ENNReal.ofReal (4 * r) * (‖Fs (t • w + (1 - t) • z)‖ₑ +
            ‖Ft (t • w + (1 - t) • z)‖ₑ) := by
          refine lintegral_lintegral_swap ?_
          exact (((hmeas Fs hFsc).add (hmeas Ft hFtc)).const_mul _).aemeasurable
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
          ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal (t ^ (-2 / p)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          have hm1 : ∀ F : ℂ → E, Continuous F →
              Measurable fun w : ℂ => ‖F (t • w + (1 - t) • z)‖ₑ := fun F hF =>
            (continuous_enorm.comp (hF.comp (by fun_prop))).measurable
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left (hm1 Fs hFsc)]
          have e1 := lintegral_enorm_comp_smul_add_le volume hp1 hFsc.aestronglyMeasurable
            ht.1 ((1 - t) • z) B
          have e2 := lintegral_enorm_comp_smul_add_le volume hp1 hFtc.aestronglyMeasurable
            ht.1 ((1 - t) • z) B
          calc ENNReal.ofReal (4 * r) * ((∫⁻ w in B, ‖Fs (t • w + (1 - t) • z)‖ₑ) +
                ∫⁻ w in B, ‖Ft (t • w + (1 - t) • z)‖ₑ)
              ≤ ENNReal.ofReal (4 * r) *
                (ENNReal.ofReal (t ^ (-2 / p)) * eLpNorm Fs q volume * P +
                  ENNReal.ofReal (t ^ (-2 / p)) * eLpNorm Ft q volume * P) := by
                gcongr
            _ = ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal (t ^ (-2 / p)) := by
                rw [hM]; ring
      _ = ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal I0 := by
          have hm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-2 / p)) :=
            (measurable_id.pow_const _).ennreal_ofReal
          rw [lintegral_const_mul _ hm, hI]
  -- divide by the measure of `B`
  have hkey : ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal I0 =
      ENNReal.ofReal (4 * I0 * Real.pi ^ (-1 / p) * r ^ (1 - 2 / p)) * M * volume B := by
    have hPr : P = ENNReal.ofReal ((Real.pi * r ^ 2) ^ (1 - 1 / p)) := by
      rw [hP, hμB, ENNReal.ofReal_rpow_of_nonneg (by positivity)]
      rw [sub_nonneg, div_le_one hp0]; exact hp1
    rw [hPr, hμB]
    have hreal : 4 * r * (Real.pi * r ^ 2) ^ (1 - 1 / p) * I0 =
        4 * I0 * Real.pi ^ (-1 / p) * r ^ (1 - 2 / p) * (Real.pi * r ^ 2) := by
      rw [Real.mul_rpow Real.pi_pos.le (by positivity), ← Real.rpow_natCast r 2,
        ← Real.rpow_mul hr.le]
      have hpi : Real.pi ^ (1 - 1 / p) = Real.pi ^ (-1 / p) * Real.pi := by
        rw [← Real.rpow_add_one Real.pi_pos.ne']; ring_nf
      have hrr : r ^ ((2 : ℕ) * (1 - 1 / p) : ℝ) * r = r ^ (1 - 2 / p) * r ^ (2 : ℕ) := by
        rw [← Real.rpow_add_one hr.ne', ← Real.rpow_natCast, ← Real.rpow_add hr]
        congr 1; push_cast; ring
      rw [hpi]
      calc 4 * r * (Real.pi ^ (-1 / p) * Real.pi * r ^ ((2 : ℕ) * (1 - 1 / p) : ℝ)) * I0
          = 4 * I0 * Real.pi ^ (-1 / p) * Real.pi * (r ^ ((2 : ℕ) * (1 - 1 / p) : ℝ) * r) := by
            ring
        _ = _ := by rw [hrr, Real.rpow_natCast]; ring
    have hpos1 : 0 ≤ 4 * r := by positivity
    have hpos2 : 0 ≤ (Real.pi * r ^ 2) ^ (1 - 1 / p) := by positivity
    have hpos3 : 0 ≤ 4 * I0 * Real.pi ^ (-1 / p) * r ^ (1 - 2 / p) := by positivity
    calc ENNReal.ofReal (4 * r) * (M * ENNReal.ofReal ((Real.pi * r ^ 2) ^ (1 - 1 / p))) *
          ENNReal.ofReal I0
        = ENNReal.ofReal (4 * r * (Real.pi * r ^ 2) ^ (1 - 1 / p) * I0) * M := by
          rw [ENNReal.ofReal_mul (p := 4 * r * (Real.pi * r ^ 2) ^ (1 - 1 / p)) (by positivity),
            ENNReal.ofReal_mul hpos1]; ring
      _ = _ := by
          rw [hreal, ENNReal.ofReal_mul hpos3]; ring
  rw [hkey] at hstep
  exact (ENNReal.mul_le_mul_iff_left hμB0 hμBt).1 hstep

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      tsupport g ⊆ ball c r → ∀ z, ‖g z‖ₑ ≤ ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
        (eLpNorm (fun y => fderiv ℝ g y 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun y => fderiv ℝ g y Complex.I) (ENNReal.ofReal p) volume) :=
  enorm_le_of_contDiff_tsupport_ball_aux p hp
