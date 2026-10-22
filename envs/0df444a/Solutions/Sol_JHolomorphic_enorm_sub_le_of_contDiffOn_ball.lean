-- Prove2me | solution 1 for JHolomorphic.enorm_sub_le_of_contDiffOn_ball
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-22T00:26:18.187303+00:00
-- url     : https://prove2.me/submissions/a7698c3f-04ca-4ad8-9e52-47fe3dc77e36

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Analysis.Normed.Module.Convex
import Theorems.Thm_JHolomorphic_lintegral_enorm_comp_smul_add_le



namespace JHolomorphic

open MeasureTheory Metric Set
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem enorm_sub_le_of_contDiffOn_ball_aux {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiffOn ℝ 1 g (ball c r) →
      ∀ z ∈ ball c r, ∀ w ∈ ball c r, ‖g z - g w‖ₑ ≤
        ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
          eLpNorm (fderiv ℝ g) (ENNReal.ofReal p) (volume.restrict (ball c r)) := by
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
  intro c r hr g hg z hz w hw
  set q := ENNReal.ofReal p with hq
  set B := ball c r with hB
  set F : ℂ → ℝ := B.indicator (fun x => ‖fderiv ℝ g x‖) with hF
  have hFm : Measurable F := ((measurable_fderiv ℝ g).norm).indicator measurableSet_ball
  set M := eLpNorm F q volume with hM
  have hMeq : M = eLpNorm (fderiv ℝ g) q (volume.restrict B) := by
    rw [hM, hF, eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball]
    exact eLpNorm_norm (fderiv ℝ g)
  have hDg : ContinuousOn (fderiv ℝ g) B :=
    hg.continuousOn_fderiv_of_isOpen isOpen_ball (by norm_num)
  have hgd : ∀ x ∈ B, DifferentiableAt ℝ g x := fun x hx =>
    (hg.differentiableOn (by norm_num)).differentiableAt (isOpen_ball.mem_nhds hx)
  -- pointwise bound for a base point `a ∈ B` and one `y ∈ B`
  have hpt : ∀ a ∈ B, ∀ y ∈ B, ‖g a - g y‖ₑ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
      ENNReal.ofReal (2 * r) * ‖F (t • y + (1 - t) • a)‖ₑ := by
    intro a ha y hy
    set γ : ℝ → ℂ := fun t => t • y + (1 - t) • a with hγ
    have hγB : ∀ t ∈ Icc (0 : ℝ) 1, γ t ∈ B := fun t ht =>
      convex_ball c r hy ha ht.1 (by linarith [ht.2]) (by ring)
    have hγd : ∀ t, HasDerivAt γ (y - a) t := by
      intro t
      have h := ((hasDerivAt_id t).smul_const y).add (((hasDerivAt_id t).const_sub 1).smul_const a)
      exact h.congr_deriv (by simp [sub_eq_add_neg])
    have hγc : Continuous γ := by fun_prop
    have hder : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (g ∘ γ) (fderiv ℝ g (γ t) (y - a)) t := by
      intro t ht
      rw [uIcc_of_le zero_le_one] at ht
      exact (hgd _ (hγB t ht)).hasFDerivAt.comp_hasDerivAt t (hγd t)
    have hint : IntervalIntegrable (fun t => fderiv ℝ g (γ t) (y - a)) volume 0 1 := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [uIcc_of_le zero_le_one]
      exact ((hDg.comp hγc.continuousOn fun t ht => hγB t ht).clm_apply continuousOn_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
    have h1 : (g ∘ γ) 1 = g y := by simp [hγ]
    have h0 : (g ∘ γ) 0 = g a := by simp [hγ]
    rw [h1, h0, intervalIntegral.integral_of_le zero_le_one] at hftc
    have hga : ‖g a - g y‖ₑ = ‖∫ t in Ioc (0 : ℝ) 1, fderiv ℝ g (γ t) (y - a)‖ₑ := by
      rw [hftc, ← enorm_neg, neg_sub]
    rw [hga]
    refine (enorm_integral_le_lintegral_enorm _).trans
      (setLIntegral_mono' measurableSet_Ioc fun t ht => ?_)
    have htB := hγB t (Ioc_subset_Icc_self ht)
    have hya : ‖y - a‖ ≤ 2 * r := by
      rw [← dist_eq_norm]
      have := dist_triangle y c a
      rw [mem_ball] at hy ha
      rw [dist_comm c a] at this
      linarith
    have hFt : F (γ t) = ‖fderiv ℝ g (γ t)‖ := by rw [hF, indicator_of_mem htB]
    have hnorm : ‖fderiv ℝ g (γ t) (y - a)‖ ≤ 2 * r * ‖F (γ t)‖ := by
      rw [hFt, norm_norm]
      refine ((fderiv ℝ g (γ t)).le_opNorm _).trans ?_
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right hya (norm_nonneg _)
    rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm, ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_le_ofReal hnorm
  -- integrate over `y ∈ B`
  set P := volume B ^ (1 - 1 / p) with hP
  have hμB : volume B = ENNReal.ofReal (Real.pi * r ^ 2) := by
    rw [hB, Complex.volume_ball, ENNReal.ofReal_mul Real.pi_pos.le, mul_comm,
      ENNReal.ofReal_pow hr.le]
    congr 1
    exact (ENNReal.ofReal_coe_nnreal (p := NNReal.pi)).symm.trans (by simp)
  have hμB0 : volume B ≠ 0 := by rw [hμB]; exact (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hμBt : volume B ≠ ⊤ := by rw [hμB]; exact ENNReal.ofReal_ne_top
  have hint : ∀ a ∈ B, ∫⁻ y in B, ‖g a - g y‖ₑ ≤ ENNReal.ofReal (2 * r) * (M * P) *
      ENNReal.ofReal I0 := by
    intro a ha
    have hmeas : Measurable (Function.uncurry fun (y : ℂ) (t : ℝ) =>
        ENNReal.ofReal (2 * r) * ‖F (t • y + (1 - t) • a)‖ₑ) :=
      measurable_const.mul (hFm.enorm.comp (by fun_prop))
    calc ∫⁻ y in B, ‖g a - g y‖ₑ
        ≤ ∫⁻ y in B, ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (2 * r) * ‖F (t • y + (1 - t) • a)‖ₑ :=
          setLIntegral_mono' measurableSet_ball (hpt a ha)
      _ = ∫⁻ t in Ioc (0 : ℝ) 1, ∫⁻ y in B,
            ENNReal.ofReal (2 * r) * ‖F (t • y + (1 - t) • a)‖ₑ :=
          lintegral_lintegral_swap hmeas.aemeasurable
      _ ≤ ∫⁻ t in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (2 * r) * (M * P) * ENNReal.ofReal (t ^ (-2 / p)) := by
          refine setLIntegral_mono' measurableSet_Ioc fun t ht => ?_
          have hm1 : Measurable fun y : ℂ => ‖F (t • y + (1 - t) • a)‖ₑ :=
            hFm.enorm.comp (by fun_prop)
          rw [lintegral_const_mul _ hm1]
          have e1 := lintegral_enorm_comp_smul_add_le volume hp1 hFm.aestronglyMeasurable
            ht.1 ((1 - t) • a) B
          calc ENNReal.ofReal (2 * r) * ∫⁻ y in B, ‖F (t • y + (1 - t) • a)‖ₑ
              ≤ ENNReal.ofReal (2 * r) * (ENNReal.ofReal (t ^ (-2 / p)) * M * P) := by
                gcongr
            _ = ENNReal.ofReal (2 * r) * (M * P) * ENNReal.ofReal (t ^ (-2 / p)) := by ring
      _ = ENNReal.ofReal (2 * r) * (M * P) * ENNReal.ofReal I0 := by
          have hm : Measurable fun t : ℝ => ENNReal.ofReal (t ^ (-2 / p)) :=
            (measurable_id.pow_const _).ennreal_ofReal
          rw [lintegral_const_mul _ hm, hI]
  have hstep : ‖g z - g w‖ₑ * volume B ≤ ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal I0 := by
    have htri : ∀ y, ‖g z - g w‖ₑ ≤ ‖g z - g y‖ₑ + ‖g w - g y‖ₑ := by
      intro y
      rw [← edist_eq_enorm_sub, ← edist_eq_enorm_sub, ← edist_eq_enorm_sub, edist_comm (g w)]
      exact edist_triangle _ _ _
    calc ‖g z - g w‖ₑ * volume B = ∫⁻ _y in B, ‖g z - g w‖ₑ := by rw [setLIntegral_const]
      _ ≤ ∫⁻ y in B, (‖g z - g y‖ₑ + ‖g w - g y‖ₑ) := lintegral_mono fun y => htri y
      _ = (∫⁻ y in B, ‖g z - g y‖ₑ) + ∫⁻ y in B, ‖g w - g y‖ₑ := by
          refine lintegral_add_left' ?_ _
          exact (continuous_enorm.comp_continuousOn
            (continuousOn_const.sub hg.continuousOn)).aemeasurable measurableSet_ball
      _ ≤ ENNReal.ofReal (2 * r) * (M * P) * ENNReal.ofReal I0 +
            ENNReal.ofReal (2 * r) * (M * P) * ENNReal.ofReal I0 :=
          add_le_add (hint z hz) (hint w hw)
      _ = ENNReal.ofReal (4 * r) * (M * P) * ENNReal.ofReal I0 := by
          rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (by positivity) (by positivity)]
          ring_nf
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
    have hpos3 : 0 ≤ 4 * I0 * Real.pi ^ (-1 / p) * r ^ (1 - 2 / p) := by positivity
    calc ENNReal.ofReal (4 * r) * (M * ENNReal.ofReal ((Real.pi * r ^ 2) ^ (1 - 1 / p))) *
          ENNReal.ofReal I0
        = ENNReal.ofReal (4 * r * (Real.pi * r ^ 2) ^ (1 - 1 / p) * I0) * M := by
          rw [ENNReal.ofReal_mul (p := 4 * r * (Real.pi * r ^ 2) ^ (1 - 1 / p)) (by positivity),
            ENNReal.ofReal_mul hpos1]; ring
      _ = _ := by
          rw [hreal, ENNReal.ofReal_mul hpos3]; ring
  rw [hkey] at hstep
  rw [← hMeq]
  exact (ENNReal.mul_le_mul_iff_left hμB0 hμBt).1 hstep

end JHolomorphic

open JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

theorem solution {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (p : ℝ) (hp : 2 < p) :
    ∃ C : ℝ, ∀ (c : ℂ) (r : ℝ), 0 < r → ∀ g : ℂ → E, ContDiffOn ℝ 1 g (ball c r) →
      ∀ z ∈ ball c r, ∀ w ∈ ball c r, ‖g z - g w‖ₑ ≤
        ENNReal.ofReal (C * r ^ (1 - 2 / p)) *
          eLpNorm (fderiv ℝ g) (ENNReal.ofReal p) (volume.restrict (ball c r)) :=
  enorm_sub_le_of_contDiffOn_ball_aux p hp
