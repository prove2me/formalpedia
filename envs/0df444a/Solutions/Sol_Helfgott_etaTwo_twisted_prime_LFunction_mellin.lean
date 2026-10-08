-- Prove2me | solution 1 for Helfgott.etaTwo_twisted_prime_LFunction_mellin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-05T09:13:19.000649+00:00
-- url     : https://prove2.me/submissions/848c3480-2e52-4260-89ac-bc4f42634fbe

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.MeasureTheory.Integral.DominatedConvergence

section
open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_nonneg (t : ℝ) : 0 ≤ etaTwo t := by
  unfold etaTwo
  split_ifs <;> positivity

lemma etaTwo_le (t : ℝ) : etaTwo t ≤ 4 * Real.log 2 := by
  have hlog : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  unfold etaTwo
  split_ifs
  · apply mul_le_mul_of_nonneg_left _ (by norm_num)
    exact max_le (sub_le_self _ (abs_nonneg _)) hlog
  · positivity

lemma etaTwo_eq_zero_of_not_mem (t : ℝ) (ht : t ∉ Set.Icc (1/4 : ℝ) 1) :
    etaTwo t = 0 := by
  by_cases hpos : 0 < t
  · unfold etaTwo
    rw [if_pos hpos]
    have htwopos : 0 < 2*t := by positivity
    have hm : Real.log 2 - |Real.log (2*t)| ≤ 0 := by
      rcases (not_and_or.mp ht) with hlo | hhi
      · have hlt : 2*t ≤ (1/2 : ℝ) := by push_neg at hlo; linarith
        have hlog := Real.log_le_log htwopos hlt
        have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by
          rw [one_div, Real.log_inv]
        rw [hhalf] at hlog
        linarith [neg_le_abs (Real.log (2*t))]
      · have hlt : (2 : ℝ) ≤ 2*t := by push_neg at hhi; linarith
        have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hlt
        linarith [le_abs_self (Real.log (2*t))]
    rw [max_eq_right hm, mul_zero]
  · simp [etaTwo,hpos]

lemma etaTwo_eq_lower (t : ℝ) (ht : t ∈ Set.Icc (1/4 : ℝ) (1/2)) :
    etaTwo t = 4 * Real.log (4*t) := by
  have hpos : 0 < t := by linarith [ht.1]
  have hprod : 0 < 2*t := by positivity
  have hlogneg : Real.log (2*t) ≤ 0 := Real.log_nonpos (le_of_lt hprod) (by linarith [ht.2])
  have hsum : Real.log 2 + Real.log (2*t) = Real.log (4*t) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hprod)]
    congr 1; ring
  have hn : 0 ≤ Real.log (4*t) := Real.log_nonneg (by linarith [ht.1])
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonpos hlogneg, sub_neg_eq_add, hsum, max_eq_left hn]

lemma etaTwo_eq_upper (t : ℝ) (ht : t ∈ Set.Icc (1/2 : ℝ) 1) :
    etaTwo t = -4 * Real.log t := by
  have hpos : 0 < t := by linarith [ht.1]
  have hlogpos : 0 ≤ Real.log (2*t) := Real.log_nonneg (by linarith [ht.1])
  have hlogneg : Real.log t ≤ 0 := Real.log_nonpos (le_of_lt hpos) ht.2
  have hlog : Real.log (2*t) = Real.log 2 + Real.log t :=
    Real.log_mul (by norm_num) (ne_of_gt hpos)
  unfold etaTwo
  rw [if_pos hpos, abs_of_nonneg hlogpos, hlog]
  have hm : Real.log 2 - (Real.log 2 + Real.log t) = -Real.log t := by ring
  rw [hm, max_eq_left (neg_nonneg.mpr hlogneg)]
  ring

lemma etaTwo_continuousOn_pos : ContinuousOn etaTwo (Set.Ioi (0 : ℝ)) := by
  intro t ht
  apply ContinuousAt.continuousWithinAt
  have hg : ContinuousAt (fun s : ℝ => 4 * max (Real.log 2 - |Real.log (2*s)|) 0) t := by
    have hpos : 0 < t := ht
    have hn : 2*t ≠ 0 := by positivity
    fun_prop
  apply hg.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with x hx
  simp only [etaTwo, if_pos (show 0 < x from hx)]

theorem etaTwo_mass_interval : (∫ t in (1/4 : ℝ)..1, etaTwo t) = 1 := by
  have hint (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : IntervalIntegrable etaTwo volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply etaTwo_continuousOn_pos.mono
    intro t ht
    exact lt_of_lt_of_le (lt_min ha hb) ht.1
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hint (1/4) (1/2) (by norm_num) (by norm_num))
    (hint (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t in (1/4 : ℝ)..(1/2), etaTwo t) =
      ∫ t in (1/4 : ℝ)..(1/2), 4 * (Real.log 4 + Real.log t) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have hmem : t ∈ Set.Icc (1/4 : ℝ) (1/2) := by
      have h := Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)
      rw [h] at ht
      exact ht
    rw [etaTwo_eq_lower t hmem, Real.log_mul (by norm_num) (by linarith [hmem.1] : t ≠ 0)]
  have hhi : (∫ t in (1/2 : ℝ)..1, etaTwo t) = ∫ t in (1/2 : ℝ)..1, -4 * Real.log t := by
    apply intervalIntegral.integral_congr
    intro t ht
    apply etaTwo_eq_upper
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    exact ht
  rw [hlo,hhi,intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add (intervalIntegrable_const) (intervalIntegral.intervalIntegrable_log'),
    intervalIntegral.integral_const,integral_log,integral_log]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -(2 * Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [h4,hhalf,hquarter,Real.log_one]
  norm_num
  ring

lemma etaTwo_continuous : Continuous etaTwo := by
  apply continuous_iff_continuousAt.mpr
  intro t
  by_cases ht : 0 < t
  · exact (etaTwo_continuousOn_pos t ht).continuousAt (Ioi_mem_nhds ht)
  · have hlo : t < (1/4 : ℝ) := by linarith
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hlo] with x hx
    apply etaTwo_eq_zero_of_not_mem
    intro h; exact (not_lt_of_ge h.1) hx

lemma etaTwo_hasCompactSupport : HasCompactSupport etaTwo := by
  apply HasCompactSupport.intro (K := Set.Icc (1/4 : ℝ) 1) isCompact_Icc
  exact etaTwo_eq_zero_of_not_mem

lemma etaTwo_integrable : Integrable etaTwo :=
  etaTwo_continuous.integrable_of_hasCompactSupport etaTwo_hasCompactSupport

theorem etaTwo_mass : (∫ t : ℝ, etaTwo t) = 1 := by
  have hind : (Set.Icc (1/4 : ℝ) 1).indicator etaTwo = etaTwo := by
    funext t
    by_cases ht : t ∈ Set.Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht etaTwo
    · rw [Set.indicator_of_notMem ht,etaTwo_eq_zero_of_not_mem t ht]
  calc
    (∫ t : ℝ, etaTwo t) = ∫ t : ℝ, (Set.Icc (1/4 : ℝ) 1).indicator etaTwo t := by rw [hind]
    _ = ∫ t in Set.Icc (1/4 : ℝ) 1, etaTwo t := integral_indicator measurableSet_Icc
    _ = ∫ t in (1/4 : ℝ)..1, etaTwo t := by
      rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
    _ = 1 := etaTwo_mass_interval

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators Interval

namespace Helfgott

lemma cpow_log_primitive_hasDeriv (s : ℂ) (hs : s ≠ 0) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun y : ℝ =>
      (y : ℂ) ^ s * ((Real.log y : ℂ) * s - 1) / s ^ 2)
      ((t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) t := by
  have hd := ((hasDerivAt_ofReal_cpow_const ht.ne' hs).mul
    (((Real.hasDerivAt_log ht.ne').ofReal_comp.mul_const s).sub_const 1)).div_const (s ^ 2)
  have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hp : (t : ℂ) ^ s = (t : ℂ) ^ (s - 1) * (t : ℂ) := by
    calc
      _ = (t : ℂ) ^ ((s - 1) + 1) := by congr 1; ring
      _ = _ := by rw [Complex.cpow_add _ _ ht0, Complex.cpow_one]
  have he : (s * (t : ℂ) ^ (s - 1) * ((Real.log t : ℂ) * s - 1) +
      (t : ℂ) ^ s * ((t⁻¹ : ℝ) * s)) / s ^ 2 =
      (t : ℂ) ^ (s - 1) * (Real.log t : ℂ) := by
    rw [hp]
    push_cast
    field_simp
    ring
  rw [he] at hd
  exact hd

lemma integral_cpow_log_positive (s : ℂ) (hs : s ≠ 0)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ in a..b, (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) =
      (b : ℂ) ^ s * ((Real.log b : ℂ) * s - 1) / s ^ 2 -
      (a : ℂ) ^ s * ((Real.log a : ℂ) * s - 1) / s ^ 2 := by
  have hp (t : ℝ) (ht : t ∈ Set.uIcc a b) : 0 < t :=
    (lt_min ha hb).trans_le ht.1
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => cpow_log_primitive_hasDeriv s hs t (hp t ht))
  apply ContinuousOn.intervalIntegrable
  intro t ht
  have ht0 : t ≠ 0 := (hp t ht).ne'
  exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).mul
    (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log ht0))).continuousWithinAt

lemma etaTwo_mellin_convergent (s : ℂ) :
    MellinConvergent (fun t : ℝ => (etaTwo t : ℂ)) s := by
  let F : ℝ → ℂ := fun t => (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)
  have hc : ContinuousOn F (Icc (1/4 : ℝ) 1) := by
    intro t ht
    have ht0 : t ≠ 0 := by linarith [ht.1]
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht0)).mul
      (Complex.continuous_ofReal.comp etaTwo_continuous).continuousAt).continuousWithinAt
  have hi : IntegrableOn F (Icc (1/4 : ℝ) 1) := hc.integrableOn_Icc
  have hzero (t : ℝ) (ht : t ∉ Icc (1/4 : ℝ) 1) : F t = 0 := by
    simp [F, etaTwo_eq_zero_of_not_mem t ht]
  have he : (Icc (1/4 : ℝ) 1).indicator F = F := by
    ext t
    by_cases ht : t ∈ Icc (1/4 : ℝ) 1
    · exact Set.indicator_of_mem ht F
    · rw [Set.indicator_of_notMem ht, hzero t ht]
  have hall : Integrable F := by
    rw [← he]
    exact hi.integrable_indicator measurableSet_Icc
  exact hall.integrableOn

lemma etaTwo_mellin_eq_interval (s : ℂ) :
    mellin (fun t : ℝ => (etaTwo t : ℂ)) s =
      ∫ t : ℝ in (1/4 : ℝ)..1, (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ) := by
  unfold mellin
  simp only [smul_eq_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
      (s := Icc (1/4 : ℝ) 1)]
    · rw [intervalIntegral.integral_of_le (by norm_num : (1/4 : ℝ) ≤ 1),
        integral_Icc_eq_integral_Ioc]
    · intro t ht
      simp only [etaTwo_eq_zero_of_not_mem t ht, Complex.ofReal_zero, mul_zero]
  · intro t ht
    have ht0 : ¬0<t := ht
    simp [etaTwo, ht0]

theorem etaTwo_mellin_formula (s : ℂ) (hs : s ≠ 0) :
    mellin (fun t : ℝ => (etaTwo t : ℂ)) s =
      4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2 := by
  have hc : ContinuousOn (fun t : ℝ =>
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) (Ioi (0 : ℝ)) := by
    intro t ht
    exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr ht.ne')).mul
      (Complex.continuous_ofReal.comp etaTwo_continuous).continuousAt).continuousWithinAt
  have hi (a b : ℝ) (ha : 0<a) (hb : 0<b) :
      IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) volume a b := by
    apply (hc.mono ?_).intervalIntegrable
    intro t ht
    exact (lt_min ha hb).trans_le ht.1
  rw [etaTwo_mellin_eq_interval,
    ← intervalIntegral.integral_add_adjacent_intervals
      (hi (1/4) (1/2) (by norm_num) (by norm_num))
      (hi (1/2) 1 (by norm_num) (by norm_num))]
  have hlo : (∫ t : ℝ in (1/4 : ℝ)..(1/2),
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) =
      4 * ((Real.log 4 : ℂ) * (∫ t : ℝ in (1/4 : ℝ)..(1/2), (t : ℂ) ^ (s - 1)) +
        (∫ t : ℝ in (1/4 : ℝ)..(1/2), (t : ℂ) ^ (s - 1) * (Real.log t : ℂ))) := by
    have hi1 : IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (s-1)) volume (1/4) (1/2) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hp : 0<t := (lt_min (by norm_num : (0 : ℝ)<1/4)
        (by norm_num : (0 : ℝ)<1/2)).trans_le ht.1
      exact (Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne')).continuousWithinAt
    have hi2 : IntervalIntegrable (fun t : ℝ =>
        (t : ℂ) ^ (s-1) * (Real.log t : ℂ)) volume (1/4) (1/2) := by
      apply ContinuousOn.intervalIntegrable
      intro t ht
      have hp : 0<t := by norm_num at ht ⊢; linarith [ht.1]
      exact ((Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hp.ne')).mul
        (Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log hp.ne'))).continuousWithinAt
    rw [← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (hi1.const_mul _) hi2,
      ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)] at ht
    rw [etaTwo_eq_lower t ht, Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    push_cast
    ring
  have hhi : (∫ t : ℝ in (1/2 : ℝ)..1,
      (t : ℂ) ^ (s - 1) * (etaTwo t : ℂ)) =
      -4 * (∫ t : ℝ in (1/2 : ℝ)..1, (t : ℂ) ^ (s - 1) * (Real.log t : ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [Set.uIcc_of_le (by norm_num : (1/2 : ℝ) ≤ 1)] at ht
    rw [etaTwo_eq_upper t ht]
    push_cast
    ring
  rw [hlo, hhi, integral_cpow_log_positive s hs (1/4) (1/2) (by norm_num) (by norm_num),
    integral_cpow_log_positive s hs (1/2) 1 (by norm_num) (by norm_num),
    integral_cpow (r := s-1) (Or.inr ⟨by intro h; apply hs; linear_combination h,
      by norm_num [Set.uIcc_of_le (by norm_num : (1/4 : ℝ) ≤ 1/2)]⟩)]
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  have hquarter : Real.log (1/4 : ℝ) = -2 * Real.log 2 := by rw [one_div, Real.log_inv, h4]; ring
  have hp2 : (((1/2 : ℝ) : ℂ) ^ s) = (2 : ℂ) ^ (-s) := by
    rw [one_div, Complex.ofReal_inv]
    rw [Complex.inv_cpow_ofReal_nonneg (by norm_num : (0 : ℝ) ≤ 2), Complex.cpow_neg]
    norm_num
  have hp4 : (((1/4 : ℝ) : ℂ) ^ s) = ((2 : ℂ) ^ (-s)) ^ 2 := by
    have he : (1/4 : ℝ) = (1/2 : ℝ)*(1/2) := by norm_num
    rw [he, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num) (by norm_num), hp2]
    ring
  rw [sub_add_cancel, h4, hhalf, hquarter, Real.log_one, Complex.ofReal_one,
    Complex.one_cpow, hp2, hp4]
  push_cast
  field_simp
  ring

lemma etaTwo_mellin_vertical_bound (σ t : ℝ) (hσ : 0 < σ) :
    ‖mellin (fun u : ℝ => (etaTwo u : ℂ))
      ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      4 * (1 + (2 : ℝ) ^ (-σ)) ^ 2 / (σ ^ 2 + t ^ 2) := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  have hs : s ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp [s] at hr
    linarith
  have hn : ‖s‖ ^ 2 = σ ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm]
    simp [s, Complex.normSq]
    ring
  have hp : ‖(2 : ℂ) ^ (-s)‖ = (2 : ℝ) ^ (-σ) := by
    simpa [s] using (Complex.norm_cpow_eq_rpow_re_of_pos
      (x := (2 : ℝ)) (y := -s) (by norm_num))
  have hb : ‖1 - (2 : ℂ) ^ (-s)‖ ≤ 1 + (2 : ℝ) ^ (-σ) := by
    simpa [hp] using norm_sub_le (1 : ℂ) ((2 : ℂ) ^ (-s))
  rw [etaTwo_mellin_formula s hs, norm_div, norm_mul, norm_pow, norm_pow, hn]
  norm_num only [Complex.norm_ofNat]
  gcongr

lemma etaTwo_mellin_vertical_integrable (σ : ℝ) (hσ : 0 < σ) :
    Complex.VerticalIntegrable (mellin (fun u : ℝ => (etaTwo u : ℂ))) σ := by
  let C : ℝ := 4 * (1 + (2 : ℝ) ^ (-σ)) ^ 2
  have hs (t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  have hc : Continuous (fun t : ℝ =>
      mellin (fun u : ℝ => (etaTwo u : ℂ)) ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
    simp_rw [etaTwo_mellin_formula _ (hs _)]
    simp only [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact pow_ne_zero 2 (hs t)
  apply (integrable_inv_one_add_sq.const_mul (C * (1 + σ⁻¹ ^ 2))).mono' hc.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < σ ^ 2 + t ^ 2 := by positivity
  have hinv : σ ^ 2 * σ⁻¹ ^ 2 = 1 := by field_simp
  have hcompare : 1 + t ^ 2 ≤ (σ ^ 2 + t ^ 2) * (1 + σ⁻¹ ^ 2) := by
    nlinarith [sq_nonneg σ, sq_nonneg (t * σ⁻¹)]
  calc
    _ ≤ C / (σ ^ 2 + t ^ 2) := etaTwo_mellin_vertical_bound σ t hσ
    _ ≤ (C * (1 + σ⁻¹ ^ 2)) * (1 + t ^ 2)⁻¹ := by
      rw [← div_eq_mul_inv]
      apply (div_le_div_iff₀ hden (by positivity : (0 : ℝ)<1+t^2)).mpr
      have hC : 0≤C := by dsimp [C]; positivity
      nlinarith [mul_le_mul_of_nonneg_left hcompare hC]


end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open MeasureTheory Set
open scoped BigOperators LSeries.notation

namespace Helfgott

lemma vertical_cpow_norm (x : ℝ) (hx : 0 < x) (σ t : ℝ) :
    ‖(x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)‖ = x ^ σ := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  simp

lemma vertical_term_norm (c : ℕ → ℂ) (σ t : ℝ) (n : ℕ) :
    ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n‖ =
      ‖LSeries.term c (σ : ℂ) n‖ := by
  simp [LSeries.norm_term_eq]

lemma positive_ratio_cpow_inverse (x y : ℝ) (hx : 0 < x) (hy : 0 < y) (s : ℂ) :
    ((y / x : ℝ) : ℂ) ^ (-s) = (x : ℂ) ^ s / (y : ℂ) ^ s := by
  rw [Complex.ofReal_div, Complex.div_cpow_ofReal_nonneg hy.le hx.le, Complex.cpow_neg,
    Complex.cpow_neg]
  simp [div_eq_mul_inv, mul_comm]

lemma vertical_term_continuous (c : ℕ → ℂ) (σ : ℝ) (n : ℕ) :
    Continuous (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n) := by
  by_cases hn : n = 0
  · subst n
    simpa only [LSeries.term_zero] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℂ)))
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    simp only [LSeries.term_of_ne_zero hn, Complex.cpow_def_of_ne_zero hn0]
    exact continuous_const.div (by fun_prop) (fun _ => Complex.exp_ne_zero _)

lemma vertical_cpow_continuous (x : ℝ) (hx : 0 < x) (σ : ℝ) :
    Continuous (fun t : ℝ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  simp only [Complex.cpow_def_of_ne_zero hx0]
  fun_prop

lemma mellin_series_term_integrable (c : ℕ → ℂ) (σ x : ℝ) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) (n : ℕ) :
    Integrable (fun t : ℝ => LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_term_continuous c σ n).mul (vertical_cpow_continuous x hx σ)).aestronglyMeasurable.mul hF.1
  apply (hF.norm.const_mul (‖LSeries.term c (σ : ℂ) n‖ * x ^ σ)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_term_norm, vertical_cpow_norm x hx]

lemma mellin_series_norm_integrals_summable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x) (f : ℝ → ℂ) :
    Summable (fun n => ∫ t : ℝ,
      ‖LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖) := by
  simp_rw [norm_mul, vertical_term_norm, vertical_cpow_norm x hx,
    integral_const_mul]
  exact (hc.norm.mul_right (x ^ σ)).mul_right _

lemma mellin_series_integrable (c : ℕ → ℂ) (σ x : ℝ)
    (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hF : Complex.VerticalIntegrable (mellin f) σ) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  have hLm : AEStronglyMeasurable (fun t : ℝ =>
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    AEStronglyMeasurable.tsum (fun n => (vertical_term_continuous c σ n).aestronglyMeasurable)
  have hm : AEStronglyMeasurable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    ((vertical_cpow_continuous x hx σ).aestronglyMeasurable.mul hF.1).mul hLm
  have hb (t : ℝ) : ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      ∑' n, ‖LSeries.term c (σ : ℂ) n‖ := by
    have ht : Summable (fun n => ‖LSeries.term c
        ((σ : ℂ) + (t : ℂ) * Complex.I) n‖) :=
      hc.norm.congr (fun n => (vertical_term_norm c σ t n).symm)
    simpa only [LSeries, vertical_term_norm] using norm_tsum_le_tsum_norm ht
  apply (hF.norm.const_mul (x ^ σ * ∑' n, ‖LSeries.term c (σ : ℂ) n‖)).mono' hm
  filter_upwards [] with t
  rw [norm_mul, norm_mul, vertical_cpow_norm x hx]
  calc
    x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        ‖LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      x ^ σ * ‖mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)‖ *
        (∑' n, ‖LSeries.term c (σ : ℂ) n‖) := by
      gcongr
      exact hb t
    _ = _ := by ring

theorem mellin_weighted_series_hasSum (c : ℕ → ℂ) (hc0 : c 0 = 0)
    (σ x : ℝ) (hc : LSeriesSummable c (σ : ℂ)) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n => c n * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I)) := by
  let F : ℕ → ℝ → ℂ := fun n t =>
    LSeries.term c ((σ : ℂ) + (t : ℂ) * Complex.I) n *
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I)
  have hi : ∀ n, Integrable (F n) := mellin_series_term_integrable c σ x hx f hF
  have hs : Summable (fun n => ∫ t, ‖F n t‖) :=
    mellin_series_norm_integrals_summable c σ x hc hx f
  have hterm (n : ℕ) : (1 / (2 * Real.pi) : ℝ) • (∫ t, F n t) =
      c n * f ((n : ℝ) / x) := by
    by_cases hn : n = 0
    · subst n
      simp [F, hc0]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hnratio : 0 < (n : ℝ) / x := div_pos hnpos hx
      have hinv := mellinInv_mellin_eq σ f hnratio hf hF
        (hcont.continuousAt (Ioi_mem_nhds hnratio))
      rw [← hinv]
      simp only [mellinInv, smul_eq_mul, Complex.real_smul]
      rw [← mul_assoc, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with t
      dsimp [F]
      rw [LSeries.term_of_ne_zero hn,
        positive_ratio_cpow_inverse x (n : ℝ) hx hnpos]
      push_cast
      ring
  have hsum := (hasSum_integral_of_summable_integral_norm hi hs).const_smul
    (1 / (2 * Real.pi) : ℝ)
  simp_rw [hterm] at hsum
  have heq : (∫ t : ℝ, ∑' n, F n t) =
      ∫ t : ℝ, (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        LSeries c ((σ : ℂ) + (t : ℂ) * Complex.I) := by
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [F]
    rw [tsum_mul_right, tsum_mul_right]
    unfold LSeries
    ring
  rw [heq] at hsum
  exact hsum

theorem twisted_prime_mellin_hasSum (q : ℕ) (χ : DirichletCharacter ℂ q)
    (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv (LSeries (fun n : ℕ => χ n)) ((σ : ℂ) + (t : ℂ) * Complex.I) /
          LSeries (fun n : ℕ => χ n) ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have hs := mellin_weighted_series_hasSum
    (fun n => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  convert hs using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  have ht : 1 < ((σ : ℂ) + (t : ℂ) * Complex.I).re := by simpa using hσ
  have he := χ.LSeries_twist_vonMangoldt_eq ht
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact congrArg
    (fun z : ℂ => (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) * z)
    he.symm

lemma twisted_prime_LFunction_identity (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) s =
      -deriv χ.LFunction s / χ.LFunction s := by
  rw [χ.deriv_LFunction_eq_deriv_LSeries hs, χ.LFunction_eq_LSeries hs]
  have he := χ.LSeries_twist_vonMangoldt_eq hs
  have hec : ((fun n : ℕ => χ n) * (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℂ))) =
      (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    ext n
    rfl
  rw [hec] at he
  exact he

theorem twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x)
    (f : ℝ → ℂ) (hf : MellinConvergent f (σ : ℂ))
    (hF : Complex.VerticalIntegrable (mellin f) σ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ))) :
    Integrable (fun t : ℝ =>
      (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
      mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
      (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
        χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) * f ((n : ℝ) / x))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        (x : ℂ) ^ ((σ : ℂ) + (t : ℂ) * Complex.I) *
        mellin f ((σ : ℂ) + (t : ℂ) * Complex.I) *
        (-deriv χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I) /
          χ.LFunction ((σ : ℂ) + (t : ℂ) * Complex.I))) := by
  have hσc : 1 < (σ : ℂ).re := by simpa using hσ
  have hc := χ.LSeriesSummable_twist_vonMangoldt hσc
  have he (t : ℝ) := twisted_prime_LFunction_identity q χ
    ((σ : ℂ) + (t : ℂ) * Complex.I) (by simpa using hσ)
  have hi := mellin_series_integrable
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) σ x hc hx f hF
  have hs := mellin_weighted_series_hasSum
    (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ)) (by simp)
    σ x hc hx f hf hF hcont
  simp_rw [he] at hi hs
  exact ⟨hi, hs⟩


end Helfgott
end

section
open MeasureTheory Set
open scoped BigOperators

namespace Helfgott

theorem etaTwo_twisted_prime_LFunction_mellin (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      (etaTwo ((n : ℝ) / x) : ℂ))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
        (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
          (-deriv χ.LFunction s / χ.LFunction s)) := by
  have hc : ContinuousOn (fun u : ℝ => (etaTwo u : ℂ)) (Ioi (0 : ℝ)) :=
    (Complex.continuous_ofReal.comp etaTwo_continuous).continuousOn
  have h := twisted_prime_LFunction_mellin q χ σ x hσ hx
    (fun u : ℝ => (etaTwo u : ℂ)) (etaTwo_mellin_convergent _)
    (etaTwo_mellin_vertical_integrable σ (by linarith)) hc
  have hs (t : ℝ) : ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro he
    have hr := congrArg Complex.re he
    simp at hr
    linarith
  simp_rw [etaTwo_mellin_formula _ (hs _)] at h
  exact h


end Helfgott
end

open MeasureTheory Set

theorem solution (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (σ x : ℝ) (hσ : 1 < σ) (hx : 0 < x) :
    Integrable (fun t : ℝ =>
      let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
        (-deriv χ.LFunction s / χ.LFunction s)) ∧
    HasSum (fun n : ℕ => χ n * (ArithmeticFunction.vonMangoldt n : ℂ) *
      (Helfgott.etaTwo ((n : ℝ) / x) : ℂ))
      ((1 / (2 * Real.pi) : ℝ) • ∫ t : ℝ,
        let s : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
        (x : ℂ) ^ s * (4 * (1 - (2 : ℂ) ^ (-s)) ^ 2 / s ^ 2) *
          (-deriv χ.LFunction s / χ.LFunction s)) := Helfgott.etaTwo_twisted_prime_LFunction_mellin q χ σ x hσ hx

#print axioms solution
