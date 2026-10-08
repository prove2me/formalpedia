-- Prove2me | solution 1 for Helfgott.etaStar_moments
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T22:04:46.952905+00:00
-- url     : https://prove2.me/submissions/1d4208e6-7e2e-46a5-ab4f-ef9f0a5db7e3

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-! Full Mellin/Fubini/convergence and smoothing moment proofs. Written by Codex. -/

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

open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_inner_integrable (f : ℝ → ℝ) (hf : IntegrableOn f (Ioi (0 : ℝ)))
    (w c : ℝ) (hw : 0 < w) :
    IntegrableOn (fun t : ℝ => f (t/w)*c/w) (Ioi (0 : ℝ)) := by
  have hh : IntegrableOn (fun t : ℝ => f (t*w⁻¹)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_right_iff f 0 (inv_pos.mpr hw)).mpr
    simpa using hf
  simpa only [IntegrableOn,div_eq_mul_inv,mul_assoc] using (hh.mul_const c).mul_const w⁻¹

lemma mellin_inner_integral (f : ℝ → ℝ) (w c : ℝ) (hw : 0 < w) :
    (∫ t in Ioi (0 : ℝ), f (t/w)*c/w) = c*(∫ t in Ioi (0 : ℝ), f t) := by
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const,integral_mul_const,
    integral_comp_mul_right_Ioi f 0 (inv_pos.mpr hw)]
  simp only [zero_mul,inv_inv,smul_eq_mul]
  field_simp

theorem mellin_integrable_mass (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfi : IntegrableOn f (Ioi (0 : ℝ))) (hgi : IntegrableOn g (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (mellinConv f g) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), f t)*(∫ t in Ioi (0 : ℝ), g t) := by
  let μ : Measure ℝ := volume.restrict (Ioi (0 : ℝ))
  have hm : Measurable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) := by
    fun_prop
  have hp : Integrable (fun z : ℝ × ℝ => f (z.2/z.1)*g z.1/z.1) (μ.prod μ) := by
    apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      exact mellin_inner_integrable f hfi w (g w) hw
    · have heq : (fun w : ℝ => ∫ t, ‖f (t/w)*g w/w‖ ∂μ) =ᵐ[μ]
          fun w => g w*(∫ t, f t ∂μ) := by
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        have hnorm : (∫ t, ‖f (t/w)*g w/w‖ ∂μ) = ∫ t, f (t/w)*g w/w ∂μ := by
          apply integral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
          exact Real.norm_of_nonneg
            (div_nonneg (mul_nonneg (hfn _ (div_pos ht hw)) (hgn _ hw)) hw.le)
        rw [hnorm]
        exact mellin_inner_integral f w (g w) hw
      apply (hgi.mul_const (∫ t, f t ∂μ)).congr
      exact heq.symm
  constructor
  · exact hp.integral_prod_right
  unfold mellinConv
  change (∫ t, ∫ w, f (t/w)*g w/w ∂μ ∂μ) = _
  rw [← integral_integral_swap hp]
  have heq : (∫ w, ∫ t, f (t/w)*g w/w ∂μ ∂μ) =
      ∫ w, g w*(∫ t, f t ∂μ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    exact mellin_inner_integral f w (g w) hw
  rw [heq,integral_mul_const]
  exact mul_comm _ _

lemma mellin_moment_identity (f g : ℝ → ℝ) (k : ℕ) (t : ℝ) :
    t^k*mellinConv f g t =
      mellinConv (fun t => t^k*f t) (fun w => w^k*g w) t := by
  unfold mellinConv
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [div_pow]
  have hn : w ≠ 0 := hw.ne'
  field_simp

theorem mellin_moment (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (k : ℕ) (hfi : IntegrableOn (fun t => t^k*f t) (Ioi (0 : ℝ)))
    (hgi : IntegrableOn (fun t => t^k*g t) (Ioi (0 : ℝ)))
    (hfn : ∀ t, 0 < t → 0 ≤ f t) (hgn : ∀ t, 0 < t → 0 ≤ g t) :
    IntegrableOn (fun t => t^k*mellinConv f g t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv f g t) =
      (∫ t in Ioi (0 : ℝ), t^k*f t)*(∫ t in Ioi (0 : ℝ), t^k*g t) := by
  simp_rw [mellin_moment_identity]
  apply mellin_integrable_mass _ _ ((continuous_id.pow k).mul hf) ((continuous_id.pow k).mul hg)
    hfi hgi
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hfn t ht)
  · intro t ht; exact mul_nonneg (pow_nonneg ht.le k) (hgn t ht)

end Helfgott

open MeasureTheory Set

namespace Helfgott

lemma phi_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*phi t) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1/2)
    (s := ((k+2 : ℕ) : ℝ)) (by have hk := Nat.cast_nonneg (α := ℝ) (k+2); linarith : (-1 : ℝ) < ((k+2 : ℕ) : ℝ))
  convert! h using 1
  funext t
  rw [Real.rpow_natCast]
  unfold phi
  rw [pow_add]
  have he : -(1/2 : ℝ)*t^2 = -(t^2)/2 := by ring
  rw [he]
  ring

lemma gaussian_power_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*Real.exp (-(t^2)/2)) =
      (1/2 : ℝ)^(-(((k : ℝ)+1)/2))*(1/2)*Real.Gamma (((k : ℝ)+1)/2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow
    (p := (2 : ℝ)) (q := (k : ℝ)) (b := (1/2 : ℝ))
    (by norm_num) (by have hk := Nat.cast_nonneg (α := ℝ) k; linarith) (by norm_num)
  simp only [neg_div] at h ⊢
  rw [← h]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro t ht
  dsimp only
  rw [Real.rpow_natCast,Real.rpow_two]
  congr 1 <;> ring

theorem phi_mass : (∫ t in Ioi (0 : ℝ), phi t) = Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 2
  norm_num only [Nat.cast_ofNat] at h
  have hg : Real.Gamma (3/2 : ℝ) = (1/2)*Real.sqrt Real.pi := by
    rw [show (3/2 : ℝ) = 1/2+1 by norm_num,
      Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
  have he : (1/2 : ℝ)^(-(3/2 : ℝ)) = 2*Real.sqrt 2 := by
    rw [show (-(3/2 : ℝ)) = -1+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg_one,
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  change (∫ t in Ioi (0 : ℝ), t^2*Real.exp (-(t^2)/2)) = _
  rw [h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

theorem phi_first_moment : (∫ t in Ioi (0 : ℝ), t*phi t) = 2 := by
  have h := gaussian_power_integral 3
  have hg : Real.Gamma (2 : ℝ) = 1 := by
    rw [show (2 : ℝ) = 1+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one]
    norm_num
  have he : (1/2 : ℝ)^(-(2 : ℝ)) = 4 := by
    rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),Real.rpow_two]
    norm_num
  have heq : (fun t : ℝ => t*phi t) = fun t => t^3*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num [hg,he]

theorem phi_second_moment : (∫ t in Ioi (0 : ℝ), t^2*phi t) =
    3*Real.sqrt (Real.pi/2) := by
  have h := gaussian_power_integral 4
  have hg : Real.Gamma (5/2 : ℝ) = (3/4)*Real.sqrt Real.pi := by
    rw [show (5/2 : ℝ) = 3/2+1 by norm_num,Real.Gamma_add_one (by norm_num),
      show (3/2 : ℝ) = 1/2+1 by norm_num,Real.Gamma_add_one (by norm_num),Real.Gamma_one_half_eq]
    ring
  have he : (1/2 : ℝ)^(-(5/2 : ℝ)) = 4*Real.sqrt 2 := by
    rw [show (-(5/2 : ℝ)) = -2+ -(1/2 : ℝ) by norm_num,
      Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),
      Real.rpow_two,Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 1/2),← Real.sqrt_eq_rpow]
    norm_num
  have heq : (fun t : ℝ => t^2*phi t) = fun t => t^4*Real.exp (-(t^2)/2) := by
    funext t; unfold phi; ring
  rw [heq,h]
  norm_num
  rw [hg,he]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hn : Real.sqrt 2 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp
  nlinarith

end Helfgott

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma integral_power_log (k : ℕ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (C : ℝ) :
    (∫ t in a..b, t^k*(C+Real.log t)) =
      b^(k+1)/((k:ℝ)+1)*(C+Real.log b-1/((k:ℝ)+1)) -
      a^(k+1)/((k:ℝ)+1)*(C+Real.log a-1/((k:ℝ)+1)) := by
  have hkn : (k:ℝ)+1 ≠ 0 := by have hk := Nat.cast_nonneg (α := ℝ) k; linarith
  have hpos (t : ℝ) (ht : t ∈ uIcc a b) : 0 < t := lt_of_lt_of_le (lt_min ha hb) ht.1
  have hi : IntervalIntegrable (fun t : ℝ => t^k*(C+Real.log t)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    intro t ht
    have hn : t ≠ 0 := (hpos t ht).ne'
    apply ContinuousAt.continuousWithinAt
    fun_prop
  have hd (t : ℝ) (ht : t ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => t^(k+1)/((k:ℝ)+1)*(C+Real.log t-1/((k:ℝ)+1)))
        (t^k*(C+Real.log t)) t := by
    have hn : t ≠ 0 := (hpos t ht).ne'
    have hp := ((hasDerivAt_id t).pow (k+1)).div_const ((k:ℝ)+1)
    have hl := ((Real.hasDerivAt_log hn).const_add C).sub_const (1/((k:ℝ)+1))
    convert! hp.mul hl using 1
    all_goals simp only [Nat.cast_add,Nat.cast_one,Nat.add_sub_cancel,one_mul,id_eq,Pi.pow_apply]
    all_goals field_simp
    all_goals simp only [pow_succ]
    all_goals ring
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi

lemma etaTwo_moment_integrable (k : ℕ) : Integrable (fun t : ℝ => t^k*etaTwo t) := by
  apply ((continuous_id.pow k).mul etaTwo_continuous).integrable_of_hasCompactSupport
  exact etaTwo_hasCompactSupport.mul_left

lemma etaTwo_moment_formula (k : ℕ) :
    (∫ t : ℝ, t^k*etaTwo t) =
      4*((1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/2)-1/((k:ℝ)+1)) -
        (1/4:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log 4+Real.log (1/4)-1/((k:ℝ)+1))) -
      4*(1/((k:ℝ)+1)*(Real.log 1-1/((k:ℝ)+1)) -
        (1/2:ℝ)^(k+1)/((k:ℝ)+1)*(Real.log (1/2)-1/((k:ℝ)+1))) := by
  have hc : Continuous (fun t : ℝ => t^k*etaTwo t) := (continuous_id.pow k).mul etaTwo_continuous
  have heq : (∫ t : ℝ, t^k*etaTwo t) = ∫ t in (1/4:ℝ)..1, t^k*etaTwo t := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc (1/4:ℝ) 1)
      (show ∀ t : ℝ, t ∉ Icc (1/4:ℝ) 1 → t^k*etaTwo t = 0 by
        intro t ht; rw [etaTwo_eq_zero_of_not_mem t ht,mul_zero])]
    rw [intervalIntegral.integral_of_le (by norm_num),integral_Icc_eq_integral_Ioc]
  rw [heq, ← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (1/4) (1/2)) (hc.intervalIntegrable (1/2) 1)]
  have hlo : (∫ t in (1/4:ℝ)..(1/2), t^k*etaTwo t) =
      4*∫ t in (1/4:ℝ)..(1/2), t^k*(Real.log 4+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/4:ℝ) ≤ 1/2)] at ht
    dsimp only
    rw [etaTwo_eq_lower t ht,Real.log_mul (by norm_num) (by linarith [ht.1] : t ≠ 0)]
    ring
  have hhi : (∫ t in (1/2:ℝ)..1, t^k*etaTwo t) =
      -4*∫ t in (1/2:ℝ)..1, t^k*(0+Real.log t) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le (by norm_num : (1/2:ℝ) ≤ 1)] at ht
    dsimp only
    rw [etaTwo_eq_upper t ht]
    ring
  rw [hlo,hhi,integral_power_log k (1/4) (1/2) (by norm_num) (by norm_num) (Real.log 4),
    integral_power_log k (1/2) 1 (by norm_num) (by norm_num) 0]
  simp
  ring

theorem etaTwo_first_moment : (∫ t : ℝ, t*etaTwo t) = (9/16 : ℝ) := by
  have h := etaTwo_moment_formula 1
  have heq : (fun t : ℝ => t*etaTwo t) = fun t => t^1*etaTwo t := by simp
  rw [heq,h]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

theorem etaTwo_second_moment : (∫ t : ℝ, t^2*etaTwo t) = (49/144 : ℝ) := by
  rw [etaTwo_moment_formula 2]
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
  have hh : Real.log (1/2 : ℝ) = -Real.log 2 := by rw [one_div,Real.log_inv]
  have hq : Real.log (1/4 : ℝ) = -(2*Real.log 2) := by rw [one_div,Real.log_inv,h4]
  rw [hh,hq,h4,Real.log_one]
  norm_num
  ring

end Helfgott

open MeasureTheory Set

namespace Helfgott

lemma etaTwo_moment_pos_integral (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaTwo t) = ∫ t : ℝ, t^k*etaTwo t := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro t ht
  simp [etaTwo,show ¬0 < t from ht]

lemma mellin_etaTwo_phi_moment (k : ℕ) :
    IntegrableOn (fun t => t^k*mellinConv etaTwo phi t) (Ioi (0 : ℝ)) ∧
    (∫ t in Ioi (0 : ℝ), t^k*mellinConv etaTwo phi t) =
      (∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t) := by
  rw [← etaTwo_moment_pos_integral]
  apply mellin_moment _ _ etaTwo_continuous (by unfold phi; fun_prop)
    k (etaTwo_moment_integrable k).integrableOn (phi_moment_integrable k)
  · intro t ht; exact etaTwo_nonneg t
  · intro t ht; unfold phi; positivity

lemma scaled_moment_integral (F : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*F (κ*t)) =
      (∫ t in Ioi (0 : ℝ), t^k*F t)/κ^(k+1) := by
  have heq : (fun t : ℝ => t^k*F (κ*t)) =
      fun t => (κ^k)⁻¹*((κ*t)^k*F (κ*t)) := by
    funext t
    rw [mul_pow]
    field_simp
  rw [heq,integral_const_mul,
    integral_comp_mul_left_Ioi (fun t => t^k*F t) 0 hκ]
  simp only [mul_zero,smul_eq_mul,pow_succ,div_eq_mul_inv,mul_inv_rev]
  ring

lemma etaStar_moment_integrable (k : ℕ) :
    IntegrableOn (fun t : ℝ => t^k*etaStar t) (Ioi (0 : ℝ)) := by
  have hmc := (mellin_etaTwo_phi_moment k).1
  have hs : IntegrableOn (fun t : ℝ => (49*t)^k*mellinConv etaTwo phi (49*t)) (Ioi (0 : ℝ)) := by
    apply (integrableOn_Ioi_comp_mul_left_iff
      (fun t => t^k*mellinConv etaTwo phi t) 0 (by norm_num : (0 : ℝ) < 49)).mpr
    simpa using hmc
  have hh := hs.const_mul ((49 : ℝ)^k)⁻¹
  have heq : (fun t : ℝ => t^k*etaStar t) =
      fun t => ((49 : ℝ)^k)⁻¹*((49*t)^k*mellinConv etaTwo phi (49*t)) := by
    funext t
    unfold etaStar
    rw [mul_pow]
    field_simp
  rw [heq]
  exact hh

lemma etaStar_moment_formula (k : ℕ) :
    (∫ t in Ioi (0 : ℝ), t^k*etaStar t) =
      ((∫ t : ℝ, t^k*etaTwo t)*(∫ t in Ioi (0 : ℝ), t^k*phi t))/(49 : ℝ)^(k+1) := by
  unfold etaStar
  rw [scaled_moment_integral _ 49 (by norm_num), (mellin_etaTwo_phi_moment k).2]

theorem etaStar_moments :
    (∫ t in Ioi (0 : ℝ), etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Ioi (0 : ℝ), t*etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Ioi (0 : ℝ), t^2*etaStar t) = Real.sqrt (Real.pi/2)/115248 := by
  constructor
  · have h := etaStar_moment_formula 0
    simpa [etaTwo_mass,phi_mass] using h
  constructor
  · have h := etaStar_moment_formula 1
    norm_num [etaTwo_first_moment,phi_first_moment] at h
    simpa using h
  · rw [etaStar_moment_formula 2,etaTwo_second_moment,phi_second_moment]
    norm_num
    ring

end Helfgott

theorem solution :
    (∫ t in Set.Ioi (0 : ℝ), Helfgott.etaStar t) = Real.sqrt (Real.pi/2)/49 ∧
    (∫ t in Set.Ioi (0 : ℝ), t*Helfgott.etaStar t) = (9/19208 : ℝ) ∧
    (∫ t in Set.Ioi (0 : ℝ), t^2*Helfgott.etaStar t) = Real.sqrt (Real.pi/2)/115248 := Helfgott.etaStar_moments

#print axioms solution
