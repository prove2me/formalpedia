-- Prove2me | solution 1 for Helfgott.etaStar_expSum_norm_le_of_etaTwo_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T23:16:21.412502+00:00
-- url     : https://prove2.me/submissions/7e49a96a-12b7-4d37-a4d9-d625b1c90ac8

import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma

/-! Full direct Mellin transfer proof. Written by Codex. -/

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

open MeasureTheory Set
open scoped Interval

namespace Helfgott

lemma etaTwo_scaled_zero (T w : ℝ) (hT : 0 < T) (hw : w ∉ Icc T (4*T)) :
    etaTwo (T/w) = 0 := by
  by_cases hwp : 0 < w
  · apply etaTwo_eq_zero_of_not_mem
    intro h
    apply hw
    constructor
    · simpa using (div_le_iff₀ hwp).mp h.2
    · have hh := (le_div_iff₀ hwp).mp h.1
      nlinarith
  · have hh : T/w ≤ 0 := div_nonpos_of_nonneg_of_nonpos hT.le (le_of_not_gt hwp)
    simp [etaTwo, not_lt_of_ge hh]

lemma etaTwo_scaled_weight_continuous (T : ℝ) (hT : 0 < T) :
    Continuous (fun w : ℝ => etaTwo (T/w)/w) := by
  apply continuous_iff_continuousAt.mpr
  intro w
  by_cases hw : w = 0
  · subst w
    apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds hT] with x hx
    change x < T at hx
    rw [etaTwo_scaled_zero T x hT (by intro hm; linarith [hm.1]), zero_div]
  · have hc : ContinuousAt (fun x : ℝ => T/x) w := by fun_prop
    exact (etaTwo_continuous.continuousAt.comp hc).div continuousAt_id hw

lemma etaTwo_scaled_weight_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)/w) := by
  apply (etaTwo_scaled_weight_continuous T hT).integrable_of_hasCompactSupport
  apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
  intro w hw
  rw [etaTwo_scaled_zero T w hT hw,zero_div]

lemma etaTwo_scaled_lower (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (2*T)) :
    etaTwo (T/w) = 4 * (Real.log w - Real.log T) := by
  have hwp : 0 < w := lt_of_lt_of_le hT hw.1
  have hm : T/w ∈ Icc (1/2 : ℝ) 1 := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; simpa using hw.1
  rw [etaTwo_eq_upper _ hm, Real.log_div hT.ne' hwp.ne']
  ring

lemma etaTwo_scaled_upper (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc (2*T) (4*T)) :
    etaTwo (T/w) = 4 * (Real.log (4*T) - Real.log w) := by
  have hwp : 0 < w := by linarith [hw.1]
  have hm : T/w ∈ Icc (1/4 : ℝ) (1/2) := by
    constructor
    · apply (le_div_iff₀ hwp).mpr; linarith [hw.2]
    · apply (div_le_iff₀ hwp).mpr; linarith [hw.1]
  rw [etaTwo_eq_lower _ hm]
  rw [show 4*(T/w) = (4*T)/w by ring,
    Real.log_div (by positivity : 4*T ≠ 0) hwp.ne']

theorem etaTwo_scaled_log_mass (T : ℝ) (hT : 0 < T) :
    (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) = 4 * (Real.log 2)^2 := by
  have hf := etaTwo_scaled_weight_continuous T hT
  have hi (a b : ℝ) : IntervalIntegrable (fun w => etaTwo (T/w)/w) volume a b :=
    hf.intervalIntegrable _ _
  have hrestrict : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)/w) =
      ∫ w in T..4*T, etaTwo (T/w)/w := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (show Icc T (4*T) ⊆ Ioi (0 : ℝ) by intro w hw; exact lt_of_lt_of_le hT hw.1)
      (show ∀ w ∈ Ioi (0 : ℝ) \ Icc T (4*T), etaTwo (T/w)/w = 0 by
        intro w hw; rw [etaTwo_scaled_zero T w hT hw.2,zero_div])]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hrestrict, ← intervalIntegral.integral_add_adjacent_intervals (hi T (2*T)) (hi (2*T) (4*T))]
  have hlo : (∫ w in T..2*T, etaTwo (T/w)/w) =
      2*(Real.log (2*T)-Real.log T)^2 := by
    have heq : (∫ w in T..2*T, etaTwo (T/w)/w) =
        ∫ w in T..2*T, 4*(Real.log w-Real.log T)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      dsimp only
      rw [etaTwo_scaled_lower T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log w-Real.log T)/w)
        volume T (2*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc T (2*T)) :
        HasDerivAt (fun w : ℝ => 2*(Real.log w-Real.log T)^2)
          (4*(Real.log w-Real.log T)/w) w := by
      rw [Set.uIcc_of_le (by linarith : T ≤ 2*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').sub_const (Real.log T)).pow 2).const_mul 2 using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  have hhi : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
      2*(Real.log (4*T)-Real.log (2*T))^2 := by
    have heq : (∫ w in 2*T..4*T, etaTwo (T/w)/w) =
        ∫ w in 2*T..4*T, 4*(Real.log (4*T)-Real.log w)/w := by
      apply intervalIntegral.integral_congr
      intro w hw
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      dsimp only
      rw [etaTwo_scaled_upper T w hT hw]
    rw [heq]
    have hint : IntervalIntegrable (fun w : ℝ => 4*(Real.log (4*T)-Real.log w)/w)
        volume (2*T) (4*T) := by
      apply ContinuousOn.intervalIntegrable
      intro w hw
      have hwp : 0 < w := by
        rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
        linarith [hw.1]
      apply ContinuousAt.continuousWithinAt
      have hwn : w ≠ 0 := hwp.ne'
      fun_prop
    have hd (w : ℝ) (hw : w ∈ uIcc (2*T) (4*T)) :
        HasDerivAt (fun w : ℝ => -2*(Real.log (4*T)-Real.log w)^2)
          (4*(Real.log (4*T)-Real.log w)/w) w := by
      rw [Set.uIcc_of_le (by linarith : 2*T ≤ 4*T)] at hw
      have hwp : 0 < w := by linarith [hw.1]
      convert! (((Real.hasDerivAt_log hwp.ne').const_sub (Real.log (4*T))).pow 2).const_mul (-2) using 1 <;> simp <;> ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
    simp
  rw [hlo,hhi,Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hT.ne',
    Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hT.ne']
  have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]; norm_num
  rw [h4]
  ring

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

lemma phi_le (t : ℝ) : phi t ≤ 2 / Real.exp 1 := by
  have h := Real.mul_exp_neg_le_exp_neg_one (t^2/2)
  have he : Real.exp (-1 : ℝ) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [he] at h
  unfold phi
  have heq : -(t^2/2) = -(t^2)/2 := by ring
  rw [heq] at h
  calc
    t^2*Real.exp (-(t^2)/2) = 2*((t^2/2)*Real.exp (-(t^2)/2)) := by ring
    _ ≤ 2*(Real.exp 1)⁻¹ := mul_le_mul_of_nonneg_left h (by norm_num)
    _ = 2/Real.exp 1 := by ring

lemma mellin_etaTwo_phi_integrable (T : ℝ) (hT : 0 < T) :
    Integrable (fun w : ℝ => etaTwo (T/w)*phi w/w) := by
  have hphi : Continuous phi := by unfold phi; fun_prop
  have hc : Continuous (fun w : ℝ => (etaTwo (T/w)/w)*phi w) :=
    (etaTwo_scaled_weight_continuous T hT).mul hphi
  have hs : HasCompactSupport (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    apply HasCompactSupport.intro (K := Icc T (4*T)) isCompact_Icc
    intro w hw
    rw [etaTwo_scaled_zero T w hT hw,zero_div,zero_mul]
  have hh : Integrable (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := hc.integrable_of_hasCompactSupport hs
  have heq : (fun w : ℝ => etaTwo (T/w)*phi w/w) = (fun w : ℝ => (etaTwo (T/w)/w)*phi w) := by
    funext w; ring
  rw [heq]
  exact hh

lemma mellin_etaTwo_phi_nonneg (T : ℝ) : 0 ≤ mellinConv etaTwo phi T := by
  unfold mellinConv
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  exact div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) (le_of_lt hw)

lemma mellin_etaTwo_phi_le (T : ℝ) :
    mellinConv etaTwo phi T ≤ 8*(Real.log 2)^2/Real.exp 1 := by
  by_cases hT : 0 < T
  · have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul (2/Real.exp 1)).restrict
      (s := Ioi (0 : ℝ))
    have hbound : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), (2/Real.exp 1)*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have he := mul_le_mul_of_nonneg_left (phi_le w) (etaTwo_nonneg (T/w))
      have hh := div_le_div_of_nonneg_right he (le_of_lt hw)
      convert! hh using 1 <;> ring
    unfold mellinConv
    refine hbound.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    ring
  · have hz : mellinConv etaTwo phi T = 0 := by
      unfold mellinConv
      apply integral_eq_zero_of_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg (le_of_not_gt hT) (le_of_lt hw)
      simp [etaTwo,not_lt_of_ge hh]
    rw [hz]
    positivity

lemma mellin_etaTwo_phi_le_rational (T : ℝ) :
    mellinConv etaTwo phi T ≤ (707/500 : ℝ) := by
  apply (mellin_etaTwo_phi_le T).trans
  apply (div_le_iff₀ (Real.exp_pos 1)).mpr
  have hlog : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs : (Real.log 2)^2 ≤ (0.6931471808 : ℝ)^2 :=
    pow_le_pow_left₀ hlog Real.log_two_lt_d9.le 2
  nlinarith only [hs, Real.exp_one_gt_d9]

theorem etaStar_abs_le (t : ℝ) : |etaStar t| ≤ (707/500 : ℝ) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg (49*t))]
  exact mellin_etaTwo_phi_le_rational (49*t)

end Helfgott

open MeasureTheory Set Filter

namespace Helfgott

lemma mellin_etaTwo_phi_zero (T : ℝ) (hT : T ≤ 0) : mellinConv etaTwo phi T = 0 := by
  unfold mellinConv
  apply integral_eq_zero_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  have hh : T/w ≤ 0 := div_nonpos_of_nonpos_of_nonneg hT (le_of_lt hw)
  simp [etaTwo,not_lt_of_ge hh]

lemma phi_le_on_scaled_support (T w : ℝ) (hT : 0 < T) (hw : w ∈ Icc T (4*T)) :
    phi w ≤ (4*T)^2*Real.exp (-(T^2)/2) := by
  have hwp : 0 ≤ w := le_trans hT.le hw.1
  have hslo : T^2 ≤ w^2 := pow_le_pow_left₀ hT.le hw.1 2
  have hshi : w^2 ≤ (4*T)^2 := pow_le_pow_left₀ hwp hw.2 2
  have he : Real.exp (-(w^2)/2) ≤ Real.exp (-(T^2)/2) :=
    Real.exp_le_exp.mpr (by linarith)
  unfold phi
  exact mul_le_mul hshi he (Real.exp_pos _).le (sq_nonneg _)

theorem mellin_etaTwo_phi_gaussian_decay (T : ℝ) :
    mellinConv etaTwo phi T ≤ 64*(Real.log 2)^2*T^2*Real.exp (-(T^2)/2) := by
  by_cases hT : 0 < T
  · let C : ℝ := (4*T)^2*Real.exp (-(T^2)/2)
    have hi := (mellin_etaTwo_phi_integrable T hT).restrict (s := Ioi (0 : ℝ))
    have hg := ((etaTwo_scaled_weight_integrable T hT).const_mul C).restrict (s := Ioi (0 : ℝ))
    have hb : (∫ w in Ioi (0 : ℝ), etaTwo (T/w)*phi w/w) ≤
        ∫ w in Ioi (0 : ℝ), C*(etaTwo (T/w)/w) := by
      apply integral_mono_ae hi hg
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      by_cases hm : w ∈ Icc T (4*T)
      · have he := mul_le_mul_of_nonneg_left (phi_le_on_scaled_support T w hT hm)
          (etaTwo_nonneg (T/w))
        have hh := div_le_div_of_nonneg_right he hw.le
        convert! hh using 1 <;> dsimp [C] <;> ring
      · rw [etaTwo_scaled_zero T w hT hm]
        simp
    unfold mellinConv
    refine hb.trans_eq ?_
    rw [integral_const_mul,etaTwo_scaled_log_mass T hT]
    dsimp [C]
    ring
  · rw [mellin_etaTwo_phi_zero T (le_of_not_gt hT)]
    positivity

theorem etaStar_abs_le_gaussian (t : ℝ) :
    |etaStar t| ≤ 64*(Real.log 2)^2*(49*t)^2*Real.exp (-((49*t)^2)/2) := by
  unfold etaStar
  rw [abs_of_nonneg (mellin_etaTwo_phi_nonneg _)]
  exact mellin_etaTwo_phi_gaussian_decay (49*t)

end Helfgott

namespace Helfgott

lemma vonMangoldt_le_nat (n : ℕ) : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) := by
  by_cases hn : n = 0
  · subst n; simp
  · have hp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hl := Real.log_le_sub_one_of_pos hp
    exact ArithmeticFunction.vonMangoldt_le_log.trans (by linarith)

theorem etaStar_vonMangoldt_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * etaStar ((n : ℝ)/x)) := by
  let C : ℝ := 64*(Real.log 2)^2*(49/x)^2
  let r : ℝ := (49/x)^2/2
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hg : Summable (fun n : ℕ => C*((n : ℝ)^3*Real.exp (-r*n))) :=
    (Real.summable_pow_mul_exp_neg_nat_mul 3 hr).mul_left C
  apply hg.of_nonneg_of_le
  · intro n
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (mellin_etaTwo_phi_nonneg (49*((n : ℝ)/x)))
  · intro n
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    have hn2 : (n : ℝ) ≤ (n : ℝ)^2 := by
      have h : (n : ℝ) ≤ (n : ℝ)*(n : ℝ) := by exact_mod_cast Nat.le_mul_self n
      nlinarith
    have he : Real.exp (-r*(n : ℝ)^2) ≤ Real.exp (-r*n) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have htail : etaStar ((n : ℝ)/x) ≤ C*(n : ℝ)^2*Real.exp (-r*(n : ℝ)^2) := by
      apply (le_abs_self _).trans
      apply (etaStar_abs_le_gaussian ((n : ℝ)/x)).trans_eq
      have heq : 49*((n : ℝ)/x) = (49/x)*(n : ℝ) := by ring
      rw [heq,mul_pow]
      have heqexp : -((49/x)^2*(n : ℝ)^2)/2 = -r*(n : ℝ)^2 := by dsimp [r]; ring
      rw [heqexp]
      dsimp [C]
      ring
    calc
      ArithmeticFunction.vonMangoldt n * etaStar ((n : ℝ)/x) ≤
          (n : ℝ)*etaStar ((n : ℝ)/x) := mul_le_mul_of_nonneg_right (vonMangoldt_le_nat n)
            (mellin_etaTwo_phi_nonneg (49*((n : ℝ)/x)))
      _ ≤ (n : ℝ)*(C*(n : ℝ)^2*Real.exp (-r*(n : ℝ)^2)) := mul_le_mul_of_nonneg_left htail hn
      _ ≤ (n : ℝ)*(C*(n : ℝ)^2*Real.exp (-r*n)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (mul_nonneg hC (sq_nonneg _))) hn
      _ = C*((n : ℝ)^3*Real.exp (-r*n)) := by ring

lemma etaStar_vonMangoldt_complex_summable (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (etaStar ((n : ℝ)/x) : ℂ)) := by
  have h := Complex.summable_ofReal.mpr (etaStar_vonMangoldt_summable x hx)
  simpa only [Complex.ofReal_mul] using h

end Helfgott

open MeasureTheory Set ENNReal
open scoped BigOperators

namespace Helfgott

private lemma integrable_complex_tsum {F : ℕ → ℝ → ℂ} {μ : Measure ℝ}
    (hi : ∀ n, Integrable (F n) μ)
    (hs : Summable (fun n => ∫ w, ‖F n w‖ ∂μ)) :
    Integrable (fun w => ∑' n, F n w) μ := by
  refine ⟨AEStronglyMeasurable.tsum (fun n => (hi n).1), ?_⟩
  have hne : (∑' n, ∫⁻ w, ‖F n w‖ₑ ∂μ) ≠ ⊤ := by
    have heq (n : ℕ) : (∫⁻ w, ‖F n w‖ₑ ∂μ) =
        ‖∫ w, ‖F n w‖ ∂μ‖ₑ := by
      dsimp [enorm]
      rw [lintegral_coe_eq_integral _ (hi n).norm, coe_nnreal_eq, coe_nnnorm,
        Real.norm_of_nonneg (integral_nonneg (fun w => norm_nonneg (F n w)))]
      simp only [coe_nnnorm]
    rw [funext heq]
    exact ENNReal.tsum_coe_ne_top_iff_summable.2 (NNReal.summable_coe.1 hs.abs)
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt ?_ hne.lt_top
  calc
    (∫⁻ w, ‖∑' n, F n w‖ₑ ∂μ) ≤ ∫⁻ w, ∑' n, ‖F n w‖ₑ ∂μ :=
      lintegral_mono (fun w => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ w, ‖F n w‖ₑ ∂μ :=
      lintegral_tsum (fun n => (hi n).1.enorm)

private lemma etaStar_term_integrable (x : ℝ) (hx : 0 < x) (n : ℕ) :
    IntegrableOn (fun w : ℝ => etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) (Ioi 0) := by
  by_cases hn : n = 0
  · subst n
    simpa [etaTwo] using (integrableOn_zero : IntegrableOn (fun _ : ℝ => (0 : ℝ)) (Ioi 0))
  · exact (mellin_etaTwo_phi_integrable _ (by positivity)).restrict

private lemma mellin_fourier_norm (x : ℝ) (n : ℕ) (α : AddCircle (1 : ℝ))
    (w : ℝ) (hw : 0 < w) :
    ‖((ArithmeticFunction.vonMangoldt n *
      (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ)*fourier (n : ℤ) α‖ =
      ArithmeticFunction.vonMangoldt n * (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) := by
  have hn : 0 ≤ ArithmeticFunction.vonMangoldt n *
      (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) := by
    exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (div_nonneg (mul_nonneg (etaTwo_nonneg _) (phi_nonneg _)) hw.le)
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hn]
  have hf : ‖fourier (n : ℤ) α‖ = 1 := by simp [fourier_apply, Circle.norm_coe]
  rw [hf,mul_one]

theorem etaStar_mellin_expSum_transfer (x : ℝ) (hx : 0 < x)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α =
      ∫ w in Ioi (0 : ℝ),
        expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
          etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α * ((phi w/w : ℝ) : ℂ) := by
  let F : ℕ → ℝ → ℂ := fun n w =>
    ((ArithmeticFunction.vonMangoldt n *
      (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ)*fourier (n : ℤ) α
  have hi : ∀ n, IntegrableOn (F n) (Ioi (0 : ℝ)) := by
    intro n
    exact (((etaStar_term_integrable x hx n).const_mul
      (ArithmeticFunction.vonMangoldt n)).ofReal).mul_const (fourier (n : ℤ) α)
  have hnorm (n : ℕ) : (∫ w in Ioi (0 : ℝ), ‖F n w‖) =
      ArithmeticFunction.vonMangoldt n * etaStar ((n : ℝ)/x) := by
    calc
      _ = ∫ w in Ioi (0 : ℝ), ArithmeticFunction.vonMangoldt n *
          (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        exact mellin_fourier_norm x n α w hw
      _ = _ := by rw [integral_const_mul]; rfl
  have hs : Summable (fun n => ∫ w in Ioi (0 : ℝ), ‖F n w‖) := by
    simp_rw [hnorm]
    exact etaStar_vonMangoldt_summable x hx
  have hterm (n : ℕ) : (∫ w in Ioi (0 : ℝ), F n w) =
      ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)*fourier (n : ℤ) α := by
    change (∫ w in Ioi (0 : ℝ),
      ((ArithmeticFunction.vonMangoldt n *
        (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ)*fourier (n : ℤ) α) = _
    rw [integral_mul_const]
    have hof : (∫ w in Ioi (0 : ℝ),
        ((ArithmeticFunction.vonMangoldt n *
          (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ)) =
        ((∫ w in Ioi (0 : ℝ), ArithmeticFunction.vonMangoldt n *
          (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ) := integral_ofReal
    rw [hof,integral_const_mul]
    rfl
  calc
    _ = ∑' n, ∫ w in Ioi (0 : ℝ), F n w := by
      unfold expSum
      exact tsum_congr (fun n => (hterm n).symm)
    _ = ∫ w in Ioi (0 : ℝ), ∑' n, F n w :=
      integral_tsum_of_summable_integral_norm hi hs
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
      unfold expSum
      rw [← tsum_mul_right]
      apply tsum_congr
      intro n
      have he : (49*((n : ℝ)/x))/w = (n : ℝ)/(x*w/49) := by
        field_simp
      dsimp [F]
      rw [he]
      push_cast
      ring

theorem etaStar_mellin_expSum_integrable (x : ℝ) (hx : 0 < x)
    (α : AddCircle (1 : ℝ)) :
    IntegrableOn (fun w : ℝ =>
      expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α * ((phi w/w : ℝ) : ℂ)) (Ioi 0) := by
  let F : ℕ → ℝ → ℂ := fun n w =>
    ((ArithmeticFunction.vonMangoldt n *
      (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) : ℝ) : ℂ)*fourier (n : ℤ) α
  have hi : ∀ n, IntegrableOn (F n) (Ioi (0 : ℝ)) := by
    intro n
    exact (((etaStar_term_integrable x hx n).const_mul
      (ArithmeticFunction.vonMangoldt n)).ofReal).mul_const (fourier (n : ℤ) α)
  have hnorm (n : ℕ) : (∫ w in Ioi (0 : ℝ), ‖F n w‖) =
      ArithmeticFunction.vonMangoldt n * etaStar ((n : ℝ)/x) := by
    calc
      _ = ∫ w in Ioi (0 : ℝ), ArithmeticFunction.vonMangoldt n *
          (etaTwo ((49*((n : ℝ)/x))/w)*phi w/w) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
        exact mellin_fourier_norm x n α w hw
      _ = _ := by rw [integral_const_mul]; rfl
  have hs : Summable (fun n => ∫ w in Ioi (0 : ℝ), ‖F n w‖) := by
    simp_rw [hnorm]
    exact etaStar_vonMangoldt_summable x hx
  apply (integrable_complex_tsum hi hs).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  unfold expSum
  rw [← tsum_mul_right]
  apply tsum_congr
  intro n
  have he : (49*((n : ℝ)/x))/w = (n : ℝ)/(x*w/49) := by field_simp
  dsimp [F]
  rw [he]
  push_cast
  ring

theorem etaStar_mellin_expSum_norm_bound (x : ℝ) (hx : 0 < x)
    (α : AddCircle (1 : ℝ)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      ∫ w in Ioi (0 : ℝ),
        ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
          etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w) := by
  rw [etaStar_mellin_expSum_transfer x hx α]
  refine (norm_integral_le_integral_norm _).trans_eq ?_
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (div_nonneg (phi_nonneg _) hw.le)]

theorem etaStar_mellin_expSum_norm_integrable (x : ℝ) (hx : 0 < x)
    (α : AddCircle (1 : ℝ)) :
    IntegrableOn (fun w : ℝ =>
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w)) (Ioi 0) := by
  apply (etaStar_mellin_expSum_integrable x hx α).norm.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
    (div_nonneg (phi_nonneg _) hw.le)]

end Helfgott

open MeasureTheory Set
open scoped BigOperators

namespace Helfgott

lemma etaTwo_vonMangoldt_eq_zero (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 ⌊y⌋₊) :
    ArithmeticFunction.vonMangoldt n * etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n; simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : ⌊y⌋₊ < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have h := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_vonMangoldt_summable (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * etaTwo ((n : ℝ)/y)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 ⌊y⌋₊)
  exact etaTwo_vonMangoldt_eq_zero y hy

theorem etaTwo_expSum_norm_le (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α‖ ≤
      15*y := by
  unfold expSum
  rw [tsum_eq_sum (s := Finset.Ioc 0 ⌊y⌋₊) (fun n hn => by
    dsimp only
    rw [etaTwo_vonMangoldt_eq_zero y hy n hn]; simp)]
  have hnorm (n : ℕ) :
      ‖((ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ =
        ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (etaTwo_nonneg _))]
    have hf : ‖fourier (n : ℤ) α‖ = 1 := by simp [fourier_apply,Circle.norm_coe]
    rw [hf,mul_one]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊,
        ‖((ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n*etaTwo ((n : ℝ)/y) := by
      simp_rw [hnorm]
    _ ≤ ∑ n ∈ Finset.Ioc 0 ⌊y⌋₊, ArithmeticFunction.vonMangoldt n*(4*Real.log 2) := by
      apply Finset.sum_le_sum
      intro n hn
      exact mul_le_mul_of_nonneg_left (etaTwo_le _) ArithmeticFunction.vonMangoldt_nonneg
    _ = (4*Real.log 2)*Chebyshev.psi y := by rw [← Finset.sum_mul]; unfold Chebyshev.psi; ring
    _ ≤ (4*Real.log 2)*((Real.log 4+4)*y) := by
      apply mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self hy.le)
      positivity
    _ ≤ 15*y := by
      have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hl := Real.log_two_lt_d9
      have h4 : Real.log (4 : ℝ) = 2*Real.log 2 := by
        rw [show (4 : ℝ) = 2^2 by norm_num,Real.log_pow]; norm_num
      rw [h4]
      have hc : (4*Real.log 2)*(2*Real.log 2+4) ≤ (15 : ℝ) := by nlinarith
      simpa [mul_assoc] using mul_le_mul_of_nonneg_right hc hy.le

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

namespace Helfgott

lemma phi_small_mass (a : ℝ) (ha : 0 < a) :
    (∫ w in Ioc (0 : ℝ) a, phi w) ≤ a^3/3 := by
  have hc : Continuous phi := by unfold phi; fun_prop
  have hp : Continuous (fun w : ℝ => w^2) := by fun_prop
  have hip : IntervalIntegrable phi volume 0 a := hc.intervalIntegrable 0 a
  have hjp : IntervalIntegrable (fun w : ℝ => w^2) volume 0 a := hp.intervalIntegrable 0 a
  have hi := hip.1
  have hj := hjp.1
  calc
    _ ≤ ∫ w in Ioc (0 : ℝ) a, w^2 := by
      apply integral_mono_ae hi hj
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with w hw
      unfold phi
      have he : Real.exp (-(w^2)/2) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        nlinarith [sq_nonneg w]
      simpa using mul_le_mul_of_nonneg_left he (sq_nonneg w)
    _ = a^3/3 := by
      rw [← intervalIntegral.integral_of_le ha.le,integral_pow]
      norm_num

theorem etaStar_expSum_norm_le_of_etaTwo_bound (x a B : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hB : 0 ≤ B) (α : AddCircle (1 : ℝ))
    (hcompact : ∀ w : ℝ, a ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ ≤ B*(x*w/49)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      (x/49)*(B*Real.sqrt (Real.pi/2)+5*a^3) := by
  let f : ℝ → ℝ := fun w =>
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
      etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w)
  let g : ℝ → ℝ := fun w =>
    (B*(x/49))*phi w + (15*(x/49))*(Ioc (0 : ℝ) a).indicator phi w
  have hphi : IntegrableOn phi (Ioi (0 : ℝ)) := by
    simpa using phi_moment_integrable 0
  have hsmall : IntegrableOn ((Ioc (0 : ℝ) a).indicator phi) (Ioi (0 : ℝ)) :=
    hphi.indicator measurableSet_Ioc
  have hg : IntegrableOn g (Ioi (0 : ℝ)) :=
    (hphi.const_mul _).add (hsmall.const_mul _)
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := etaStar_mellin_expSum_norm_integrable x hx α
  have hle : (∫ w in Ioi (0 : ℝ), f w) ≤ ∫ w in Ioi (0 : ℝ), g w := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hwp : 0 < w := hw
    have hweight : 0 ≤ phi w/w := div_nonneg (phi_nonneg _) hwp.le
    have hp : 0 ≤ (B*(x/49))*phi w :=
      mul_nonneg (mul_nonneg hB (div_nonneg hx.le (by norm_num))) (phi_nonneg w)
    by_cases hwa : w ≤ a
    · have hb := etaTwo_expSum_norm_le (x*w/49) (by positivity) α
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : (15*(x*w/49))*(phi w/w) = (15*(x/49))*phi w := by
        field_simp
      dsimp [f,g]
      rw [indicator_of_mem (show w ∈ Ioc (0 : ℝ) a from ⟨hwp,hwa⟩) phi]
      rw [he] at hh
      linarith
    · have hb := hcompact w (le_of_lt (lt_of_not_ge hwa))
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : (B*(x*w/49))*(phi w/w) = (B*(x/49))*phi w := by
        field_simp
      dsimp [f,g]
      rw [indicator_of_notMem (show w ∉ Ioc (0 : ℝ) a from fun h => hwa h.2) phi]
      rw [he] at hh
      simpa using hh
  have hsmall_eq : (∫ w in Ioi (0 : ℝ), (Ioc (0 : ℝ) a).indicator phi w) =
      ∫ w in Ioc (0 : ℝ) a, phi w := by
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset (show Ioc (0 : ℝ) a ⊆ Ioi 0 from fun w hw => hw.1)]
  have hgeq : (∫ w in Ioi (0 : ℝ), g w) =
      (B*(x/49))*Real.sqrt (Real.pi/2) + (15*(x/49))*(∫ w in Ioc (0 : ℝ) a, phi w) := by
    rw [show g = (fun w => (B*(x/49))*phi w +
      (15*(x/49))*(Ioc (0 : ℝ) a).indicator phi w) from rfl]
    rw [integral_add (hphi.const_mul _) (hsmall.const_mul _),
      integral_const_mul,integral_const_mul,phi_mass,hsmall_eq]
  calc
    _ ≤ ∫ w in Ioi (0 : ℝ), f w := etaStar_mellin_expSum_norm_bound x hx α
    _ ≤ ∫ w in Ioi (0 : ℝ), g w := hle
    _ = (B*(x/49))*Real.sqrt (Real.pi/2) +
        (15*(x/49))*(∫ w in Ioc (0 : ℝ) a, phi w) := hgeq
    _ ≤ (B*(x/49))*Real.sqrt (Real.pi/2) + (15*(x/49))*(a^3/3) := by
      gcongr
      exact phi_small_mass a ha
    _ = _ := by ring

end Helfgott

open Helfgott

theorem solution (x a B : ℝ) (hx : 0 < x) (ha : 0 < a) (hB : 0 ≤ B)
    (α : AddCircle (1 : ℝ))
    (hcompact : ∀ w : ℝ, a ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ ≤ B*(x*w/49)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      (x/49)*(B*Real.sqrt (Real.pi/2)+5*a^3) :=
  Helfgott.etaStar_expSum_norm_le_of_etaTwo_bound x a B hx ha hB α hcompact

#print axioms solution
