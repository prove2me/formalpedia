-- Prove2me | solution 1 for Helfgott.etaStar_vonMangoldt_summable
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-04T22:23:52.84048+00:00
-- url     : https://prove2.me/submissions/e676e885-6e4e-4896-9b2d-34425ab17cb6

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

/-! Full Gaussian decay and actual von Mangoldt sum convergence proof. Written by Codex. -/

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

theorem solution (x : ℝ) (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n * Helfgott.etaStar ((n : ℝ)/x)) :=
  Helfgott.etaStar_vonMangoldt_summable x hx

#print axioms solution
