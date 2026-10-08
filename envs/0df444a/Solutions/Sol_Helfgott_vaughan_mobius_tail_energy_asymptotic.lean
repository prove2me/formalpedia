-- Prove2me | solution 1 for Helfgott.vaughan_mobius_tail_energy_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-10-06T13:20:15.252997+00:00
-- url     : https://prove2.me/submissions/99a108e9-01e3-4152-b175-cc974b032c60

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic
import Definitions.Def_Helfgott_VaughanData
import Definitions.Def_Helfgott_Smoothings
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.Factorial.Basic

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

theorem finite_divisor_weight_square_energy (M U : ℕ) (c : ℕ → ℝ) :
    (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ) := by
  have hpoint (n : ℕ) : (∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2 =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        if Nat.lcm d e ∣ n then c d*c e else 0 := by
    rw [pow_two,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    by_cases hdvd : d ∣ n <;> by_cases hevd : e ∣ n <;>
      simp [hdvd,hevd,Nat.lcm_dvd_iff]
  simp_rw [hpoint]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [←Finset.sum_filter]
  simp only [Finset.sum_const,smul_eq_mul]
  have hi : (Finset.Icc 1 M).filter (fun n => Nat.lcm d e ∣ n) =
      (Finset.Ioc 0 M).filter (fun n => Nat.lcm d e ∣ n) := by
    congr 1
  rw [hi,Nat.Ioc_filter_dvd_card_eq_div]
  ring

end Helfgott
end

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
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
open ArithmeticFunction MeasureTheory Set Finset
open scoped BigOperators Classical

namespace Helfgott

lemma arithmeticCutoff_add_tail (U : ℕ) (f : ArithmeticFunction ℝ) :
    arithmeticCutoff U f+arithmeticTail U f = f := by
  unfold arithmeticTail
  abel

theorem vaughan_arithmetic_identity (U V : ℕ) :
    (vonMangoldt : ArithmeticFunction ℝ) = vaughanTypeOne U-vaughanCorrection U V+
      arithmeticCutoff V vonMangoldt+vaughanTypeTwo U V := by
  let ml : ArithmeticFunction ℝ := arithmeticCutoff U (moebius : ArithmeticFunction ℝ)
  let mh : ArithmeticFunction ℝ := arithmeticTail U (moebius : ArithmeticFunction ℝ)
  let ll : ArithmeticFunction ℝ := arithmeticCutoff V vonMangoldt
  let lh : ArithmeticFunction ℝ := arithmeticTail V vonMangoldt
  have hm : ml+mh = (moebius : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail U _
  have hl : ll+lh = (vonMangoldt : ArithmeticFunction ℝ) := arithmeticCutoff_add_tail V _
  have hz : (ml+mh)*(zeta : ArithmeticFunction ℝ) = 1 := by
    rw [hm,coe_moebius_mul_coe_zeta]
  change (vonMangoldt : ArithmeticFunction ℝ) = ml*log-ml*ll*zeta+ll+mh*lh*zeta
  rw [←vonMangoldt_mul_zeta,←hl]
  calc
    ll+lh = ll+((ml+mh)*zeta)*lh := by rw [hz,one_mul]
    _ = _ := by ring

lemma etaTwo_arithmetic_eq_zero (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) (n : ℕ)
    (hn : n ∉ Finset.Ioc 0 (Nat.floor y)) : f n*etaTwo ((n : ℝ)/y) = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
    have hfloor : Nat.floor y < n := by simpa [Finset.mem_Ioc,hnpos] using hn
    have hlarge : y < (n : ℝ) := Nat.lt_of_floor_lt hfloor
    have hz : etaTwo ((n : ℝ)/y) = 0 := by
      apply etaTwo_eq_zero_of_not_mem
      intro hm
      have hh := (div_le_iff₀ hy).mp hm.2
      linarith
    rw [hz,mul_zero]

lemma etaTwo_arithmetic_summable (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y) :
    Summable (fun n : ℕ => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) := by
  apply summable_of_ne_finset_zero (s := Finset.Ioc 0 (Nat.floor y))
  intro n hn
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

lemma etaTwo_arithmetic_expSum_finite (f : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ n ∈ Finset.Ioc 0 (Nat.floor y), ((f n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)*fourier (n : ℤ) α := by
  unfold expSum
  apply tsum_eq_sum
  intro n hn
  dsimp only
  rw [etaTwo_arithmetic_eq_zero f y hy n hn]
  simp

theorem vaughan_etaTwo_expSum_identity (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      expSum (fun n => ((vaughanTypeOne U n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α-
      expSum (fun n => ((vaughanCorrection U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((arithmeticCutoff V vonMangoldt n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α+
      expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α := by
  simp_rw [etaTwo_arithmetic_expSum_finite _ y hy α]
  rw [←Finset.sum_sub_distrib,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n _
  have hn := congrArg (fun f : ArithmeticFunction ℝ => f n) (vaughan_arithmetic_identity U V)
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply] at hn
  rw [hn]
  push_cast
  ring

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1000000
open Finset
open scoped BigOperators Classical

namespace Helfgott

theorem truncated_divisor_sum_complex (B : ℕ) (F : ℕ → ℕ → ℂ) :
    (∑ q ∈ Icc 1 B, ∑ d ∈ q.divisors, F d (q/d)) =
      ∑ d ∈ Icc 1 B, ∑ r ∈ Icc 1 (B/d), F d r := by
  classical
  rw [← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.2 (i.1/i.2)),
    ← sum_sigma (f := fun i : Σ _ : ℕ, ℕ => F i.1 i.2)]
  refine sum_bij (fun i _ => (⟨i.2, i.1/i.2⟩ : Σ _ : ℕ, ℕ)) ?_ ?_ ?_ ?_
  · intro i hi
    rcases mem_sigma.mp hi with ⟨hq, hd⟩
    have hdq := (Nat.mem_divisors.mp hd).1
    have hqpos : 0 < i.1 := (mem_Icc.mp hq).1
    have hdpos := Nat.pos_of_dvd_of_pos hdq hqpos
    apply mem_sigma.mpr
    constructor
    · exact mem_Icc.mpr ⟨hdpos, (Nat.le_of_dvd hqpos hdq).trans (mem_Icc.mp hq).2⟩
    · apply mem_Icc.mpr
      exact ⟨Nat.div_pos (Nat.le_of_dvd hqpos hdq) hdpos,
        Nat.div_le_div_right (mem_Icc.mp hq).2⟩
  · intro i hi j hj he
    rcases mem_sigma.mp hi with ⟨_, hdi⟩
    rcases mem_sigma.mp hj with ⟨_, hdj⟩
    have hd : i.2 = j.2 := congrArg Sigma.fst he
    have hr : i.1/i.2 = j.1/j.2 := congrArg (fun k : Σ _ : ℕ, ℕ => k.2) he
    have hq : i.1 = j.1 := by
      calc
        i.1 = i.2*(i.1/i.2) := (Nat.mul_div_cancel' (Nat.mem_divisors.mp hdi).1).symm
        _ = j.2*(j.1/j.2) := by rw [hr, hd]
        _ = j.1 := Nat.mul_div_cancel' (Nat.mem_divisors.mp hdj).1
    exact Sigma.ext hq (by simpa using hd)
  · intro j hj
    rcases mem_sigma.mp hj with ⟨hd, hr⟩
    have hdpos : 0 < j.1 := (mem_Icc.mp hd).1
    have hrpos : 0 < j.2 := (mem_Icc.mp hr).1
    have hprod : j.1*j.2 ≤ B := by
      calc
        _ ≤ j.1*(B/j.1) := Nat.mul_le_mul_left j.1 (mem_Icc.mp hr).2
        _ ≤ B := by simpa only [mul_comm] using Nat.div_mul_le_self B j.1
    refine ⟨⟨j.1*j.2, j.1⟩, mem_sigma.mpr ⟨mem_Icc.mpr ⟨Nat.mul_pos hdpos hrpos, hprod⟩,
      Nat.mem_divisors.mpr ⟨Nat.dvd_mul_right j.1 j.2, (Nat.mul_pos hdpos hrpos).ne'⟩⟩, ?_⟩
    change (⟨j.1, (j.1*j.2)/j.1⟩ : Σ _ : ℕ, ℕ) = j
    rw [Nat.mul_div_right j.2 hdpos]
  · intro _ _
    rfl

lemma etaTwo_convolution_expSum_hyperbola (f g : ArithmeticFunction ℝ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => (((f*g) n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc 1 (Nat.floor y), ∑ m ∈ Finset.Icc 1 (Nat.floor (y/(d : ℝ))),
        ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have hindex : Finset.Ioc 0 (Nat.floor y) = Finset.Icc 1 (Nat.floor y) := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    omega
  let F (d m : ℕ) : ℂ :=
    ((f d*g m*etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α
  rw [etaTwo_arithmetic_expSum_finite _ y hy α,hindex]
  have hinner (k : ℕ) :
      (((f*g) k*etaTwo ((k : ℝ)/y) : ℝ) : ℂ)*fourier (k : ℤ) α =
      ∑ d ∈ k.divisors, F d (k/d) := by
    rw [ArithmeticFunction.mul_apply,Nat.sum_divisorsAntidiagonal (fun a b => f a*g b)]
    rw [Complex.ofReal_mul,Complex.ofReal_sum,Finset.sum_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro d hd
    have he : d*(k/d) = k := Nat.mul_div_cancel' (Nat.mem_divisors.mp hd).1
    simp only [F,he,Complex.ofReal_mul]
  simp_rw [hinner]
  rw [truncated_divisor_sum_complex]
  apply Finset.sum_congr rfl
  intro d _
  rw [Nat.floor_div_natCast]

lemma arithmeticTail_zero_of_le (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : n ≤ U) :
    arithmeticTail U f n = 0 := by
  change f n-(if n ≤ U then f n else 0) = 0
  simp [hn]

lemma arithmeticTail_self_of_gt (U n : ℕ) (f : ArithmeticFunction ℝ) (hn : U < n) :
    arithmeticTail U f n = f n := by
  change f n-(if n ≤ U then f n else 0) = f n
  simp [not_le_of_gt hn]

lemma vaughan_bilinear_coefficient_zero (U n : ℕ) (hn : n ≤ U) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n = 0 := by
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  apply Finset.sum_eq_zero
  intro d hd
  have hdn : d ≤ n := Nat.le_of_dvd
    (Nat.pos_of_ne_zero (Nat.mem_divisors.mp hd).2) (Nat.mem_divisors.mp hd).1
  exact arithmeticTail_zero_of_le U d _ (hdn.trans hn)

lemma vaughan_bilinear_coefficient_short_moebius (U n : ℕ) (hn : n ≠ 1) :
    (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n =
      -(∑ d ∈ n.divisors.filter (fun d => d ≤ U), ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  have he : arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta =
      1-arithmeticCutoff U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta := by
    unfold arithmeticTail
    rw [sub_mul,ArithmeticFunction.coe_moebius_mul_coe_zeta]
  rw [he]
  simp only [sub_eq_add_neg,ArithmeticFunction.add_apply,ArithmeticFunction.neg_apply,
    ArithmeticFunction.one_apply_ne hn,zero_add]
  rw [ArithmeticFunction.coe_mul_zeta_apply,Finset.sum_filter]
  congr 1

lemma sum_Icc_of_low_zero (F : ℕ → ℂ) (U B : ℕ) (hF : ∀ n ≤ U, F n = 0) :
    (∑ n ∈ Finset.Icc 1 B, F n) = ∑ n ∈ Finset.Icc (U+1) B, F n := by
  symm
  apply Finset.sum_subset
  · intro n hn
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    exact Finset.mem_Icc.mpr ⟨by omega,h2⟩
  · intro n hn hnot
    rcases Finset.mem_Icc.mp hn with ⟨h1,h2⟩
    have hnU : n ≤ U := by
      by_contra h
      exact hnot (Finset.mem_Icc.mpr ⟨by omega,h2⟩)
    exact hF n hnU

theorem vaughan_typeTwo_bilinear_expSum (U V : ℕ) (y : ℝ) (hy : 0 < y)
    (α : AddCircle (1 : ℝ)) :
    expSum (fun n => ((vaughanTypeTwo U V n*etaTwo ((n : ℝ)/y) : ℝ) : ℂ)) α =
      ∑ d ∈ Finset.Icc (V+1) (Nat.floor y), ∑ m ∈ Finset.Icc (U+1) (Nat.floor (y/(d : ℝ))),
        ((ArithmeticFunction.vonMangoldt d*
          (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m*
          etaTwo (((d*m : ℕ) : ℝ)/y) : ℝ) : ℂ)*fourier ((d*m : ℕ) : ℤ) α := by
  have he : vaughanTypeTwo U V = arithmeticTail V ArithmeticFunction.vonMangoldt*
      (arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) := by
    unfold vaughanTypeTwo
    ring
  rw [he,etaTwo_convolution_expSum_hyperbola _ _ y hy α]
  rw [sum_Icc_of_low_zero (U := V)]
  · apply Finset.sum_congr rfl
    intro d hd
    rw [sum_Icc_of_low_zero (U := U)]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [arithmeticTail_self_of_gt V d _ (by have := (Finset.mem_Icc.mp hd).1;omega)]
    · intro m hm
      rw [vaughan_bilinear_coefficient_zero U m hm]
      simp
  · intro d hd
    rw [arithmeticTail_zero_of_le V d _ hd]
    simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott

lemma short_moebius_divisor_sum (U n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors.filter (fun d => d ≤ U),((ArithmeticFunction.moebius d : ℤ) : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
  have he : n.divisors.filter (fun d => d ≤ U) = (Finset.Icc 1 U).filter (fun d => d ∣ n) := by
    ext d
    simp only [Finset.mem_filter,Nat.mem_divisors,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hd,hn0⟩,hdU⟩
      exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn,hdU⟩,hd⟩
    · rintro ⟨⟨hdpos,hdU⟩,hd⟩
      exact ⟨⟨hd,hn.ne'⟩,hdU⟩
  rw [he,Finset.sum_filter]

lemma vaughan_mobius_energy_pointwise (U n : ℕ) (hU : 1 ≤ U) (hn : 0 < n) :
    ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) n)^2 =
      (∑ d ∈ Finset.Icc 1 U,if d ∣ n then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
      (if n=1 then 1 else 0) := by
  by_cases hn1 : n=1
  · subst n
    rw [vaughan_bilinear_coefficient_zero U 1 hU]
    have hs : (∑ d ∈ Finset.Icc 1 U,if d ∣ 1 then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0) = 1 := by
      rw [←short_moebius_divisor_sum U 1 (by norm_num)]
      rw [Nat.divisors_one,Finset.filter_singleton]
      simp [hU]
    rw [hs]
    norm_num
  · rw [vaughan_bilinear_coefficient_short_moebius U n hn1,short_moebius_divisor_sum U n hn,if_neg hn1]
    ring

theorem vaughan_mobius_tail_square_energy (U M : ℕ) (hU : 1 ≤ U) :
    (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)*
        ((M/(Nat.lcm d e) : ℕ) : ℝ))-(if 1 ≤ M then 1 else 0) := by
  have hs : (∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) := by
    apply Finset.sum_subset
    · intro m hm
      exact Finset.mem_Icc.mpr ⟨by have := (Finset.mem_Icc.mp hm).1;omega,(Finset.mem_Icc.mp hm).2⟩
    · intro m hm hnot
      have hmU : m ≤ U := by
        have hml := (Finset.mem_Icc.mp hm).1
        have hmh := (Finset.mem_Icc.mp hm).2
        have hnot' : ¬(U+1 ≤ m ∧ m ≤ M) := by simpa only [Finset.mem_Icc] using hnot
        omega
      rw [vaughan_bilinear_coefficient_zero U m hmU]
      simp
  rw [hs]
  have he : (∑ m ∈ Finset.Icc 1 M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2) =
      ∑ m ∈ Finset.Icc 1 M,
        ((∑ d ∈ Finset.Icc 1 U,if d ∣ m then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0)^2-
          (if m=1 then 1 else 0)) := by
    apply Finset.sum_congr rfl
    intro m hm
    exact vaughan_mobius_energy_pointwise U m hU (Finset.mem_Icc.mp hm).1
  rw [he,Finset.sum_sub_distrib,finite_divisor_weight_square_energy]
  congr 1
  simp only [Finset.sum_ite_eq',Finset.mem_Icc]
  simp

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 2200000
open Finset Nat Real
open scoped BigOperators Classical

namespace Helfgott

lemma nat_div_cast_error_le_one (M k : ℕ) (hk : 0 < k) :
    |((M/k : ℕ) : ℝ)-(M : ℝ)/(k : ℝ)| ≤ 1 := by
  have hlo : ((M/k : ℕ) : ℝ) ≤ (M : ℝ)/(k : ℝ) := Nat.cast_div_le
  have hmod : ((M%k : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt M hk
  have he : (k : ℝ)*((M/k : ℕ) : ℝ)+((M%k : ℕ) : ℝ)=(M : ℝ) := by exact_mod_cast Nat.div_add_mod M k
  rw [abs_of_nonpos (sub_nonpos.mpr hlo)]
  have hkR : (0 : ℝ)<k := by exact_mod_cast hk
  have hupper : (M : ℝ)/(k : ℝ) ≤ ((M/k : ℕ) : ℝ)+1 := (div_le_iff₀ hkR).mpr (by nlinarith)
  linarith

theorem finite_divisor_weight_square_energy_approximation (M U : ℕ) (c : ℕ → ℝ) :
    |(∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ))| ≤
        (∑ d ∈ Finset.Icc 1 U,|c d|)^2 := by
  rw [finite_divisor_weight_square_energy]
  have he : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ))-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) =
      ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum,←Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [he]
  calc
    _ ≤ ∑ d ∈ Finset.Icc 1 U,|∑ e ∈ Finset.Icc 1 U,c d*c e*
        (((M/(Nat.lcm d e) : ℕ) : ℝ)-(M : ℝ)/(Nat.lcm d e : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,|c d| * |c e| := by
      apply Finset.sum_le_sum
      intro d hd
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      apply Finset.sum_le_sum
      intro e he
      have hk : 0 < Nat.lcm d e := Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1
      rw [abs_mul,abs_mul]
      exact mul_le_of_le_one_right (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (nat_div_cast_error_le_one M _ hk)
    _ = _ := by rw [pow_two,Finset.sum_mul];apply Finset.sum_congr rfl;intro d hd;rw [Finset.mul_sum]

theorem finite_divisor_weight_leading_quadratic_nonneg (U : ℕ) (c : ℕ → ℝ) :
    0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ) := by
  let M := U.factorial
  have hM : (0:ℝ)<M := by exact_mod_cast Nat.factorial_pos U
  have hexact : (∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e*((M/(Nat.lcm d e) : ℕ) : ℝ)) =
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,c d*c e/(Nat.lcm d e : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d hd
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hdM : d ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2
    have heM : e ∣ M := Nat.dvd_factorial (Finset.mem_Icc.mp he).1 (Finset.mem_Icc.mp he).2
    rw [Nat.cast_div (Nat.lcm_dvd hdM heM)] <;> try exact_mod_cast (Nat.lcm_pos (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp he).1).ne'
    ring
  have h := finite_divisor_weight_square_energy M U c
  rw [hexact] at h
  have hnonneg : 0 ≤ (∑ n ∈ Finset.Icc 1 M,(∑ d ∈ Finset.Icc 1 U,if d ∣ n then c d else 0)^2) :=
    Finset.sum_nonneg (fun n hn => sq_nonneg _)
  rw [h] at hnonneg
  exact nonneg_of_mul_nonneg_right hnonneg hM

end Helfgott
end

section
set_option autoImplicit false
set_option maxHeartbeats 1800000
open Finset Nat ArithmeticFunction Real
open scoped BigOperators Classical

namespace Helfgott

theorem vaughan_mobius_tail_energy_asymptotic_complete (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := by
  refine ⟨finite_divisor_weight_leading_quadratic_nonneg U _,?_⟩
  have hsum : (∑ d ∈ Finset.Icc 1 U,|((ArithmeticFunction.moebius d : ℤ) : ℝ)|) ≤ (U : ℝ) := by
    calc
      _ ≤ ∑ d ∈ Finset.Icc 1 U,(1:ℝ) := by
        apply Finset.sum_le_sum
        intro d hd
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      _ = _ := by simp
  have h := finite_divisor_weight_square_energy_approximation M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  have he := vaughan_mobius_tail_square_energy U M hU
  have hfull := finite_divisor_weight_square_energy M U (fun d => ((ArithmeticFunction.moebius d : ℤ) : ℝ))
  rw [hfull] at h
  rw [he,sub_add_cancel]
  refine h.trans ?_
  nlinarith [Finset.sum_nonneg (fun d (_ : d ∈ Finset.Icc 1 U) => abs_nonneg (((ArithmeticFunction.moebius d : ℤ) : ℝ)))]

end Helfgott
end

open Helfgott

theorem solution (U M : ℕ) (hU : 1 ≤ U) :
    (0 ≤ ∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ)) ∧
    |(∑ m ∈ Finset.Icc (U+1) M,
      ((arithmeticTail U (ArithmeticFunction.moebius : ArithmeticFunction ℝ)*ArithmeticFunction.zeta) m)^2)+
      (if 1 ≤ M then 1 else 0)-
      (M : ℝ)*(∑ d ∈ Finset.Icc 1 U,∑ e ∈ Finset.Icc 1 U,
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)*((ArithmeticFunction.moebius e : ℤ) : ℝ)/(Nat.lcm d e : ℝ))| ≤ (U : ℝ)^2 := Helfgott.vaughan_mobius_tail_energy_asymptotic_complete U M hU

#print axioms solution
