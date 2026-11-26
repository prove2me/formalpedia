-- Prove2me | solution 1 for MasulloRH.theta_value_enclosure_of_gaussian_parameter
-- status  : ACCEPTED   (prove)
-- author  : @scuba8684
-- created : 2026-11-26T09:29:01.583147+00:00
-- url     : https://prove2.me/submissions/79ae797b-9aa7-4d95-ab47-dcf3748e2fa5

import Theorems.Thm_MasulloRH_theta_gaussian_truncation_error
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

open MasulloRH.GaussianApproximation
open scoped BigOperators ComplexConjugate

theorem solution (K : ℕ) (x L U : ℝ) (hL : 0 ≤ L)
    (hl : L ≤ Real.exp (-Real.pi * (Real.exp x)^2))
    (hu : Real.exp (-Real.pi * (Real.exp x)^2) ≤ U) (hU : U < 1) :
    let B (a b : ℝ) := 2 * ∑ n ∈ Finset.range K,
      (a ^ ((n+1)^2) - 3*b ^ (4*(n+1)^2) + 2*a ^ (16*(n+1)^2))
    let E := 12 * U ^ ((K+1)^2) / (1 - U ^ (2*K+3))
    (theta x).im = 0 ∧ B L U - E ≤ (theta x).re ∧ (theta x).re ≤ B U L + E := by
  intro B E
  let q := Real.exp (-Real.pi * (Real.exp x)^2)
  have hq : 0 ≤ q := (Real.exp_pos _).le
  have hUn : 0 ≤ U := hq.trans hu
  have hm (a b c d : ℝ) (ha : 0 ≤ a) (hd : 0 ≤ d) (hac : a ≤ c) (hdb : d ≤ b) :
      B a b ≤ B c d := by
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    apply Finset.sum_le_sum
    intro n _
    linarith [pow_le_pow_left₀ ha hac ((n+1)^2),
      pow_le_pow_left₀ ha hac (16*(n+1)^2), pow_le_pow_left₀ hd hdb (4*(n+1)^2)]
  have low := hm L U q q hL hq hl hu
  have high := hm q q U L hq hL hu hl
  have hdec : 0 < 1 - U ^ (2*K+3) := sub_pos.mpr (pow_lt_one₀ hUn hU (by omega))
  have hden : 1-U^(2*K+3) ≤ 1-q^(2*K+3) :=
    sub_le_sub_left (pow_le_pow_left₀ hq hu _) _
  have htail : 12*q^((K+1)^2)/(1-q^(2*K+3)) ≤ E := by
    calc
      _ ≤ 12*U^((K+1)^2)/(1-q^(2*K+3)) := by
        apply div_le_div_of_nonneg_right _ (hdec.le.trans hden)
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hu _) (by norm_num)
      _ ≤ E := div_le_div_of_nonneg_left (by positivity) hdec hden
  have hpow (n : ℕ) : Real.exp (-Real.pi*(Real.exp x)^2*(n:ℝ)) = q^n := by
    calc
      _ = Real.exp ((n : ℝ) * (-Real.pi*(Real.exp x)^2)) := congrArg Real.exp (mul_comm _ _)
      _ = _ := Real.exp_nat_mul _ n
  have hterm (n c : ℕ) :
      Real.exp (-Real.pi*((c:ℝ)*(((n:ℝ)+1)*Real.exp x))^2) = q^(c^2*(n+1)^2) := by
    rw [← hpow]
    congr 1
    push_cast
    ring
  have hfin : ((2 * ∑ n ∈ Finset.range K,
      ((Real.exp (-Real.pi * (((n : ℝ)+1)*Real.exp x)^2) -
        3 * Real.exp (-Real.pi * (2*(((n : ℝ)+1)*Real.exp x))^2) +
        2 * Real.exp (-Real.pi * (4*(((n : ℝ)+1)*Real.exp x))^2) : ℝ) : ℂ)) : ℂ).re =
      B q q := by
    have twoRe : (2 : ℂ).re = 2 := rfl
    have twoIm : (2 : ℂ).im = 0 := rfl
    simp only [Complex.mul_re, twoRe, twoIm, zero_mul, sub_zero,
      Complex.re_sum, Complex.ofReal_re, B]
    congr 1
    apply Finset.sum_congr rfl
    intro n _
    have h1 := hterm n 1
    have h2 := hterm n 2
    have h4 := hterm n 4
    norm_num only [Nat.cast_ofNat, Nat.cast_one, one_mul, one_pow] at h1 h2 h4
    rw [h1,h2,h4]
  have hc := MasulloRH.theta_gaussian_truncation_error x K
  have hnum : Real.exp (-Real.pi*(Real.exp x)^2*((K:ℝ)+1)^2) = q^((K+1)^2) := by
    rw [← hpow]
    push_cast
    rfl
  have hexp : Real.exp (-Real.pi*(Real.exp x)^2*(2*(K:ℝ)+3)) = q^(2*K+3) := by
    rw [← hpow]
    push_cast
    rfl
  rw [hnum,hexp] at hc
  have hr := (Complex.abs_re_le_norm _).trans (hc.trans htail)
  rw [Complex.sub_re,hfin] at hr
  obtain ⟨hlower,hupper⟩ := abs_le.mp hr
  refine ⟨?_, by linarith, by linarith⟩
  apply Complex.conj_eq_iff_im.mp
  simp only [theta, Complex.conj_tsum, Complex.conj_ofReal]
