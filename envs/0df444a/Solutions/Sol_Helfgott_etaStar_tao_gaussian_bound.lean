-- Prove2me | solution 1 for Helfgott.etaStar_tao_gaussian_bound
-- status  : ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T16:39:01.026802+00:00
-- url     : https://prove2.me/submissions/c09da205-e424-4daf-90fb-c2c8c65eaaf3

import Theorems.Thm_TaoFivePrimes_exp_sum_estimate
import Definitions.Def_Helfgott_Smoothings
import Definitions.Def_Helfgott_WeightedCounting
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Theorems.Thm_Helfgott_etaStar_mellin_expSum
import Mathlib.Analysis.MeanInequalities

open Helfgott
open scoped BigOperators Classical

lemma etaTwo_eq_tao_eta0 : Helfgott.etaTwo = TaoFivePrimes.eta0 := by
  funext t
  simp only [Helfgott.etaTwo, TaoFivePrimes.eta0, max_comm]

lemma compact_expSum_eq_tao (x α : ℝ) :
    Helfgott.expSum (fun n => ((ArithmeticFunction.vonMangoldt n *
      Helfgott.etaTwo ((n : ℝ)/x) : ℝ) : ℂ)) (α : AddCircle (1 : ℝ)) =
      TaoFivePrimes.smoothedExpSum TaoFivePrimes.eta0 1 x α := by
  unfold Helfgott.expSum TaoFivePrimes.smoothedExpSum
  apply tsum_congr
  intro n
  rw [if_pos (Nat.coprime_one_right n)]
  simp only [etaTwo_eq_tao_eta0, Complex.ofReal_mul]
  have hf : fourier (n : ℤ) (α : AddCircle (1 : ℝ)) = TaoFivePrimes.expCircle (α*n) := by
    rw [fourier_coe_apply]
    unfold TaoFivePrimes.expCircle
    congr 1
    push_cast
    ring
  rw [hf]
  ring

private theorem compact_tao_estimate (x α β : ℝ) (a : ℤ) (q : ℕ)
    (hx : (10 : ℝ)^20 ≤ x) (hq : 100 ≤ q) (hqx : (q : ℝ) ≤ x/100)
    (haq : Nat.Coprime a.natAbs q) (hα : 4*α = (a : ℝ)/q+β)
    (hβ : |β| ≤ 1/(q : ℝ)^2) :
    ‖Helfgott.expSum (fun n => ((ArithmeticFunction.vonMangoldt n *
      Helfgott.etaTwo ((n : ℝ)/x) : ℝ) : ℂ)) (α : AddCircle (1 : ℝ))‖ ≤
      ((7/50:ℝ)*x/Real.sqrt q + (16/25:ℝ)*x/Real.sqrt (x/q) +
        (3/20:ℝ)*x^(4/5:ℝ)) * Real.log x * (Real.log x+113/10) := by
  rw [compact_expSum_eq_tao]
  have h := TaoFivePrimes.exp_sum_estimate x α β a q 1 hx hq hqx haq hα hβ (by simp)
  norm_num at h ⊢
  exact h



-- Auxiliary smoothing and Gaussian lemmas adapted from the accepted Prove2Me transfer proof
-- 7e49a96a-12b7-4d37-a4d9-d625b1c90ac8. The new polynomial transfer follows below.
open MeasureTheory Set
open scoped Interval BigOperators Classical
namespace HelfgottPolynomial
open Helfgott

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

lemma phi_nonneg (t : ℝ) : 0 ≤ phi t := by unfold phi; positivity

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


theorem etaStar_expSum_norm_le_of_polynomial (x a B₀ B₁ B₂ : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (α : AddCircle (1 : ℝ))
    (hcompact : ∀ w : ℝ, a ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n *
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ ≤
          (B₀+B₁*w+B₂*w^2)*(x*w/49)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      (x/49)*((B₀+3*B₂)*Real.sqrt (Real.pi/2)+2*B₁+5*a^3) := by
  let f : ℝ → ℝ := fun w =>
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
      etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w)
  let P : ℝ → ℝ := fun w => B₀*phi w+B₁*(w*phi w)+B₂*(w^2*phi w)
  let g : ℝ → ℝ := fun w => (x/49)*P w + (15*(x/49))*(Ioc (0 : ℝ) a).indicator phi w
  have hphi : IntegrableOn phi (Ioi (0 : ℝ)) := by simpa using phi_moment_integrable 0
  have hphi1 : IntegrableOn (fun w : ℝ => w*phi w) (Ioi (0 : ℝ)) := by
    simpa using phi_moment_integrable 1
  have hphi2 := phi_moment_integrable 2
  have hP : IntegrableOn P (Ioi (0 : ℝ)) :=
    ((hphi.const_mul _).add (hphi1.const_mul _)).add (hphi2.const_mul _)
  have hsmall : IntegrableOn ((Ioc (0 : ℝ) a).indicator phi) (Ioi (0 : ℝ)) :=
    hphi.indicator measurableSet_Ioc
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := (hP.const_mul _).add (hsmall.const_mul _)
  have hm := Helfgott.etaStar_mellin_expSum x hx α
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply hm.1.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (phi_nonneg _) hw.le)]
  have hle : (∫ w in Ioi (0 : ℝ), f w) ≤ ∫ w in Ioi (0 : ℝ), g w := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hwp : 0 < w := hw
    have hweight : 0 ≤ phi w/w := div_nonneg (phi_nonneg _) hwp.le
    have hp : 0 ≤ (x/49)*P w := by
      dsimp [P]
      have hphi0 := phi_nonneg w
      positivity
    by_cases hwa : w ≤ a
    · have hb := etaTwo_expSum_norm_le (x*w/49) (by positivity) α
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : (15*(x*w/49))*(phi w/w) = (15*(x/49))*phi w := by field_simp
      dsimp [f,g]
      rw [indicator_of_mem (show w ∈ Ioc (0 : ℝ) a from ⟨hwp,hwa⟩) phi]
      rw [he] at hh
      linarith
    · have hb := hcompact w (le_of_lt (lt_of_not_ge hwa))
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : ((B₀+B₁*w+B₂*w^2)*(x*w/49))*(phi w/w) = (x/49)*P w := by
        dsimp [P]
        field_simp
        <;> ring
      dsimp [f,g]
      rw [indicator_of_notMem (show w ∉ Ioc (0 : ℝ) a from fun h => hwa h.2) phi]
      rw [he] at hh
      simpa using hh
  have hsmall_eq : (∫ w in Ioi (0 : ℝ), (Ioc (0 : ℝ) a).indicator phi w) =
      ∫ w in Ioc (0 : ℝ) a, phi w := by
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset (show Ioc (0 : ℝ) a ⊆ Ioi 0 from fun w hw => hw.1)]
  have hPeq : (∫ w in Ioi (0 : ℝ), P w) =
      B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2)) := by
    have hi01 : IntegrableOn (fun w : ℝ => B₀*phi w+B₁*(w*phi w)) (Ioi (0 : ℝ)) :=
      (hphi.const_mul B₀).add (hphi1.const_mul B₁)
    dsimp [P]
    rw [integral_add hi01 (hphi2.const_mul B₂),
      integral_add (hphi.const_mul B₀) (hphi1.const_mul B₁),
      integral_const_mul, integral_const_mul, integral_const_mul,
      phi_mass, phi_first_moment, phi_second_moment]
  have hgeq : (∫ w in Ioi (0 : ℝ), g w) =
      (x/49)*(B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2))) +
        (15*(x/49))*(∫ w in Ioc (0 : ℝ) a, phi w) := by
    dsimp [g]
    rw [integral_add (hP.const_mul _) (hsmall.const_mul _),
      integral_const_mul, integral_const_mul, hPeq, hsmall_eq]
  calc
    _ ≤ ∫ w in Ioi (0 : ℝ), f w := hm.2.2
    _ ≤ ∫ w in Ioi (0 : ℝ), g w := hle
    _ = _ := hgeq
    _ ≤ (x/49)*(B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2))) +
        (15*(x/49))*(a^3/3) := by
      gcongr
      exact phi_small_mass a ha
    _ = _ := by ring

end HelfgottPolynomial


open MeasureTheory Set Helfgott HelfgottPolynomial
open scoped Interval BigOperators Classical
namespace HelfgottLaurent

lemma phi_div_eq (w : ℝ) : phi w/w = w*Real.exp (-(w^2)/2) := by
  unfold phi
  by_cases hw : w = 0
  · simp [hw]
  · field_simp

lemma phi_div_integrable : IntegrableOn (fun w : ℝ => phi w/w) (Ioi (0 : ℝ)) := by
  have h := integrableOn_rpow_mul_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1/2)
    (s := (1:ℝ)) (by norm_num)
  convert! h using 1
  funext w
  rw [phi_div_eq, Real.rpow_one]
  congr 2
  ring

lemma phi_div_mass : (∫ w in Ioi (0 : ℝ), phi w/w) = 1 := by
  have h := gaussian_power_integral 1
  norm_num [Real.Gamma_one, Real.rpow_neg_one] at h
  simpa only [phi_div_eq] using h

theorem etaStar_expSum_norm_le_of_laurent (x a Bm B₀ B₁ B₂ : ℝ)
    (hx : 0 < x) (ha : 0 < a) (hBm : 0 ≤ Bm) (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (α : AddCircle (1 : ℝ))
    (hcompact : ∀ w : ℝ, a ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n *
        etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ ≤
          (Bm/w+B₀+B₁*w+B₂*w^2)*(x*w/49)) :
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n : ℝ)/x) : ℝ) : ℂ)) α‖ ≤
      (x/49)*((B₀+3*B₂)*Real.sqrt (Real.pi/2)+2*B₁+Bm+5*a^3) := by
  let f : ℝ → ℝ := fun w =>
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*
      etaTwo ((n : ℝ)/(x*w/49)) : ℝ) : ℂ)) α‖ * (phi w/w)
  let P : ℝ → ℝ := fun w => B₀*phi w+B₁*(w*phi w)+B₂*(w^2*phi w)+Bm*(phi w/w)
  let g : ℝ → ℝ := fun w => (x/49)*P w + (15*(x/49))*(Ioc (0 : ℝ) a).indicator phi w
  have hphi : IntegrableOn phi (Ioi (0 : ℝ)) := by simpa using phi_moment_integrable 0
  have hphi1 : IntegrableOn (fun w : ℝ => w*phi w) (Ioi (0 : ℝ)) := by
    simpa using phi_moment_integrable 1
  have hphi2 := phi_moment_integrable 2
  have hdiv := phi_div_integrable
  have hP : IntegrableOn P (Ioi (0 : ℝ)) :=
    (((hphi.const_mul _).add (hphi1.const_mul _)).add (hphi2.const_mul _)).add (hdiv.const_mul _)
  have hsmall : IntegrableOn ((Ioc (0 : ℝ) a).indicator phi) (Ioi (0 : ℝ)) :=
    hphi.indicator measurableSet_Ioc
  have hg : IntegrableOn g (Ioi (0 : ℝ)) := (hP.const_mul _).add (hsmall.const_mul _)
  have hm := Helfgott.etaStar_mellin_expSum x hx α
  have hf : IntegrableOn f (Ioi (0 : ℝ)) := by
    apply hm.1.norm.congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    dsimp [f]
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
      (div_nonneg (phi_nonneg _) hw.le)]
  have hle : (∫ w in Ioi (0 : ℝ), f w) ≤ ∫ w in Ioi (0 : ℝ), g w := by
    apply integral_mono_ae hf hg
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with w hw
    have hwp : 0 < w := hw
    have hweight : 0 ≤ phi w/w := div_nonneg (phi_nonneg _) hwp.le
    have hp : 0 ≤ (x/49)*P w := by
      dsimp [P]
      have hphi0 := phi_nonneg w
      positivity
    by_cases hwa : w ≤ a
    · have hb := etaTwo_expSum_norm_le (x*w/49) (by positivity) α
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : (15*(x*w/49))*(phi w/w) = (15*(x/49))*phi w := by field_simp
      dsimp [f,g]
      rw [indicator_of_mem (show w ∈ Ioc (0 : ℝ) a from ⟨hwp,hwa⟩) phi]
      rw [he] at hh
      linarith
    · have hb := hcompact w (le_of_lt (lt_of_not_ge hwa))
      have hh := mul_le_mul_of_nonneg_right hb hweight
      have he : ((Bm/w+B₀+B₁*w+B₂*w^2)*(x*w/49))*(phi w/w) = (x/49)*P w := by
        dsimp [P]
        field_simp
        <;> ring
      dsimp [f,g]
      rw [indicator_of_notMem (show w ∉ Ioc (0 : ℝ) a from fun h => hwa h.2) phi]
      rw [he] at hh
      simpa using hh
  have hsmall_eq : (∫ w in Ioi (0 : ℝ), (Ioc (0 : ℝ) a).indicator phi w) =
      ∫ w in Ioc (0 : ℝ) a, phi w := by
    rw [integral_indicator measurableSet_Ioc,
      Measure.restrict_restrict_of_subset (show Ioc (0 : ℝ) a ⊆ Ioi 0 from fun w hw => hw.1)]
  have hPeq : (∫ w in Ioi (0 : ℝ), P w) =
      B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2))+Bm := by
    have hi01 : IntegrableOn (fun w : ℝ => B₀*phi w+B₁*(w*phi w)) (Ioi (0 : ℝ)) :=
      (hphi.const_mul B₀).add (hphi1.const_mul B₁)
    have hi012 : IntegrableOn (fun w : ℝ => B₀*phi w+B₁*(w*phi w)+B₂*(w^2*phi w)) (Ioi (0 : ℝ)) :=
      hi01.add (hphi2.const_mul B₂)
    dsimp [P]
    rw [integral_add hi012 (hdiv.const_mul Bm), integral_const_mul,
      phi_div_mass, mul_one, integral_add hi01 (hphi2.const_mul B₂),
      integral_add (hphi.const_mul B₀) (hphi1.const_mul B₁),
      integral_const_mul, integral_const_mul, integral_const_mul,
      phi_mass, phi_first_moment, phi_second_moment]
  have hgeq : (∫ w in Ioi (0 : ℝ), g w) =
      (x/49)*(B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2))+Bm) +
        (15*(x/49))*(∫ w in Ioc (0 : ℝ) a, phi w) := by
    dsimp [g]
    rw [integral_add (hP.const_mul _) (hsmall.const_mul _),
      integral_const_mul, integral_const_mul, hPeq, hsmall_eq]
  calc
    _ ≤ ∫ w in Ioi (0 : ℝ), f w := hm.2.2
    _ ≤ ∫ w in Ioi (0 : ℝ), g w := hle
    _ = _ := hgeq
    _ ≤ (x/49)*(B₀*Real.sqrt (Real.pi/2)+B₁*2+B₂*(3*Real.sqrt (Real.pi/2))+Bm) +
        (15*(x/49))*(a^3/3) := by
      gcongr
      exact phi_small_mass a ha
    _ = _ := by ring


end HelfgottLaurent


open Helfgott
open scoped BigOperators Classical
set_option maxHeartbeats 1000000

namespace Helfgott

private lemma inverse_power_tangent (w θ : ℝ) (hw : 0 < w) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    w^(-θ) ≤ θ/w+(1-θ) := by
  have h := Real.geom_mean_le_arith_mean2_weighted hθ (sub_nonneg.mpr hθ1)
    (inv_nonneg.mpr hw.le) (by norm_num : (0:ℝ) ≤ 1) (by ring : θ+(1-θ) = 1)
  rw [Real.one_rpow, mul_one, ← Real.rpow_neg_eq_inv_rpow] at h
  simpa only [mul_one, div_eq_mul_inv] using h

theorem etaStar_tao_gaussian_bound (x t α β : ℝ) (a : ℤ) (q : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hq : 100 ≤ q) (hqx : (q:ℝ) ≤ (x*t/49)/100)
    (haq : Nat.Coprime a.natAbs q) (hα : 4*α = (a:ℝ)/q+β)
    (hβ : |β| ≤ 1/(q:ℝ)^2) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt q
    let B := (16/25:ℝ)/Real.sqrt (X/q)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by
  let X : ℝ := x/49
  let L : ℝ := Real.log X
  let A : ℝ := (7/50:ℝ)/Real.sqrt q
  let B : ℝ := (16/25:ℝ)/Real.sqrt (X/q)
  let C : ℝ := (3/20:ℝ)*X^(-(1/5:ℝ))
  let D₀ : ℝ := A+B/2+4*C/5
  let Dm : ℝ := B/2+C/5
  let H : ℝ := L*(L+113/10)
  let J : ℝ := 2*L+113/10
  have hx0 : 0 < x := by linarith
  have hX : 0 < X := by dsimp [X]; positivity
  have hq0 : (0:ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hL : 0 ≤ L := Real.log_nonneg ((le_div_iff₀ (by norm_num : (0:ℝ) < 49)).mpr (by linarith))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hDm : 0 ≤ Dm := by dsimp [Dm]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hcompact : ∀ w : ℝ, t ≤ w →
      ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaTwo ((n:ℝ)/(x*w/49)):ℝ):ℂ))
        (α : AddCircle (1:ℝ))‖ ≤
        (Dm*H/w+(D₀*H+Dm*J)+(D₀*J+Dm)*w+D₀*w^2)*(x*w/49) := by
    intro w hw
    let y : ℝ := x*w/49
    have hw0 : 0 < w := ht.trans_le hw
    have hy : 0 < y := by dsimp [y]; positivity
    have hlow : x*t/49 ≤ y := by dsimp [y]; nlinarith
    have hymin : (10:ℝ)^20 ≤ y := hmin.trans hlow
    have hqy : (q:ℝ) ≤ y/100 := hqx.trans (by linarith)
    have hbound := _root_.compact_tao_estimate y α β a q hymin hq hqy haq hα hβ
    have hy_eq : y = X*w := by dsimp [y,X]; ring
    have hlog0 : 0 ≤ Real.log y := Real.log_nonneg (by nlinarith [hymin])
    have hlog : Real.log y ≤ L+w := by
      rw [hy_eq, Real.log_mul hX.ne' hw0.ne']
      dsimp [L]
      linarith [Real.log_le_sub_one_of_pos hw0]
    have hsqrt : Real.sqrt (y/(q:ℝ)) = Real.sqrt (X/(q:ℝ))*Real.sqrt w := by
      rw [hy_eq, show X*w/(q:ℝ) = (X/(q:ℝ))*w by ring, Real.sqrt_mul (div_nonneg hX.le hq0.le)]
    have hsecond_eq : (16/25:ℝ)*y/Real.sqrt (y/q) = B*y*w^(-(1/2:ℝ)) := by
      rw [hsqrt, Real.rpow_neg hw0.le, ← Real.sqrt_eq_rpow]
      dsimp [B]
      field_simp
    have hpow_eq : y^(4/5:ℝ) = y*y^(-(1/5:ℝ)) := by
      rw [show (4/5:ℝ) = 1 + -(1/5) by norm_num, Real.rpow_add hy, Real.rpow_one]
    have hthird_eq : (3/20:ℝ)*y^(4/5:ℝ) = C*y*w^(-(1/5:ℝ)) := by
      rw [hpow_eq]
      conv_lhs => arg 2; arg 2; rw [hy_eq, Real.mul_rpow hX.le hw0.le]
      dsimp [C]
      ring
    have hhalf := inverse_power_tangent w (1/2) hw0 (by norm_num) (by norm_num)
    have hfifth := inverse_power_tangent w (1/5) hw0 (by norm_num) (by norm_num)
    have hb := mul_le_mul_of_nonneg_left hhalf (mul_nonneg hB hy.le)
    have hc := mul_le_mul_of_nonneg_left hfifth (mul_nonneg hC hy.le)
    have hbase : (7/50:ℝ)*y/Real.sqrt q + (16/25:ℝ)*y/Real.sqrt (y/q) +
        (3/20:ℝ)*y^(4/5:ℝ) ≤ (D₀+Dm/w)*y := by
      rw [hsecond_eq, hthird_eq]
      have hfirst : (7/50:ℝ)*y/Real.sqrt q = A*y := by dsimp [A]; ring
      rw [hfirst]
      dsimp [D₀,Dm]
      simp only [div_eq_mul_inv] at hb hc ⊢
      nlinarith
    have hD : 0 ≤ D₀+Dm/w := by positivity
    have hb1 := mul_le_mul_of_nonneg_right hbase hlog0
    have hb2 := mul_le_mul_of_nonneg_right hb1 (show 0 ≤ Real.log y+113/10 by linarith)
    have hl1 := mul_le_mul_of_nonneg_left hlog (mul_nonneg hD hy.le)
    have hl2 := mul_le_mul hl1 (show Real.log y+113/10 ≤ L+w+113/10 by linarith)
      (show 0 ≤ Real.log y+113/10 by linarith)
      (show 0 ≤ (D₀+Dm/w)*y*(L+w) by positivity)
    calc
      _ ≤ (D₀+Dm/w)*y*(L+w)*(L+w+113/10) := hbound.trans (hb2.trans hl2)
      _ = _ := by
        change _ = (Dm*H/w+(D₀*H+Dm*J)+(D₀*J+Dm)*w+D₀*w^2)*y
        dsimp [H,J]
        field_simp
        <;> ring
  have h := HelfgottLaurent.etaStar_expSum_norm_le_of_laurent x t
    (Dm*H) (D₀*H+Dm*J) (D₀*J+Dm) D₀ hx0 ht
    (by positivity) (by positivity) (by positivity) hD₀ (α : AddCircle (1:ℝ)) hcompact
  dsimp only
  change _ ≤ X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J)+
    Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3)
  change _ ≤ X*(_) at h
  convert h using 1 <;> ring

end Helfgott

open Helfgott

theorem solution (x t α β : ℝ) (a : ℤ) (q : ℕ)
    (hx : 49 ≤ x) (ht : 0 < t) (hmin : (10:ℝ)^20 ≤ x*t/49)
    (hq : 100 ≤ q) (hqx : (q:ℝ) ≤ (x*t/49)/100)
    (haq : Nat.Coprime a.natAbs q) (hα : 4*α = (a:ℝ)/q+β)
    (hβ : |β| ≤ 1/(q:ℝ)^2) :
    let X := x/49
    let L := Real.log X
    let A := (7/50:ℝ)/Real.sqrt q
    let B := (16/25:ℝ)/Real.sqrt (X/q)
    let C := (3/20:ℝ)*X^(-(1/5:ℝ))
    let D₀ := A+B/2+4*C/5
    let Dm := B/2+C/5
    let H := L*(L+113/10)
    let J := 2*L+113/10
    ‖expSum (fun n => ((ArithmeticFunction.vonMangoldt n*etaStar ((n:ℝ)/x):ℝ):ℂ))
      (α : AddCircle (1:ℝ))‖ ≤
      X*(D₀*((H+3)*Real.sqrt (Real.pi/2)+2*J) +
        Dm*(J*Real.sqrt (Real.pi/2)+H+2)+5*t^3) := by
  exact Helfgott.etaStar_tao_gaussian_bound x t α β a q hx ht hmin hq hqx haq hα hβ
