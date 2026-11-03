-- Prove2me | solution 1 for Grothendieck.vietoris_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T15:05:09.950209+00:00
-- url     : https://prove2.me/submissions/b1d5c937-91f1-40de-9160-8ef2992a766a

import Mathlib
import Definitions.Def_Grothendieck_Series

set_option autoImplicit false

noncomputable section
open scoped BigOperators Real
open MeasureTheory

namespace VietorisAux

/-! ## Pochhammer polynomial and binomial-series facts -/

theorem ascPochhammer_eval_eq_prod (z : ℂ) (n : ℕ) :
    (ascPochhammer ℂ n).eval z = ∏ i ∈ Finset.range n, (z + i) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [ascPochhammer_succ_eval, ih, Finset.prod_range_succ]

theorem ofReal_risingFact (a : ℝ) (n : ℕ) :
    ((Grothendieck.risingFact a n : ℝ) : ℂ) = ∏ i ∈ Finset.range n, ((a : ℂ) + i) := by
  rw [Grothendieck.risingFact]
  push_cast
  rfl

/-- `Ring.choose (n - 1/2) n = (1/2)_n / n!` -/
theorem choose_eq_risingFact (n : ℕ) :
    Ring.choose ((1/2 : ℂ) + (n : ℂ) - 1) n
      = ((Grothendieck.risingFact (1/2) n : ℝ) : ℂ) / (n.factorial : ℂ) := by
  have h1 : (n.factorial : ℂ) * Ring.choose ((1/2 : ℂ) + (n : ℂ) - 1) n
      = (descPochhammer ℤ n).smeval ((1/2 : ℂ) + (n : ℂ) - 1) := by
    have := Ring.descPochhammer_eq_factorial_smul_choose ((1/2 : ℂ) + (n : ℂ) - 1) n
    rw [nsmul_eq_mul] at this
    exact this.symm
  have h2 : (descPochhammer ℤ n).smeval ((1/2 : ℂ) + (n : ℂ) - 1)
      = ((Grothendieck.risingFact (1/2) n : ℝ) : ℂ) := by
    rw [Polynomial.descPochhammer_smeval_eq_ascPochhammer,
      Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_eq_prod, ofReal_risingFact]
    refine Finset.prod_congr rfl ?_
    intro i _
    push_cast
    ring
  have h3 := h1.trans h2
  rw [eq_div_iff (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)), mul_comm]
  exact h3

/-- The binomial series `1/(1-w)^(1/2) = ∑_k (1/2)_k/k! w^k` for `‖w‖ < 1`. -/
theorem hasSum_binom_series (w : ℂ) (hw : ‖w‖ < 1) :
    HasSum (fun k : ℕ => ((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ) * w ^ k)
      (1 / (1 - w) ^ (1/2 : ℂ)) := by
  have h := Complex.one_div_one_sub_cpow_hasFPowerSeriesOnBall_zero (1/2 : ℂ)
  have hmem : w ∈ Metric.eball (0 : ℂ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
    exact hw
  have hs := h.hasSum hmem
  have hpt : ∀ k : ℕ,
      ((FormalMultilinearSeries.ofScalars ℂ fun n => Ring.choose ((1/2 : ℂ) + ↑n - 1) n) k)
        (fun _ => w)
      = ((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ) * w ^ k := by
    intro k
    simp only [FormalMultilinearSeries.ofScalars]
    rw [choose_eq_risingFact]
    simp
  simpa only [hpt, zero_add] using hs

/-! ## Positivity of the real part -/

theorem pow_mul_exp_re (x t : ℝ) (k : ℕ) :
    (((x : ℂ) * Complex.exp (t * Complex.I)) ^ k).re = x ^ k * Real.cos (k * t) := by
  rw [mul_pow, ← Complex.ofReal_pow, ← Complex.exp_nat_mul]
  have hk : (↑k : ℂ) * (t * Complex.I) = (((k : ℝ) * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hk, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]

theorem re_one_sub_mul_exp_pos {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < π) :
    0 < (1 - (x : ℂ) * Complex.exp (t * Complex.I)).re := by
  rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, zero_mul, sub_zero]
  have hpi : t < 2 * π := by linarith [Real.pi_pos]
  have hcos1 : Real.cos t < 1 := by
    rcases lt_or_eq_of_le (Real.cos_le_one t) with h | h
    · exact h
    · exfalso
      rw [Real.cos_eq_one_iff_of_lt_of_lt (by linarith [Real.pi_pos]) hpi] at h
      linarith
  rcases le_total 0 (Real.cos t) with hc | hc
  · nlinarith [mul_le_mul_of_nonneg_right hx1 hc]
  · nlinarith [mul_nonpos_of_nonneg_of_nonpos hx0 hc]

theorem cpow_half_ne_zero {z : ℂ} (hz : z ≠ 0) : z ^ (1/2 : ℂ) ≠ 0 := by
  intro h
  have hvv : z ^ (1/2 : ℂ) * z ^ (1/2 : ℂ) = z := by
    rw [← Complex.cpow_add _ _ hz, show ((1/2 : ℂ) + (1/2 : ℂ)) = 1 by norm_num,
      Complex.cpow_one]
  rw [h, mul_zero] at hvv
  exact hz hvv.symm

/-- For `x ∈ [0,1]` and `t ∈ (0,π)`, the real part of `1/(1-x e^{it})^{1/2}` is nonzero. -/
theorem re_inv_cpow_ne_zero {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (ht0 : 0 < t) (ht1 : t < π) :
    (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re ≠ 0 := by
  set z : ℂ := 1 - (x : ℂ) * Complex.exp (t * Complex.I) with hzdef
  have hzre : 0 < z.re := by
    rw [hzdef]; exact re_one_sub_mul_exp_pos x hx0 hx1 ht0 ht1
  have hz : z ≠ 0 := by
    intro h; rw [h] at hzre; simp at hzre
  set v : ℂ := z ^ (1/2 : ℂ) with hvdef
  have hvv : v * v = z := by
    rw [hvdef, ← Complex.cpow_add _ _ hz,
      show ((1/2 : ℂ) + (1/2 : ℂ)) = 1 by norm_num, Complex.cpow_one]
  have hvne : v ≠ 0 := by
    rw [hvdef]; exact cpow_half_ne_zero hz
  have hvrels : v.re * v.re = v.im * v.im + z.re := by
    have h := congrArg Complex.re hvv
    simp only [Complex.mul_re] at h
    linarith
  have hvr : v.re ≠ 0 := by
    have hpos : 0 < v.re * v.re := by
      rw [hvrels]; nlinarith [sq_nonneg v.im, hzre]
    exact fun h => absurd hpos (by rw [h, mul_zero]; exact lt_irrefl 0)
  have hval : (1 / v).re = v.re / ‖v‖ ^ 2 := by
    rw [one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [hval]
  exact div_ne_zero hvr (pow_ne_zero 2 (norm_ne_zero_iff.mpr hvne))

/-- For `t ∈ (0,π)` and all `x ∈ [0,1]`, `Re (1/(1-x e^{it})^{1/2}) > 0`. -/
theorem re_inv_cpow_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1,
      0 < (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re := by
  set g : ℝ → ℝ :=
    fun x => (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re with hg
  have hne : ∀ x ∈ Set.Icc (0 : ℝ) 1, g x ≠ 0 := by
    intro x hx
    rw [hg]
    exact re_inv_cpow_ne_zero x hx.1 hx.2 ht0 ht1
  have hbase : Continuous fun x : ℝ => 1 - (x : ℂ) * Complex.exp (t * Complex.I) := by
    fun_prop
  have hslit : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1)
  have hcpow : ContinuousOn
      (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact hbase.continuousWithinAt.cpow continuousWithinAt_const (hslit x hx)
  have hnonzero : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ) ≠ 0 := by
    intro x hx
    refine cpow_half_ne_zero (z := 1 - (x : ℂ) * Complex.exp (t * Complex.I)) ?_
    intro h
    have hzre := re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1
    rw [h] at hzre
    simp at hzre
  have hinv : ContinuousOn
      (fun x : ℝ => 1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.div hcpow hnonzero
  have hgc : ContinuousOn g (Set.Icc (0 : ℝ) 1) := Complex.continuous_re.comp_continuousOn hinv
  have hg0 : g 0 = 1 := by
    rw [hg]
    norm_num
  intro x hx
  rcases lt_trichotomy (g x) 0 with h | h | h
  · have hcont : ContinuousOn g (Set.Icc (0 : ℝ) x) :=
      hgc.mono fun y hy => ⟨hy.1, hy.2.trans hx.2⟩
    have hmem : (0 : ℝ) ∈ Set.Icc (g x) (g 0) := ⟨h.le, by rw [hg0]; norm_num⟩
    obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc' hx.1 hcont hmem
    exact absurd hyv (hne y ⟨hy.1, hy.2.trans hx.2⟩)
  · exfalso; exact hne x hx h
  · exact h

/-- The Beta-type moment `∫_0^1 x^{k-1/2} (1-x)^{r/2-1/2} dx`. -/
def Jb (r k : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2)

/-- The constant `c = r/2 + 1`. -/
def cc (r : ℕ) : ℝ := (r : ℝ)/2 + 1

theorem Jb_eq_betaIntegral (r k : ℕ) :
    ((Jb r k : ℝ) : ℂ)
      = Complex.betaIntegral (((k : ℝ) + 1/2 : ℝ) : ℂ) ((((r : ℝ) + 1)/2 : ℝ) : ℂ) := by
  have h1 : ((Jb r k : ℝ) : ℂ)
      = ∫ x in (0 : ℝ)..1,
          ((x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2) : ℝ) : ℂ) := by
    rw [Jb, intervalIntegral.integral_ofReal]
  rw [h1, Complex.betaIntegral]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards with x hx
  have hx' : x ∈ Set.Ioc (0:ℝ) 1 := by
    simpa [Set.uIoc_of_le (by norm_num : (0:ℝ) ≤ 1)] using hx
  have hxpos : 0 < x := hx'.1
  have e1 : (((k : ℝ) - 1/2 : ℝ) : ℂ) = (((k : ℝ) + 1/2 : ℝ) : ℂ) - 1 := by push_cast; ring
  have e2 : ((((r : ℝ)/2 - 1/2) : ℝ) : ℂ) = (((((r : ℝ) + 1)/2) : ℝ) : ℂ) - 1 := by push_cast; ring
  have e3 : ((1 - x : ℝ) : ℂ) = 1 - (x : ℂ) := by push_cast; ring
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hxpos.le,
    Complex.ofReal_cpow (show (0:ℝ) ≤ 1 - x by linarith [hx'.2]), e1, e2, e3]

theorem Jb_eq_gamma (r k : ℕ) :
    Jb r k = Real.Gamma ((k : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1)/2)
      / Real.Gamma ((k : ℝ) + cc r) := by
  have hu : (0:ℝ) < ((((k : ℝ) + 1/2 : ℝ)) : ℂ).re := by
    have h : (0:ℝ) < (k : ℝ) + 1/2 := by positivity
    simpa using h
  have hv : (0:ℝ) < ((((r : ℝ) + 1)/2 : ℝ) : ℂ).re := by
    have h : (0:ℝ) < ((r : ℝ) + 1)/2 := by positivity
    simpa using h
  have hG : ((Jb r k : ℝ) : ℂ)
      = Complex.Gamma ((((k : ℝ) + 1/2 : ℝ)) : ℂ) * Complex.Gamma (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)
        / Complex.Gamma (((((k : ℝ) + 1/2 : ℝ)) : ℂ) + (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)) := by
    rw [Jb_eq_betaIntegral r k, Complex.betaIntegral_eq_Gamma_mul_div _ _ hu hv]
  have key : ((Real.Gamma ((k : ℝ) + 1/2) * Real.Gamma (((r : ℝ) + 1)/2)
      / Real.Gamma ((k : ℝ) + cc r) : ℝ) : ℂ)
      = Complex.Gamma ((((k : ℝ) + 1/2 : ℝ)) : ℂ) * Complex.Gamma (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)
        / Complex.Gamma (((((k : ℝ) + 1/2 : ℝ)) : ℂ) + (((((r : ℝ) + 1)/2 : ℝ)) : ℂ)) := by
    rw [Complex.ofReal_div, Complex.ofReal_mul, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal,
      ← Complex.Gamma_ofReal]
    congr 2
    simp only [cc]
    push_cast
    ring
  exact Complex.ofReal_inj.mp (hG.trans key.symm)

theorem gamma_add_nat_div_eq_risingFact (a : ℝ) (ha : 0 < a) (k : ℕ) :
    Real.Gamma ((k : ℝ) + a) / Real.Gamma a = Grothendieck.risingFact a k := by
  have hz : ∀ m : ℕ, (a : ℂ) ≠ -(m : ℂ) := by
    intro m h
    have h2 : a = -(m : ℝ) := by
      have hh := congrArg Complex.re h
      simpa using hh
    have : (0:ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have h := Complex.Gamma_add_nat_div_Gamma_eq (a : ℂ) hz (n := k)
  have hmain : Complex.Gamma ((a : ℂ) + (k : ℂ)) / Complex.Gamma (a : ℂ)
      = ((Grothendieck.risingFact a k : ℝ) : ℂ) := by
    rw [h, ascPochhammer_eval_eq_prod, ofReal_risingFact]
  have hreal : ((Real.Gamma ((k : ℝ) + a) / Real.Gamma a : ℝ) : ℂ)
      = Complex.Gamma ((a : ℂ) + (k : ℂ)) / Complex.Gamma (a : ℂ) := by
    rw [Complex.ofReal_div, ← Complex.Gamma_ofReal, ← Complex.Gamma_ofReal]
    have e : (((k : ℝ) + a : ℝ) : ℂ) = ((a : ℂ) + (k : ℂ)) := by push_cast; ring
    rw [e]
  exact Complex.ofReal_inj.mp (hreal.trans hmain)

theorem Jb_pos (r k : ℕ) : 0 < Jb r k := by
  rw [Jb_eq_gamma r k]
  have h1 : 0 < Real.Gamma ((k : ℝ) + 1/2) := Real.Gamma_pos_of_pos (by positivity)
  have h2 : 0 < Real.Gamma (((r : ℝ) + 1)/2) := Real.Gamma_pos_of_pos (by positivity)
  have h3 : 0 < Real.Gamma ((k : ℝ) + cc r) := Real.Gamma_pos_of_pos (by
    simp only [cc]; positivity)
  positivity

/-- Ratio formula: `Jb r k = Jb r 0 * ((1/2)_k / (r/2+1)_k)`. -/
theorem Jb_ratio (r k : ℕ) :
    Jb r k = Jb r 0 * (Grothendieck.risingFact (1/2) k / Grothendieck.risingFact (cc r) k) := by
  have hcpos : 0 < cc r := by simp only [cc]; positivity
  have hA : Real.Gamma ((k : ℝ) + 1/2) / Real.Gamma (1/2) = Grothendieck.risingFact (1/2) k := by
    simpa using gamma_add_nat_div_eq_risingFact (1/2) (by norm_num) k
  have hB : Real.Gamma ((k : ℝ) + cc r) / Real.Gamma (cc r) = Grothendieck.risingFact (cc r) k :=
    gamma_add_nat_div_eq_risingFact (cc r) hcpos k
  have hA0 : Real.Gamma (1/2) ≠ 0 := (Real.Gamma_pos_of_pos (by norm_num)).ne'
  have hB0 : Real.Gamma (cc r) ≠ 0 := (Real.Gamma_pos_of_pos hcpos).ne'
  have hAk : Real.Gamma ((k : ℝ) + 1/2) = Grothendieck.risingFact (1/2) k * Real.Gamma (1/2) := by
    have hh := congrArg (· * Real.Gamma (1/2)) hA
    rwa [div_mul_cancel₀ _ hA0] at hh
  have hBk : Real.Gamma ((k : ℝ) + cc r) = Grothendieck.risingFact (cc r) k * Real.Gamma (cc r) := by
    have hh := congrArg (· * Real.Gamma (cc r)) hB
    rwa [div_mul_cancel₀ _ hB0] at hh
  rw [Jb_eq_gamma r k, Jb_eq_gamma r 0, hAk, hBk]
  simp only [Nat.cast_zero, zero_add]
  have hG : Real.Gamma (((r : ℝ) + 1)/2) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  field_simp
/-- The real cosine series coming from the binomial series at `w = x·e^{it}`. -/
theorem hasSum_series_re {t : ℝ} (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k
        * Real.cos (k * t))
      ((1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re) := by
  have hw : ‖(x : ℂ) * Complex.exp (t * Complex.I)‖ < 1 := by
    rw [Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0,
      Complex.norm_exp_ofReal_mul_I, mul_one]
    exact hx1
  have hs := (hasSum_binom_series _ hw).map Complex.reCLM Complex.reCLM.continuous
  have hc : ∀ k : ℕ, (((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
      = (((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_div]
    push_cast
    try ring
  have hterm : ∀ k : ℕ,
      ((((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
          * ((x : ℂ) * Complex.exp (t * Complex.I)) ^ k).re
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k * Real.cos (k * t) := by
    intro k
    rw [hc k, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      pow_mul_exp_re]
    ring
  simp only [Function.comp_def, Complex.reCLM_apply] at hs ⊢
  rw [funext hterm] at hs
  exact hs

/-- Closed form of the underlying nonnegative series at a real point. -/
theorem hasSum_closed {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    HasSum (fun k : ℕ => (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k)
      ((1 - x) ^ (-(1/2) : ℝ)) := by
  have hw : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0]
    exact hx1
  have hs := (hasSum_binom_series (x : ℂ) hw).map Complex.reCLM Complex.reCLM.continuous
  have hc : ∀ k : ℕ, (((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ))
      = (((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) : ℝ) : ℂ) := by
    intro k
    rw [Complex.ofReal_div]
    push_cast
    try ring
  have hterm : ∀ k : ℕ,
      ((((Grothendieck.risingFact (1/2) k : ℝ) : ℂ) / (k.factorial : ℂ)) * (x : ℂ) ^ k).re
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * x ^ k := by
    intro k
    rw [hc k, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
      ← Complex.ofReal_pow, Complex.ofReal_re]
  have hrhs : ((1 / (1 - (x : ℂ)) ^ (1/2 : ℂ))).re = (1 - x) ^ (-(1/2) : ℝ) := by
    have h1x : (0:ℝ) < 1 - x := by linarith
    have hcast : (1 - (x : ℂ)) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
    have e : ((1 - x : ℝ) : ℂ) ^ (1/2 : ℂ) = ((Real.sqrt (1 - x) : ℝ) : ℂ) := by
      rw [show (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) by norm_num,
        ← Complex.ofReal_cpow h1x.le (1/2 : ℝ), ← Real.sqrt_eq_rpow]
    rw [hcast, e, one_div, ← Complex.ofReal_inv, Complex.ofReal_re]
    rw [show ((Real.sqrt (1 - x))⁻¹ : ℝ) = (1 - x) ^ (-(1/2) : ℝ) by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg h1x.le]]
  simp only [Function.comp_def, Complex.reCLM_apply] at hs ⊢
  rw [funext hterm, hrhs] at hs
  exact hs

/-! ## The weight, the summands and term-by-term integration -/

/-- The weight `x^{k-1/2}(1-x)^{r/2-1/2}`. -/
def Wt (r k : ℕ) (x : ℝ) : ℝ := x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2)

/-- The term of the cosine series multiplied by the weight. -/
def Fn (r : ℕ) (t : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * Real.cos (k * t) * Wt r k x

/-- The real part function whose positivity is the crux. -/
def Gt (t : ℝ) (x : ℝ) : ℝ :=
  (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re

theorem Jb_eq_setIntegral (r k : ℕ) :
    Jb r k = ∫ x in Set.Ioo (0 : ℝ) 1, Wt r k x := by
  have h : Jb r k = ∫ x in Set.Ioo (0 : ℝ) 1,
      x ^ ((k : ℝ) - 1/2) * (1 - x) ^ ((r : ℝ)/2 - 1/2) := by
    rw [Jb, intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
      integral_Ioc_eq_integral_Ioo]
  rw [h]
  rfl

theorem Wt_nonneg (r k : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) : 0 ≤ Wt r k x := by
  rw [Wt]
  exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.rpow_nonneg (by linarith [hx.2]) _)

theorem Wt_le_invSqrt (r k : ℕ) (hr : 2 ≤ r) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    Wt r k x ≤ x ^ (-(1/2) : ℝ) := by
  have h2r : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hα : 0 ≤ (r : ℝ)/2 - 1/2 := by linarith
  have hx0 : 0 < x := hx.1
  have hx1 : x < 1 := hx.2
  have hA : (1 - x) ^ ((r : ℝ)/2 - 1/2) ≤ 1 :=
    Real.rpow_le_one (by linarith) (by linarith) hα
  have hA0 : 0 ≤ (1 - x) ^ ((r : ℝ)/2 - 1/2) := Real.rpow_nonneg (by linarith) _
  have hB : x ^ ((k:ℝ)) ≤ 1 := Real.rpow_le_one hx0.le hx1.le (Nat.cast_nonneg k)
  have hC : 0 ≤ x ^ (-(1/2) : ℝ) := Real.rpow_nonneg hx0.le _
  have hW : Wt r k x = x ^ (k:ℝ) * x ^ (-(1/2) : ℝ) * (1 - x) ^ ((r : ℝ)/2 - 1/2) := by
    rw [Wt, ← Real.rpow_add hx0,
      show ((k : ℝ) + -(1/2)) = (k : ℝ) - 1/2 by ring]
  rw [hW]
  have hstep : x ^ (k:ℝ) * x ^ (-(1/2) : ℝ) * (1 - x) ^ ((r : ℝ)/2 - 1/2)
      ≤ 1 * x ^ (-(1/2) : ℝ) * 1 := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_right hB hC
    · exact hA
    · exact hA0
    · exact mul_nonneg zero_le_one hC
  linarith [hstep]

theorem integral_invSqrt :
    ∫ x in Set.Ioo (0:ℝ) 1, x ^ (-(1/2) : ℝ) = 2 := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  norm_num

theorem integrable_invSqrt :
    IntegrableOn (fun x : ℝ => x ^ (-(1/2) : ℝ)) (Set.Ioo (0:ℝ) 1) :=
  (intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0:ℝ) < 1)).mpr
    (by norm_num : (-1:ℝ) < -(1/2))

theorem continuousOn_Wt (r k : ℕ) : ContinuousOn (Wt r k) (Set.Ioo (0:ℝ) 1) := by
  have h1 : ContinuousOn (fun x : ℝ => x ^ ((k:ℝ) - 1/2)) (Set.Ioo (0:ℝ) 1) :=
    continuousOn_id.rpow_const (fun x hx => Or.inl hx.1.ne')
  have h2 : ContinuousOn (fun x : ℝ => (1 - x) ^ ((r:ℝ)/2 - 1/2)) (Set.Ioo (0:ℝ) 1) :=
    (continuousOn_const.sub continuousOn_id).rpow_const
      (fun x hx => Or.inl (by linarith [hx.2] : (1:ℝ) - x ≠ 0))
  exact h1.mul h2

theorem coeff_nonneg (k : ℕ) :
    (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := by
  rw [Grothendieck.risingFact]
  exact div_nonneg (Finset.prod_nonneg fun i _ => by positivity) (Nat.cast_nonneg k.factorial)

theorem integrable_Wt (r k : ℕ) (hr : 2 ≤ r) :
    Integrable (Wt r k) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine Integrable.mono' integrable_invSqrt ?_ ?_
  · exact (continuousOn_Wt r k).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Wt_nonneg r k hx)]
    exact Wt_le_invSqrt r k hr hx

theorem integral_Wt (r k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, Wt r k x = Jb r k :=
  (Jb_eq_setIntegral r k).symm

theorem integral_Fn (r : ℕ) (t : ℝ) (k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, Fn r t k x
      = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * Real.cos (k * t) * Jb r k := by
  rw [show (fun x => Fn r t k x) = (fun x => ((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * Real.cos (k * t)) * Wt r k x) from rfl, MeasureTheory.integral_const_mul,
    integral_Wt r k]

theorem integrable_Fn (r : ℕ) (t : ℝ) (k : ℕ) (hr : 2 ≤ r) :
    Integrable (Fn r t k) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  refine (integrable_invSqrt.const_mul |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)|).mono' ?_ ?_
  · have h1 : ContinuousOn (fun x : ℝ => Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
        (Set.Ioo (0:ℝ) 1) := continuousOn_const
    have h2 : ContinuousOn (fun x : ℝ => Real.cos (k * t)) (Set.Ioo (0:ℝ) 1) := by fun_prop
    exact ((h1.mul h2).mul (continuousOn_Wt r k)).aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hc : (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := coeff_nonneg k
    have hW : Wt r k x ≤ x ^ (-(1/2) : ℝ) := Wt_le_invSqrt r k hr hx
    have hW0 : 0 ≤ Wt r k x := Wt_nonneg r k hx
    have hb : 0 ≤ x ^ (-(1/2) : ℝ) := Real.rpow_nonneg hx.1.le _
    have hcos : |Real.cos (k * t)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
    calc ‖Fn r t k x‖
        = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * |Real.cos (k * t)| * Wt r k x := by
          rw [Real.norm_eq_abs, show Fn r t k x = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
            * Real.cos (k * t) * Wt r k x from rfl, abs_mul, abs_mul, abs_of_nonneg hc,
            abs_of_nonneg hW0]
      _ = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
            * (|Real.cos (k * t)| * Wt r k x) := by ring
      _ ≤ (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)) * (1 * x ^ (-(1/2) : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hc
          exact mul_le_mul hcos hW hW0 (by norm_num)
      _ = |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * x ^ (-(1/2) : ℝ) := by
          rw [abs_of_nonneg hc]; ring
/-! ## Summability of the integrated norms -/

/-- `a_k = (1/2)_k (1/2)_k / ((r/2+1)_k k!)`. -/
def ak (r k : ℕ) : ℝ :=
  Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
    / (Grothendieck.risingFact (cc r) k * (k.factorial : ℝ))

theorem ak_eq (r k : ℕ) :
    ak r k = Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
      / (Grothendieck.risingFact (cc r) k * (k.factorial : ℝ)) := rfl

theorem risingFact_succ' (a : ℝ) (k : ℕ) :
    Grothendieck.risingFact a (k+1) = Grothendieck.risingFact a k * (a + (k:ℝ)) := by
  rw [Grothendieck.risingFact, Grothendieck.risingFact, Finset.prod_range_succ]

theorem risingFact_pos_one_half (k : ℕ) : 0 < Grothendieck.risingFact (1/2) k := by
  rw [Grothendieck.risingFact]
  exact Finset.prod_pos fun i _ => by positivity

theorem cc_pos (r : ℕ) : 0 < cc r := by simp only [cc]; positivity

theorem risingFact_pos_cc (r k : ℕ) : 0 < Grothendieck.risingFact (cc r) k := by
  rw [Grothendieck.risingFact]
  exact Finset.prod_pos fun i _ => by
    have h : (0:ℝ) < cc r := cc_pos r
    positivity

theorem ak_nonneg (r k : ℕ) : 0 ≤ ak r k := by
  rw [ak_eq]
  exact div_nonneg (mul_nonneg (risingFact_pos_one_half k).le (risingFact_pos_one_half k).le)
    (mul_nonneg (risingFact_pos_cc r k).le (by positivity))

theorem ak_pos (r k : ℕ) : 0 < ak r k := by
  rw [ak_eq]
  exact div_pos (mul_pos (risingFact_pos_one_half k) (risingFact_pos_one_half k))
    (mul_pos (risingFact_pos_cc r k) (by positivity))

theorem ak_ratio (r k : ℕ) :
    ak r (k+1) = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) := by
  have h1 : Grothendieck.risingFact (1/2) (k+1)
      = Grothendieck.risingFact (1/2) k * (1/2 + (k:ℝ)) := risingFact_succ' (1/2) k
  have h2 : Grothendieck.risingFact (cc r) (k+1)
      = Grothendieck.risingFact (cc r) k * (cc r + (k:ℝ)) := risingFact_succ' (cc r) k
  have h3 : (((k+1).factorial : ℕ) : ℝ) = (k.factorial : ℝ) * ((k:ℝ)+1) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have hA : (0:ℝ) < Grothendieck.risingFact (1/2) k := risingFact_pos_one_half k
  have hB : (0:ℝ) < Grothendieck.risingFact (cc r) k := risingFact_pos_cc r k
  have hC : (0:ℝ) < (k.factorial : ℝ) := by positivity
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  rw [ak_eq, ak_eq, h1, h2, h3]
  field_simp

theorem ak_step (r k : ℕ) (hr : 2 ≤ r) :
    ak r (k+1) * ((k:ℝ)+2)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
  have h2r : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hcc : (2:ℝ) ≤ cc r := by simp only [cc]; linarith
  have hA : (0:ℝ) < ak r k := ak_pos r k
  have hD : (0:ℝ) < cc r + (k:ℝ) := by have := cc_pos r; positivity
  have hE : (0:ℝ) < (k:ℝ) + 1 := by positivity
  have hF : (0:ℝ) < (k:ℝ) + 2 := by positivity
  have hkey : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 := by nlinarith
  have hfrac : (1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2
      ≤ ((k:ℝ)+1)^2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    have h1 : (2:ℝ) + (k:ℝ) ≤ cc r + (k:ℝ) := by linarith
    have h2 : (1/2 + (k:ℝ))^2 * ((k:ℝ)+2)^2 ≤ ((k:ℝ)+1)^3 * ((k:ℝ)+2) := by
      have hm := mul_le_mul_of_nonneg_right hkey hF.le
      linarith [hm]
    have h3 : ((k:ℝ)+1)^3 * ((k:ℝ)+2) ≤ ((k:ℝ)+1)^3 * (cc r + (k:ℝ)) :=
      mul_le_mul_of_nonneg_left (by linarith : (k:ℝ)+2 ≤ cc r + (k:ℝ)) (by positivity)
    nlinarith [h2, h3]
  rw [ak_ratio]
  calc ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1))) * ((k:ℝ)+2)^2
      = ak r k * ((1/2 + (k:ℝ))^2 / ((cc r + (k:ℝ)) * ((k:ℝ)+1)) * ((k:ℝ)+2)^2) := by ring
    _ ≤ ak r k * ((k:ℝ)+1)^2 := by
        exact mul_le_mul_of_nonneg_left hfrac hA.le

theorem ak_mul_le (r k : ℕ) (hr : 2 ≤ r) : ak r k * ((k:ℝ)+1)^2 ≤ 1 := by
  induction k with
  | zero =>
    rw [ak_eq]
    norm_num [Grothendieck.risingFact]
  | succ k ih =>
    have h1 : ak r (k+1) * (((k:ℝ)+1)+1)^2 ≤ ak r k * ((k:ℝ)+1)^2 := by
      have h := ak_step r k hr
      rwa [show ((k:ℝ)+1)+1 = (k:ℝ)+2 by ring]
    have h1' : ak r (k+1) * ((↑(k+1) : ℝ)+1)^2 ≤ ak r k * ((↑k : ℝ)+1)^2 := by
      push_cast
      exact h1
    have h2 : ak r k * ((↑k : ℝ)+1)^2 ≤ 1 := ih
    linarith

theorem ak_le (r k : ℕ) (hr : 2 ≤ r) : ak r k ≤ 1/((k:ℝ)+1)^2 := by
  have h := ak_mul_le r k hr
  have hpos : (0:ℝ) < ((k:ℝ)+1)^2 := by positivity
  rw [le_div_iff₀ hpos]
  exact h

theorem summable_inv_sq : Summable (fun k : ℕ => 1/((k:ℝ)+1)^2) := by
  have h : Summable (fun n : ℕ => 1/((n:ℝ))^2) :=
    (Real.summable_one_div_nat_pow).mpr (by norm_num : 1 < 2)
  have h' : Summable (fun n : ℕ => 1/(((n+1 : ℕ) : ℝ))^2) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1/((n:ℝ))^2) 1).mpr h
  simpa [Nat.cast_add, Nat.cast_one] using h'

theorem integral_norm_Fn (r : ℕ) (t : ℝ) (k : ℕ) :
    ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖
      = |Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * |Real.cos (k * t)| * Jb r k := by
  have hae : ∀ᵐ x ∂(volume.restrict (Set.Ioo (0:ℝ) 1)), ‖Fn r t k x‖
      = (|Grothendieck.risingFact (1/2) k / (k.factorial : ℝ)| * |Real.cos (k * t)|) * Wt r k x := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hW0 : 0 ≤ Wt r k x := Wt_nonneg r k hx
    rw [Real.norm_eq_abs, show Fn r t k x = (Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * Real.cos (k * t) * Wt r k x from rfl, abs_mul, abs_mul, abs_of_nonneg hW0]
  rw [MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_const_mul, integral_Wt r k]

theorem integral_norm_Fn_le (r : ℕ) (t : ℝ) (k : ℕ) (hr : 2 ≤ r) :
    ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖ ≤ Jb r 0 * ak r k := by
  rw [integral_norm_Fn, abs_of_nonneg (coeff_nonneg k)]
  have hcos : |Real.cos (k * t)| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  have hJ : 0 ≤ Jb r k := (Jb_pos r k).le
  have hc : (0:ℝ) ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) := coeff_nonneg k
  have step : Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * |Real.cos (k * t)| * Jb r k
      ≤ Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * 1 * Jb r k := by
    apply mul_le_mul_of_nonneg_right _ hJ
    exact mul_le_mul_of_nonneg_left hcos hc
  have heq : Grothendieck.risingFact (1/2) k / (k.factorial : ℝ) * 1 * Jb r k = Jb r 0 * ak r k := by
    rw [Jb_ratio r k, ak_eq]
    field_simp
  linarith [step, heq.le, heq.ge]

theorem summable_integral_norm_Fn (r : ℕ) (t : ℝ) (hr : 2 ≤ r) :
    Summable (fun k : ℕ => ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖) := by
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_inv_sq).mul_left (Jb r 0))
  · exact integral_nonneg fun x => norm_nonneg _
  · calc ∫ x in Set.Ioo (0:ℝ) 1, ‖Fn r t k x‖ ≤ Jb r 0 * ak r k := integral_norm_Fn_le r t k hr
      _ ≤ Jb r 0 * (1/((k:ℝ)+1)^2) := by
          exact mul_le_mul_of_nonneg_left (ak_le r k hr) (Jb_pos r 0).le
/-! ## Continuity of `Gt` and the final assembly -/

theorem Gt_pos {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 < Gt t x :=
  re_inv_cpow_pos ht0 ht1

theorem continuousOn_Gt {t : ℝ} (ht0 : 0 < t) (ht1 : t < π) :
    ContinuousOn (Gt t) (Set.Icc (0 : ℝ) 1) := by
  have hbase : Continuous fun x : ℝ => 1 - (x : ℂ) * Complex.exp (t * Complex.I) := by
    fun_prop
  have hslit : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ∈ Complex.slitPlane := by
    intro x hx
    rw [Complex.mem_slitPlane_iff]
    exact Or.inl (re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1)
  have hcpow : ContinuousOn
      (fun x : ℝ => (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) := by
    intro x hx
    exact hbase.continuousWithinAt.cpow continuousWithinAt_const (hslit x hx)
  have hnonzero : ∀ x ∈ Set.Icc (0 : ℝ) 1,
      (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ) ≠ 0 := by
    intro x hx
    refine cpow_half_ne_zero (z := 1 - (x : ℂ) * Complex.exp (t * Complex.I)) ?_
    intro h
    have hzre := re_one_sub_mul_exp_pos x hx.1 hx.2 ht0 ht1
    rw [h] at hzre
    simp at hzre
  have hinv : ContinuousOn
      (fun x : ℝ => 1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ))
      (Set.Icc (0 : ℝ) 1) :=
    continuousOn_const.div hcpow hnonzero
  exact Complex.continuous_re.comp_continuousOn hinv

theorem hasSum_Fn (r : ℕ) (t : ℝ) {x : ℝ} (hx : x ∈ Set.Ioo (0:ℝ) 1) :
    HasSum (fun k : ℕ => Fn r t k x) (Gt t x * Wt r 0 x) := by
  have hWk : ∀ k : ℕ, Wt r k x = x ^ k * Wt r 0 x := by
    intro k
    have h : x ^ ((k:ℝ)) * x ^ (-(1/2) : ℝ) = x ^ ((k:ℝ) - 1/2) := by
      rw [← Real.rpow_add hx.1]
      ring_nf
    rw [Wt, Wt, ← Real.rpow_natCast x k, ← h]
    ring
  have h := (hasSum_series_re (t := t) x hx.1.le hx.2).mul_left (Wt r 0 x)
  have hterm : ∀ k : ℕ, Wt r 0 x * ((Grothendieck.risingFact (1/2) k / (k.factorial : ℝ))
      * x ^ k * Real.cos (k * t)) = Fn r t k x := by
    intro k
    rw [Fn, hWk k]
    ring
  rw [funext hterm] at h
  have h2 : HasSum (fun k : ℕ => Fn r t k x) (Gt t x * Wt r 0 x) := by
    rw [show Gt t x = (1 / (1 - (x : ℂ) * Complex.exp (t * Complex.I)) ^ (1/2 : ℂ)).re from rfl,
      mul_comm]
    exact h
  exact h2

theorem integral_tsum_Fn (r : ℕ) (t : ℝ) (hr : 2 ≤ r) :
    HasSum (fun k : ℕ => ∫ x in Set.Ioo (0:ℝ) 1, Fn r t k x)
      (∫ x in Set.Ioo (0:ℝ) 1, ∑' k : ℕ, Fn r t k x) := by
  refine MeasureTheory.hasSum_integral_of_summable_integral_norm (fun k => integrable_Fn r t k hr) ?_
  simpa using summable_integral_norm_Fn r t hr

theorem integral_tsum_Fn_eq (r : ℕ) (t : ℝ) :
    ∫ x in Set.Ioo (0:ℝ) 1, ∑' k : ℕ, Fn r t k x
      = ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
  refine MeasureTheory.integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  exact (hasSum_Fn r t hx).tsum_eq

theorem integrable_Gt_Wt (r : ℕ) (t : ℝ) (hr : 2 ≤ r) (ht0 : 0 < t) (ht1 : t < π) :
    Integrable (fun x => Gt t x * Wt r 0 x) (volume.restrict (Set.Ioo (0:ℝ) 1)) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn (continuousOn_Gt ht0 ht1)
  refine Integrable.mono' ((integrable_Wt r 0 hr).const_mul C) ?_ ?_
  · have h1 : ContinuousOn (fun x => Gt t x * Wt r 0 x) (Set.Ioo (0:ℝ) 1) :=
      (continuousOn_Gt ht0 ht1).mono Set.Ioo_subset_Icc_self |>.mul (continuousOn_Wt r 0)
    exact h1.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hW0 : 0 ≤ Wt r 0 x := Wt_nonneg r 0 hx
    have hb : ‖Gt t x‖ ≤ C := hC x ⟨hx.1.le, hx.2.le⟩
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hW0]
    exact mul_le_mul_of_nonneg_right hb hW0

theorem integral_Gt_Wt_pos (r : ℕ) (t : ℝ) (hr : 2 ≤ r) (ht0 : 0 < t) (ht1 : t < π) :
    0 < ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
  obtain ⟨x₀, hx₀, hmin⟩ := isCompact_Icc.exists_isMinOn
    (Set.nonempty_Icc.mpr (by norm_num : (0:ℝ) ≤ 1)) (continuousOn_Gt ht0 ht1)
  have hmono : ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x
      ≤ ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
    refine MeasureTheory.integral_mono_ae ((integrable_Wt r 0 hr).const_mul _)
      (integrable_Gt_Wt r t hr ht0 ht1) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    have hle : Gt t x₀ ≤ Gt t x := hmin ⟨hx.1.le, hx.2.le⟩
    exact mul_le_mul_of_nonneg_right hle (Wt_nonneg r 0 hx)
  have hval : ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x = Gt t x₀ * Jb r 0 := by
    rw [MeasureTheory.integral_const_mul, integral_Wt r 0]
  have hm : 0 < Gt t x₀ := Gt_pos ht0 ht1 x₀ hx₀
  have hJ : 0 < Jb r 0 := Jb_pos r 0
  have hpos : 0 < ∫ x in Set.Ioo (0:ℝ) 1, Gt t x₀ * Wt r 0 x := by
    rw [hval]; exact mul_pos hm hJ
  linarith

end VietorisAux

namespace Grothendieck

open VietorisAux

/-- Vietoris-type positivity (Leaf 4 of the roadmap). -/
theorem vietoris_pos_proof (r : ℕ) (hr : 2 ≤ r) (t : ℝ) (ht0 : 0 < t)
    (ht1 : t < Real.pi) :
    0 < ∑' k : ℕ, (Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
      / (Grothendieck.risingFact ((r:ℝ)/2 + 1) k * (k.factorial : ℝ))) * Real.cos (k * t) := by
  have hS := integral_tsum_Fn r t hr
  rw [integral_tsum_Fn_eq r t] at hS
  have hterms : ∀ k : ℕ, ∫ x in Set.Ioo (0:ℝ) 1, Fn r t k x
      = Jb r 0 * (ak r k * Real.cos (k * t)) := by
    intro k
    rw [integral_Fn, Jb_ratio r k, ak_eq]
    field_simp
  rw [funext hterms] at hS
  have htsum : Jb r 0 * (∑' k : ℕ, ak r k * Real.cos (k * t))
      = ∫ x in Set.Ioo (0:ℝ) 1, Gt t x * Wt r 0 x := by
    rw [← hS.tsum_eq, tsum_mul_left]
  have hpos := integral_Gt_Wt_pos r t hr ht0 ht1
  have hJ : 0 < Jb r 0 := Jb_pos r 0
  have key : ∑' k : ℕ, ak r k * Real.cos (k * t) > 0 := by
    have hne : (∑' k : ℕ, ak r k * Real.cos (k * t)) ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at htsum
      linarith
    rcases le_total (∑' k : ℕ, ak r k * Real.cos (k * t)) 0 with h | h
    · have h1 : Jb r 0 * (∑' k : ℕ, ak r k * Real.cos (k * t)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hJ.le h
      linarith
    · exact lt_of_le_of_ne h (Ne.symm hne)
  have hgoal : ∑' k : ℕ, (Grothendieck.risingFact (1/2) k * Grothendieck.risingFact (1/2) k
      / (Grothendieck.risingFact ((r:ℝ)/2 + 1) k * (k.factorial : ℝ))) * Real.cos (k * t)
      = ∑' k : ℕ, ak r k * Real.cos (k * t) := by
    refine tsum_congr (fun k => ?_)
    rw [ak_eq]
    simp only [cc]
  rw [hgoal]
  exact key

end Grothendieck

open Grothendieck in
theorem solution (r : ℕ) (hr : 2 ≤ r) (t : ℝ) (ht0 : 0 < t) (ht1 : t < Real.pi) :
    0 < ∑' k : ℕ, (risingFact (1/2) k * risingFact (1/2) k
      / (risingFact ((r:ℝ)/2 + 1) k * (k.factorial : ℝ))) * Real.cos (k * t) :=
  Grothendieck.vietoris_pos_proof r hr t ht0 ht1
