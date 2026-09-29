-- Prove2me | solution 1 for LanglandsTunnell.integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/28f6397f-86bc-5038-9526-c4e370bddb49

import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.ExpDecay
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Normed.Group.Indicator
import Mathlib.Analysis.SpecialFunctions.PolynomialExp
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Theorems.Thm_LanglandsTunnell_exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion

set_option autoImplicit false

open MeasureTheory Set Filter Topology Polynomial Asymptotics

namespace FbInt

noncomputable def G : ℝ → ℂ := fun s : ℝ => (Real.exp (-(Real.pi * s ^ 2)) : ℂ)

noncomputable def QG (q : ℝ[X]) (s : ℝ) : ℝ := q.eval s * Real.exp (-(Real.pi * s ^ 2))

noncomputable def nextq (q : ℝ[X]) : ℝ[X] := derivative q - C (2 * Real.pi) * X * q

noncomputable def qseq : ℕ → ℝ[X]
  | 0 => 1
  | n + 1 => nextq (qseq n)

lemma hasDerivAt_QG (q : ℝ[X]) (s : ℝ) :
    HasDerivAt (QG q) (QG (nextq q) s) s := by
  have h1 : HasDerivAt (fun x : ℝ => q.eval x) (q.derivative.eval s) s := q.hasDerivAt s
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (-(Real.pi * x ^ 2)))
      (Real.exp (-(Real.pi * s ^ 2)) * (-(Real.pi * ((2 : ℕ) * s ^ (2 - 1))))) s :=
    (((hasDerivAt_pow 2 s).const_mul Real.pi).neg).exp
  have h3 := h1.mul h2
  unfold QG nextq
  convert h3 using 1
  · rfl
  · rfl
  · rfl
  simp only [eval_sub, eval_mul, eval_C, eval_X]
  push_cast
  ring

lemma hasDerivAt_QG_complex (q : ℝ[X]) (s : ℝ) :
    HasDerivAt (fun x : ℝ => (QG q x : ℂ)) ((QG (nextq q) s : ℝ) : ℂ) s :=
  (hasDerivAt_QG q s).ofReal_comp

lemma iteratedDeriv_G (n : ℕ) : iteratedDeriv n G = fun s : ℝ => ((QG (qseq n) s : ℝ) : ℂ) := by
  induction n with
  | zero =>
    funext s
    simp [iteratedDeriv_zero, G, QG, qseq]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext s
    exact (hasDerivAt_QG_complex (qseq n) s).deriv

lemma continuous_QG (q : ℝ[X]) : Continuous (QG q) :=
  q.continuous.mul (by fun_prop)

lemma base_pos {w v σ : ℝ} (hw : 0 < w) (hσ : v / w < σ) : 0 < σ * w - v := by
  have := (div_lt_iff₀ hw).mp hσ
  linarith

lemma base_zero {w v : ℝ} (hw : 0 < w) : v / w * w - v = 0 := by
  rw [div_mul_cancel₀ v hw.ne']; ring

lemma continuousOn_real (b : ℝ) (q : ℝ[X]) (w v : ℝ) (hw : 0 < w) :
    ContinuousOn (fun σ : ℝ => (σ * w - v) ^ b * |QG q σ|) (Ioi (v / w)) := by
  refine ContinuousOn.mul ?_ ?_
  · refine ContinuousOn.rpow_const (by fun_prop) ?_
    intro x hx
    exact Or.inl (base_pos hw hx).ne'
  · exact ((continuous_QG q).abs).continuousOn

lemma continuousOn_cpx (β : ℂ) (q : ℝ[X]) (w v : ℝ) (hw : 0 < w) :
    ContinuousOn (fun σ : ℝ => (((σ * w - v : ℝ) : ℂ) ^ β) * ((QG q σ : ℝ) : ℂ)) (Ioi (v / w)) := by
  intro σ hσ
  apply ContinuousAt.continuousWithinAt
  refine ContinuousAt.mul ?_ ?_
  · have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ β) (σ * w - v) :=
      Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr (base_pos hw hσ).ne')
    exact h1.comp (f := fun x : ℝ => x * w - v) (by fun_prop : Continuous (fun x : ℝ => x * w - v)).continuousAt
  · exact (Complex.continuous_ofReal.comp (continuous_QG q)).continuousAt

lemma tendsto_tail (b : ℝ) (hb : -1 < b) (q : ℝ[X]) (w v : ℝ) (hw : 0 < w) :
    Tendsto (fun σ : ℝ => ((σ * w - v) ^ b * |QG q σ|) / Real.exp (-σ)) atTop (𝓝 0) := by
  obtain ⟨L, hL⟩ : ∃ L : ℝ, L = (b + 1) * w + 3 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = L ^ 2 / (4 * Real.pi) - (b + 1) * v := ⟨_, rfl⟩
  have hpi := Real.pi_pos

  have hq : ∀ᶠ σ in atTop, |q.eval σ| ≤ Real.exp σ := by
    have h := (Polynomial.tendsto_div_exp_atTop q).abs
    have h1 : ∀ᶠ σ in atTop, |q.eval σ / Real.exp σ| < 1 := (tendsto_order.1 h).2 1 (by simp)
    filter_upwards [h1] with σ hσ
    rw [abs_div, abs_of_pos (Real.exp_pos σ), div_lt_one (Real.exp_pos σ)] at hσ
    exact hσ.le

  have hbound : ∀ᶠ σ in atTop,
      ((σ * w - v) ^ b * |QG q σ|) / Real.exp (-σ) ≤ w⁻¹ * Real.exp (K - σ) := by
    filter_upwards [hq, eventually_gt_atTop (v / w + 1)] with σ hqσ hσ
    have hx : w < σ * w - v := by
      have h1 : (v / w + 1) * w < σ * w := mul_lt_mul_of_pos_right hσ hw
      have h2 : (v / w + 1) * w = v + w := by rw [add_mul, div_mul_cancel₀ v hw.ne', one_mul]
      linarith
    have hx0 : 0 < σ * w - v := hw.trans hx

    have s1 : (σ * w - v) ^ b ≤ (σ * w - v) ^ (b + 1) / w := by
      rw [Real.rpow_add_one hx0.ne', le_div_iff₀ hw]
      exact mul_le_mul_of_nonneg_left hx.le (Real.rpow_nonneg hx0.le b)

    have s2 : (σ * w - v) ^ (b + 1) ≤ Real.exp ((b + 1) * (σ * w - v)) := by
      have h := Real.rpow_le_rpow hx0.le
        (by linarith [Real.add_one_le_exp (σ * w - v)] : σ * w - v ≤ Real.exp (σ * w - v))
        (by linarith : 0 ≤ b + 1)
      rw [← Real.exp_mul] at h
      have e : Real.exp ((σ * w - v) * (b + 1)) = Real.exp ((b + 1) * (σ * w - v)) := by
        rw [mul_comm]
      rw [e] at h
      exact h

    have s3 : |QG q σ| ≤ Real.exp σ * Real.exp (-(Real.pi * σ ^ 2)) := by
      unfold QG
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right hqσ (Real.exp_pos _).le

    have key : -Real.pi * σ ^ 2 + L * σ ≤ L ^ 2 / (4 * Real.pi) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (2 * Real.pi * σ - L)]
    have s4 : (b + 1) * (σ * w - v) + σ + -(Real.pi * σ ^ 2) + σ ≤ K - σ := by
      have hid : K - σ - ((b + 1) * (σ * w - v) + σ + -(Real.pi * σ ^ 2) + σ)
          = L ^ 2 / (4 * Real.pi) - (-Real.pi * σ ^ 2 + L * σ) := by
        rw [hK, hL]; ring
      linarith [key, hid]

    have e1 : ((σ * w - v) ^ b * |QG q σ|) / Real.exp (-σ)
        = (σ * w - v) ^ b * |QG q σ| * Real.exp σ := by
      rw [Real.exp_neg, div_inv_eq_mul]
    rw [e1]
    have A : (σ * w - v) ^ b * |QG q σ|
        ≤ (Real.exp ((b + 1) * (σ * w - v)) / w) * (Real.exp σ * Real.exp (-(Real.pi * σ ^ 2))) :=
      mul_le_mul (s1.trans (div_le_div_of_nonneg_right s2 hw.le)) s3 (abs_nonneg _)
        (div_nonneg (Real.exp_pos _).le hw.le)
    have B := mul_le_mul_of_nonneg_right A (Real.exp_pos σ).le
    refine B.trans ?_
    have e2 : (Real.exp ((b + 1) * (σ * w - v)) / w) * (Real.exp σ * Real.exp (-(Real.pi * σ ^ 2)))
        * Real.exp σ = w⁻¹ * Real.exp ((b + 1) * (σ * w - v) + σ + -(Real.pi * σ ^ 2) + σ) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr s4) (inv_nonneg.mpr hw.le)

  have hlim : Tendsto (fun σ : ℝ => w⁻¹ * Real.exp (K - σ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (Real.exp K)).const_mul w⁻¹
    rw [mul_zero, mul_zero] at h
    refine h.congr' ?_
    filter_upwards with σ
    rw [sub_eq_add_neg, Real.exp_add]

  have hnn : ∀ᶠ σ in atTop, 0 ≤ ((σ * w - v) ^ b * |QG q σ|) / Real.exp (-σ) := by
    filter_upwards [eventually_gt_atTop (v / w)] with σ hσ
    have := (base_pos hw hσ).le
    positivity
  exact squeeze_zero' hnn hbound hlim

lemma integrableOn_real (b : ℝ) (hb : -1 < b) (q : ℝ[X]) (w v : ℝ) (hw : 0 < w) :
    IntegrableOn (fun σ : ℝ => (σ * w - v) ^ b * |QG q σ|) (Ioi (v / w)) := by
  have hsplit : Ioi (v / w) = Ioc (v / w) (v / w + 1) ∪ Ioi (v / w + 1) :=
    (Ioc_union_Ioi_eq_Ioi (by linarith)).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  ·
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := v / w) (b := v / w + 1)).exists_bound_of_continuousOn
      ((continuous_QG q).continuousOn)
    have hrpow : IntegrableOn (fun σ : ℝ => (σ * w - v) ^ b) (Ioc (v / w) (v / w + 1)) := by
      have h0 : IntervalIntegrable (fun x : ℝ => x ^ b) volume 0 w := intervalIntegral.intervalIntegrable_rpow' hb
      have h1 : IntervalIntegrable (fun x : ℝ => (x - v) ^ b) volume (0 + v) (w + v) := h0.comp_sub_right v
      have h2 : IntervalIntegrable (fun x : ℝ => (x * w - v) ^ b) volume ((0 + v) / w) ((w + v) / w) :=
        h1.comp_mul_right (c := w)
      have e1 : (0 + v) / w = v / w := by rw [zero_add]
      have e2 : (w + v) / w = v / w + 1 := by rw [add_div, div_self hw.ne', add_comm]
      rw [e1, e2] at h2
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp h2
    refine Integrable.mono' (hrpow.mul_const M) ?_ ?_
    · exact ((continuousOn_real b q w v hw).mono Ioc_subset_Ioi_self).aestronglyMeasurable
        measurableSet_Ioc
    · refine (ae_restrict_mem measurableSet_Ioc).mono ?_
      intro σ hσ
      have hx0 : 0 ≤ σ * w - v := (base_pos hw hσ.1).le
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (Real.rpow_nonneg hx0 b)]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hx0 b)
      have := hM σ (Ioc_subset_Icc_self hσ)
      rwa [Real.norm_eq_abs] at this
  ·
    refine integrable_of_isBigO_exp_neg zero_lt_one ?_ ?_
    · refine (continuousOn_real b q w v hw).mono ?_
      intro σ hσ
      exact lt_of_lt_of_le (lt_add_one (v / w)) hσ
    · have h := (isLittleO_iff_tendsto (f := fun σ : ℝ => (σ * w - v) ^ b * |QG q σ|)
        (g := fun σ : ℝ => Real.exp (-σ)) (l := atTop)
        (by intro x hx; exact absurd hx (Real.exp_pos _).ne')).mpr (tendsto_tail b hb q w v hw)
      refine h.isBigO.congr_right ?_
      intro σ
      rw [neg_mul, one_mul]

lemma integrableOn_cpx (β : ℂ) (hβ : -1 < β.re) (q : ℝ[X]) (w v : ℝ) (hw : 0 < w) :
    IntegrableOn (fun σ : ℝ => (((σ * w - v : ℝ) : ℂ) ^ β) * ((QG q σ : ℝ) : ℂ)) (Ioi (v / w)) := by
  refine Integrable.mono' (integrableOn_real β.re hβ q w v hw) ?_ ?_
  · exact (continuousOn_cpx β q w v hw).aestronglyMeasurable measurableSet_Ioi
  · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
    intro σ hσ
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (base_pos hw hσ), Complex.norm_real,
      Real.norm_eq_abs]

lemma gauss_mul_moment (n : ℕ) (σ : ℝ) :
    (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
        ∫ z : ℝ, ((σ : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)
      = (-(2 * (Real.pi : ℂ)))⁻¹ ^ n * ((QG (qseq n) σ : ℝ) : ℂ) := by
  have hB : (Real.exp (-(Real.pi * σ ^ 2)) : ℂ) *
        ∫ z : ℝ, ((σ : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)
      = (-(2 * (Real.pi : ℂ)))⁻¹ ^ n * iteratedDeriv n G σ :=
    LanglandsTunnell.exp_neg_pi_mul_sq_mul_integral_sub_I_mul_pow_mul_exp_eq_iteratedDeriv n σ
  rw [iteratedDeriv_G] at hB
  exact hB

lemma QG_bound (q : ℝ[X]) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ σ : ℝ, |QG q σ| ≤ B * Real.exp (-(Real.pi * σ ^ 2 / 2)) := by
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = ∑ i ∈ Finset.range (q.natDegree + 1),
      |q.coeff i| * (i.factorial : ℝ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hpi := Real.pi_pos
  refine ⟨A * Real.exp (1 / (2 * Real.pi)), by positivity, ?_⟩
  intro σ
  have h1 : |q.eval σ| ≤ A * Real.exp |σ| := by
    rw [Polynomial.eval_eq_sum_range, hA, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_pow]
    have hfac : |σ| ^ i ≤ (i.factorial : ℝ) * Real.exp |σ| := by
      have h := Real.pow_div_factorial_le_exp (x := |σ|) (abs_nonneg σ) i
      rw [div_le_iff₀ (by positivity)] at h
      linarith [mul_comm (Real.exp |σ|) (i.factorial : ℝ)]
    calc |q.coeff i| * |σ| ^ i ≤ |q.coeff i| * ((i.factorial : ℝ) * Real.exp |σ|) :=
          mul_le_mul_of_nonneg_left hfac (abs_nonneg _)
      _ = |q.coeff i| * (i.factorial : ℝ) * Real.exp |σ| := by ring
  have h2 : |σ| + -(Real.pi * σ ^ 2) ≤ 1 / (2 * Real.pi) + -(Real.pi * σ ^ 2 / 2) := by
    have hsq : |σ| ^ 2 = σ ^ 2 := sq_abs σ
    have key' : 2 * Real.pi * |σ| - Real.pi ^ 2 * σ ^ 2 ≤ 1 := by
      nlinarith [sq_nonneg (Real.pi * |σ| - 1), hsq]
    have key : |σ| - Real.pi * σ ^ 2 / 2 ≤ 1 / (2 * Real.pi) := by
      have e : |σ| - Real.pi * σ ^ 2 / 2 = (2 * Real.pi * |σ| - Real.pi ^ 2 * σ ^ 2) / (2 * Real.pi) := by
        rw [eq_div_iff (by positivity)]
        ring
      rw [e]
      exact div_le_div_of_nonneg_right key' (by positivity)
    linarith
  unfold QG
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc |q.eval σ| * Real.exp (-(Real.pi * σ ^ 2))
      ≤ A * Real.exp |σ| * Real.exp (-(Real.pi * σ ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = A * Real.exp (|σ| + -(Real.pi * σ ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ A * Real.exp (1 / (2 * Real.pi) + -(Real.pi * σ ^ 2 / 2)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hA0
    _ = A * Real.exp (1 / (2 * Real.pi)) * Real.exp (-(Real.pi * σ ^ 2 / 2)) := by
        rw [Real.exp_add]; ring

lemma rpow_mul_exp_neg_div_sq_le (β c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, ∀ w : ℝ, 0 < w → w ≤ 1 → w ^ β * Real.exp (-(c / w ^ 2)) ≤ C := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, -β ≤ 2 * (N : ℝ) := ⟨Nat.ceil |β|, by
    have h1 : |β| ≤ (Nat.ceil |β| : ℝ) := Nat.le_ceil _
    have h2 : -β ≤ |β| := neg_le_abs β
    have h3 : (0 : ℝ) ≤ (Nat.ceil |β| : ℝ) := Nat.cast_nonneg _
    linarith⟩
  refine ⟨(N.factorial : ℝ) / c ^ N, ?_⟩
  intro w hw hw1
  have hw2 : 0 < w ^ 2 := by positivity
  have s1 : w ^ β ≤ (w ^ (2 * N))⁻¹ := by
    have h := Real.rpow_le_rpow_of_exponent_ge hw hw1 (show -(2 * (N : ℝ)) ≤ β by linarith)
    have e : w ^ (-(2 * (N : ℝ))) = (w ^ (2 * N))⁻¹ := by
      rw [Real.rpow_neg hw.le, show (2 * (N : ℝ)) = ((2 * N : ℕ) : ℝ) by push_cast; ring,
        Real.rpow_natCast]
    rw [e] at h
    exact h
  have s2 : Real.exp (-(c / w ^ 2)) ≤ (N.factorial : ℝ) / (c / w ^ 2) ^ N := by
    have h := Real.pow_div_factorial_le_exp (x := c / w ^ 2) (le_of_lt (div_pos hc hw2)) N
    have hpos : 0 < (c / w ^ 2) ^ N / (N.factorial : ℝ) := by positivity
    have h' := inv_anti₀ hpos h
    rw [inv_div] at h'
    rw [Real.exp_neg]
    exact h'
  calc w ^ β * Real.exp (-(c / w ^ 2)) ≤ (w ^ (2 * N))⁻¹ * ((N.factorial : ℝ) / (c / w ^ 2) ^ N) :=
        mul_le_mul s1 s2 (Real.exp_pos _).le (by positivity)
    _ = (N.factorial : ℝ) / c ^ N := by
        rw [div_pow, pow_mul]
        field_simp

lemma integrableOn_core (β c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun w : ℝ => w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2)))
      (Ioi 0) := by
  have hpi := Real.pi_pos
  have hcont : ContinuousOn
      (fun w : ℝ => w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2))) (Ioi 0) := by
    refine ContinuousOn.mul (ContinuousOn.mul ?_ ?_) ?_
    · exact continuousOn_id.rpow_const (fun x hx => Or.inl (ne_of_gt hx))
    · exact (Continuous.continuousOn (by fun_prop))
    · refine Real.continuous_exp.comp_continuousOn ?_
      refine ContinuousOn.neg ?_
      refine ContinuousOn.div continuousOn_const (by fun_prop) ?_
      intro x hx
      exact pow_ne_zero 2 (ne_of_gt hx)
  have hsplit : Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 := (Ioc_union_Ioi_eq_Ioi zero_le_one).symm
  rw [hsplit]
  refine IntegrableOn.union ?_ ?_
  · obtain ⟨C, hC⟩ := rpow_mul_exp_neg_div_sq_le β c hc
    have hconst : IntegrableOn (fun _ : ℝ => C) (Ioc (0 : ℝ) 1) :=
      integrableOn_const (hs := measure_Ioc_lt_top.ne)
    refine Integrable.mono' hconst ?_ ?_
    · exact (hcont.mono Ioc_subset_Ioi_self).aestronglyMeasurable measurableSet_Ioc
    · refine (ae_restrict_mem measurableSet_Ioc).mono ?_
      intro w hw
      have hw0 : 0 < w := hw.1
      have e1 : Real.exp (-(Real.pi * w ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      have hrp : 0 ≤ w ^ β := Real.rpow_nonneg hw0.le β
      have hnn : 0 ≤ w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2)) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have step : w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2))
          ≤ w ^ β * Real.exp (-(c / w ^ 2)) := by
        have := mul_le_mul_of_nonneg_left e1 hrp
        have h2 := mul_le_mul_of_nonneg_right this (Real.exp_pos (-(c / w ^ 2))).le
        simpa using h2
      exact step.trans (hC w hw0 hw.2)
  · have hmaj : IntegrableOn (fun x : ℝ => x ^ (max β 0) * Real.exp (-Real.pi * x ^ (2 : ℝ))) (Ioi 1) :=
      (integrableOn_rpow_mul_exp_neg_mul_rpow (lt_of_lt_of_le neg_one_lt_zero (le_max_right β 0))
        (by norm_num : (0 : ℝ) < 2) hpi).mono_set (Ioi_subset_Ioi zero_le_one)
    refine Integrable.mono' hmaj ?_ ?_
    · exact (hcont.mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable measurableSet_Ioi
    · refine (ae_restrict_mem measurableSet_Ioi).mono ?_
      intro w hw
      have hw1 : 1 < w := hw
      have hw0 : 0 < w := zero_lt_one.trans hw1
      have hrp : 0 ≤ w ^ β := Real.rpow_nonneg hw0.le β
      have hnn : 0 ≤ w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2)) := by
        positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have e1 : w ^ β ≤ w ^ (max β 0) := Real.rpow_le_rpow_of_exponent_le hw1.le (le_max_left _ _)
      have e2 : Real.exp (-(c / w ^ 2)) ≤ 1 := by
        rw [Real.exp_le_one_iff, neg_nonpos]; positivity
      have e3 : Real.exp (-(Real.pi * w ^ 2)) = Real.exp (-Real.pi * w ^ (2 : ℝ)) := by
        rw [Real.rpow_two, neg_mul]
      have hE : 0 ≤ Real.exp (-(Real.pi * w ^ 2)) := (Real.exp_pos _).le
      have step1 : w ^ β * Real.exp (-(Real.pi * w ^ 2)) * Real.exp (-(c / w ^ 2))
          ≤ w ^ β * Real.exp (-(Real.pi * w ^ 2)) := by
        have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hrp hE)
        simpa using this
      have step2 : w ^ β * Real.exp (-(Real.pi * w ^ 2))
          ≤ w ^ (max β 0) * Real.exp (-(Real.pi * w ^ 2)) :=
        mul_le_mul_of_nonneg_right e1 hE
      rw [← e3]
      exact step1.trans step2

lemma fibre_gamma (α : ℝ) (hα : -1 < α) (lam : ℝ) (hlam : 0 < lam) (v w : ℝ) (hw : 0 < w) :
    IntegrableOn (fun σ : ℝ => (σ * w - v) ^ α * Real.exp (-(lam * (σ * w - v)))) (Ioi (v / w)) ∧
      ∫ σ in Ioi (v / w), (σ * w - v) ^ α * Real.exp (-(lam * (σ * w - v)))
        = w⁻¹ * ((1 / lam) ^ (α + 1) * Real.Gamma (α + 1)) := by

  set h : ℝ → ℝ := fun t => t ^ α * Real.exp (-(lam * t)) with hh
  have hh_int : IntegrableOn h (Ioi 0) := by
    have := integrableOn_rpow_mul_exp_neg_mul_rpow hα (zero_lt_one' ℝ) hlam
    refine this.congr_fun ?_ measurableSet_Ioi
    intro t ht
    simp only [hh, Real.rpow_one, neg_mul]
  have hh_val : ∫ t in Ioi 0, h t = (1 / lam) ^ (α + 1) * Real.Gamma (α + 1) := by
    have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := α + 1) (r := lam) (by linarith) hlam
    rw [add_sub_cancel_right] at this
    simpa only [hh] using this

  set hv' : ℝ → ℝ := fun y => h (y - v) with hhv
  have hind : (Ioi v).indicator hv' = fun y => (Ioi (0 : ℝ)).indicator h (y - v) := by
    funext y
    simp only [hhv, Set.indicator_apply, mem_Ioi, sub_pos]
  have hv_int : IntegrableOn hv' (Ioi v) := by
    rw [← integrable_indicator_iff measurableSet_Ioi, hind]
    exact ((integrable_indicator_iff measurableSet_Ioi).mpr hh_int).comp_sub_right v
  have hv_val : ∫ y in Ioi v, hv' y = ∫ t in Ioi 0, h t := by
    rw [← integral_indicator measurableSet_Ioi, hind,
      integral_sub_right_eq_self (fun t => (Ioi (0 : ℝ)).indicator h t) v,
      integral_indicator measurableSet_Ioi]

  have hwv : w * (v / w) = v := by field_simp
  have hsc_int : IntegrableOn (fun σ : ℝ => hv' (w * σ)) (Ioi (v / w)) := by
    rw [integrableOn_Ioi_comp_mul_left_iff hv' (v / w) hw, hwv]
    exact hv_int
  have hsc_val : ∫ σ in Ioi (v / w), hv' (w * σ) = w⁻¹ * ∫ y in Ioi v, hv' y := by
    rw [integral_comp_mul_left_Ioi hv' (v / w) hw, hwv, smul_eq_mul]

  have hfun : ∀ σ : ℝ, hv' (w * σ) = (σ * w - v) ^ α * Real.exp (-(lam * (σ * w - v))) := by
    intro σ
    simp only [hhv, hh, mul_comm w σ]
  constructor
  · exact hsc_int.congr_fun (fun σ _ => hfun σ) measurableSet_Ioi
  · rw [← hh_val, ← hv_val, ← hsc_val]
    refine setIntegral_congr_fun measurableSet_Ioi ?_
    intro σ _
    exact (hfun σ).symm

lemma inner_le (α : ℝ) (hα : -1 < α) (q : ℝ[X]) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ σ : ℝ, |QG q σ| ≤ B * Real.exp (-(Real.pi * σ ^ 2 / 2)))
    (v : ℝ) (hv : 0 < v) (w : ℝ) (hw : 0 < w) :
    ∫ σ in Ioi (v / w), (σ * w - v) ^ α * |QG q σ|
      ≤ B * Real.exp (-((Real.pi * v ^ 2 / 2) / w ^ 2)) *
          (w⁻¹ * ((1 / (Real.pi * v / w ^ 2)) ^ (α + 1) * Real.Gamma (α + 1))) := by
  have hpi := Real.pi_pos
  set lam : ℝ := Real.pi * v / w ^ 2 with hlam_def
  have hlam : 0 < lam := by rw [hlam_def]; positivity
  set E0 : ℝ := Real.exp (-((Real.pi * v ^ 2 / 2) / w ^ 2)) with hE0
  obtain ⟨hm_int, hm_val⟩ := fibre_gamma α hα lam hlam v w hw
  have hpt : ∀ σ ∈ Ioi (v / w), (σ * w - v) ^ α * |QG q σ|
      ≤ B * E0 * ((σ * w - v) ^ α * Real.exp (-(lam * (σ * w - v)))) := by
    intro σ hσ
    have hx0 : 0 ≤ σ * w - v := (base_pos hw hσ).le
    have hgauss : Real.exp (-(Real.pi * σ ^ 2 / 2)) ≤ E0 * Real.exp (-(lam * (σ * w - v))) := by
      rw [hE0, ← Real.exp_add, Real.exp_le_exp, hlam_def]
      have e : -((Real.pi * v ^ 2 / 2) / w ^ 2) + -(Real.pi * v / w ^ 2 * (σ * w - v))
          - (-(Real.pi * σ ^ 2 / 2)) = Real.pi / (2 * w ^ 2) * (σ * w - v) ^ 2 := by
        field_simp
        ring
      have : 0 ≤ Real.pi / (2 * w ^ 2) * (σ * w - v) ^ 2 := by positivity
      linarith
    calc (σ * w - v) ^ α * |QG q σ|
        ≤ (σ * w - v) ^ α * (B * Real.exp (-(Real.pi * σ ^ 2 / 2))) :=
          mul_le_mul_of_nonneg_left (hB σ) (Real.rpow_nonneg hx0 α)
      _ ≤ (σ * w - v) ^ α * (B * (E0 * Real.exp (-(lam * (σ * w - v))))) := by
          gcongr
      _ = B * E0 * ((σ * w - v) ^ α * Real.exp (-(lam * (σ * w - v)))) := by ring
  have hle := setIntegral_mono_on (integrableOn_real α hα q w v hw) (hm_int.const_mul (B * E0))
    measurableSet_Ioi hpt
  refine hle.trans ?_
  rw [integral_const_mul, hm_val]

def R (v : ℝ) : Set (ℝ × ℝ) := {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2}

lemma measurableSet_R (v : ℝ) : MeasurableSet (R v) :=
  (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_const (measurable_fst.mul measurable_snd)))

lemma mem_R_iff {v w : ℝ} (hv : 0 < v) (hw : 0 < w) (σ : ℝ) :
    (σ, w) ∈ R v ↔ σ ∈ Ioi (v / w) := by
  simp only [R, mem_setOf_eq, mem_Ioi]
  constructor
  · rintro ⟨-, -, h⟩
    rw [div_lt_iff₀ hw]
    linarith
  · intro h
    have h' := (div_lt_iff₀ hw).mp h
    refine ⟨?_, hw, by linarith⟩
    by_contra hs
    have hs' := not_lt.mp hs
    nlinarith

lemma indicator_section {E : Type*} [Zero E] {v w : ℝ} (hv : 0 < v) (hw : 0 < w)
    (g : ℝ × ℝ → E) (σ : ℝ) :
    (R v).indicator g (σ, w) = (Ioi (v / w)).indicator (fun s : ℝ => g (s, w)) σ := by
  by_cases hmem : σ ∈ Ioi (v / w)
  · rw [indicator_of_mem hmem, indicator_of_mem ((mem_R_iff hv hw σ).mpr hmem)]
  · rw [indicator_of_notMem hmem,
      indicator_of_notMem (fun h => hmem ((mem_R_iff hv hw σ).mp h))]

lemma indicator_section_zero {E : Type*} [Zero E] {v w : ℝ} (hw : ¬ 0 < w)
    (g : ℝ × ℝ → E) (σ : ℝ) : (R v).indicator g (σ, w) = 0 := by
  apply indicator_of_notMem
  intro h
  exact hw h.2.1

noncomputable def cn (n : ℕ) : ℂ := (-(2 * (Real.pi : ℂ)))⁻¹ ^ n

noncomputable def W (k : ℤ) (w : ℝ) : ℂ := (w : ℂ) ^ k * (Real.exp (-(Real.pi * w ^ 2)) : ℂ)

noncomputable def A (a : ℂ) (n : ℕ) (v : ℝ) (σ w : ℝ) : ℂ :=
  ((σ * w - v : ℝ) : ℂ) ^ a * ((QG (qseq n) σ : ℝ) : ℂ)

noncomputable def F (a : ℂ) (k : ℤ) (n : ℕ) (v : ℝ) : ℝ × ℝ → ℂ := fun q : ℝ × ℝ =>
  ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
    (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
    ∫ z : ℝ, ((q.1 : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ)

noncomputable def F' (a : ℂ) (k : ℤ) (n : ℕ) (v : ℝ) : ℝ × ℝ → ℂ := fun q : ℝ × ℝ =>
  cn n * W k q.2 * A a n v q.1 q.2

lemma F_eq (a : ℂ) (k : ℤ) (n : ℕ) (v : ℝ) : F a k n v = F' a k n v := by
  funext q
  simp only [F, F', cn, W, A]
  have hB := gauss_mul_moment n q.1
  have hexp : (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ)
      = (Real.exp (-(Real.pi * q.1 ^ 2)) : ℂ) * (Real.exp (-(Real.pi * q.2 ^ 2)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  linear_combination (((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
    (Real.exp (-(Real.pi * q.2 ^ 2)) : ℂ)) * hB

lemma norm_W {k : ℤ} {w : ℝ} (hw : 0 < w) :
    ‖W k w‖ = w ^ k * Real.exp (-(Real.pi * w ^ 2)) := by
  unfold W
  rw [norm_mul, norm_zpow, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_pos hw, abs_of_pos (Real.exp_pos _)]

lemma norm_A {a : ℂ} {n : ℕ} {v σ w : ℝ} (hw : 0 < w) (hσ : v / w < σ) :
    ‖A a n v σ w‖ = (σ * w - v) ^ a.re * |QG (qseq n) σ| := by
  unfold A
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (base_pos hw hσ), Complex.norm_real,
    Real.norm_eq_abs]

lemma continuousOn_F' (a : ℂ) (k : ℤ) (n : ℕ) (v : ℝ) : ContinuousOn (F' a k n v) (R v) := by
  intro q hq
  obtain ⟨hσ, hw, hvq⟩ := hq
  apply ContinuousAt.continuousWithinAt
  unfold F'
  refine (continuousAt_const.mul ?_).mul ?_
  · unfold W
    refine ContinuousAt.mul ?_ ?_
    · have h1 : ContinuousAt (fun z : ℂ => z ^ k) ((q.2 : ℝ) : ℂ) :=
        continuousAt_zpow₀ _ _ (Or.inl (by exact_mod_cast hw.ne'))
      exact h1.comp (f := fun p : ℝ × ℝ => ((p.2 : ℝ) : ℂ))
        (Complex.continuous_ofReal.comp continuous_snd).continuousAt
    · exact (Complex.continuous_ofReal.comp (by fun_prop :
        Continuous fun p : ℝ × ℝ => Real.exp (-(Real.pi * p.2 ^ 2)))).continuousAt
  · unfold A
    refine ContinuousAt.mul ?_ ?_
    · have hpos : 0 < q.1 * q.2 - v := by linarith
      have h1 : ContinuousAt (fun y : ℝ => (y : ℂ) ^ a) (q.1 * q.2 - v) :=
        Complex.continuousAt_ofReal_cpow_const _ _ (Or.inr hpos.ne')
      exact h1.comp (f := fun p : ℝ × ℝ => p.1 * p.2 - v)
        (by fun_prop : Continuous (fun p : ℝ × ℝ => p.1 * p.2 - v)).continuousAt
    · exact ((Complex.continuous_ofReal.comp (continuous_QG (qseq n))).comp
        continuous_fst).continuousAt

theorem integrableOn_F' (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (F' a k n v) (R v) := by
  have hpi := Real.pi_pos
  have hR := measurableSet_R v
  obtain ⟨B, hB0, hB⟩ := QG_bound (qseq n)

  set S : ℝ × ℝ → ℂ := fun p => (R v).indicator (F' a k n v) p.swap with hS
  have hS_meas : AEStronglyMeasurable S ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have h1 : AEStronglyMeasurable ((R v).indicator (F' a k n v)) (volume : Measure (ℝ × ℝ)) :=
      (aestronglyMeasurable_indicator_iff hR).mpr
        ((continuousOn_F' a k n v).aestronglyMeasurable hR)
    rw [Measure.volume_eq_prod] at h1
    exact h1.prod_swap

  have hsec : ∀ w : ℝ, Integrable (fun σ : ℝ => S (w, σ)) volume := by
    intro w
    by_cases hw : 0 < w
    · have e : (fun σ : ℝ => S (w, σ)) = (Ioi (v / w)).indicator (fun σ : ℝ => F' a k n v (σ, w)) := by
        funext σ
        simp only [hS, Prod.swap]
        exact indicator_section hv hw _ σ
      rw [e, integrable_indicator_iff measurableSet_Ioi]
      exact (integrableOn_cpx a ha (qseq n) w v hw).const_mul (cn n * W k w)
    · have e : (fun σ : ℝ => S (w, σ)) = fun _ => 0 := by
        funext σ
        simp only [hS, Prod.swap]
        exact indicator_section_zero hw _ σ
      rw [e]
      exact integrable_zero _ _ _

  set g : ℝ → ℝ := fun w => ‖cn n‖ * ‖W k w‖ *
      (B * Real.exp (-((Real.pi * v ^ 2 / 2) / w ^ 2)) *
        (w⁻¹ * ((1 / (Real.pi * v / w ^ 2)) ^ (a.re + 1) * Real.Gamma (a.re + 1)))) with hg
  have hg_int : IntegrableOn g (Ioi 0) := by
    set β : ℝ := (k : ℝ) + (-1) + 2 * (a.re + 1) with hβ
    set K : ℝ := ‖cn n‖ * B * Real.Gamma (a.re + 1) / (Real.pi * v) ^ (a.re + 1) with hK
    have hcore : IntegrableOn (fun w : ℝ => K * (w ^ β * Real.exp (-(Real.pi * w ^ 2)) *
        Real.exp (-((Real.pi * v ^ 2 / 2) / w ^ 2)))) (Ioi 0) :=
      (integrableOn_core β (Real.pi * v ^ 2 / 2) (by positivity)).const_mul K
    refine IntegrableOn.congr_fun hcore ?_ measurableSet_Ioi
    intro w hw
    have hw0 : 0 < w := hw
    rw [hg]
    beta_reduce
    rw [norm_W hw0]
    have e1 : (w : ℝ) ^ k = w ^ (k : ℝ) := (Real.rpow_intCast w k).symm
    have e2 : w⁻¹ = w ^ (-1 : ℝ) := (Real.rpow_neg_one w).symm
    have e3 : (1 / (Real.pi * v / w ^ 2)) ^ (a.re + 1)
        = w ^ (2 * (a.re + 1)) / (Real.pi * v) ^ (a.re + 1) := by
      rw [one_div_div, Real.div_rpow (sq_nonneg w) (by positivity),
        show w ^ 2 = w ^ (2 : ℝ) from (Real.rpow_two w).symm, ← Real.rpow_mul hw0.le]
    have e4 : w ^ (k : ℝ) * w ^ (-1 : ℝ) * w ^ (2 * (a.re + 1)) = w ^ β := by
      rw [hβ, Real.rpow_add hw0, Real.rpow_add hw0]
    rw [e1, e2, e3, hK, ← e4]
    ring
  have hmaj : Integrable (fun w : ℝ => ∫ σ : ℝ, ‖S (w, σ)‖) volume := by
    have hΦ_meas : AEStronglyMeasurable (fun w : ℝ => ∫ σ : ℝ, ‖S (w, σ)‖) volume :=
      hS_meas.norm.integral_prod_right'
    have hgI : Integrable ((Ioi (0 : ℝ)).indicator g) volume :=
      (integrable_indicator_iff measurableSet_Ioi).mpr hg_int
    refine Integrable.mono' hgI hΦ_meas (ae_of_all _ ?_)
    intro w
    by_cases hw : 0 < w
    · rw [indicator_of_mem (mem_Ioi.mpr hw)]
      have hnn : 0 ≤ ∫ σ : ℝ, ‖S (w, σ)‖ := integral_nonneg (fun _ => norm_nonneg _)
      rw [Real.norm_of_nonneg hnn]

      have e : (fun σ : ℝ => ‖S (w, σ)‖)
          = (Ioi (v / w)).indicator (fun σ : ℝ => ‖F' a k n v (σ, w)‖) := by
        funext σ
        simp only [hS, Prod.swap]
        rw [indicator_section hv hw _ σ, norm_indicator_eq_indicator_norm]
      rw [e, integral_indicator measurableSet_Ioi]
      have e2 : ∫ σ in Ioi (v / w), ‖F' a k n v (σ, w)‖
          = ∫ σ in Ioi (v / w), (‖cn n‖ * ‖W k w‖) * ((σ * w - v) ^ a.re * |QG (qseq n) σ|) := by
        refine setIntegral_congr_fun measurableSet_Ioi ?_
        intro σ hσ
        simp only [F']
        rw [norm_mul, norm_mul, norm_A hw hσ]
      rw [e2, integral_const_mul, hg]
      exact mul_le_mul_of_nonneg_left (inner_le a.re ha (qseq n) B hB0 hB v hv w hw)
        (by positivity)
    · rw [indicator_of_notMem (fun h : w ∈ Ioi (0 : ℝ) => hw (mem_Ioi.mp h))]
      have e : (fun σ : ℝ => ‖S (w, σ)‖) = fun _ => 0 := by
        funext σ
        simp only [hS, Prod.swap]
        rw [indicator_section_zero hw _ σ, norm_zero]
      rw [e, integral_zero, norm_zero]
  have hS_int : Integrable S ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (integrable_prod_iff hS_meas).mpr ⟨ae_of_all _ hsec, hmaj⟩
  have hT := hS_int.swap
  have e : S ∘ Prod.swap = (R v).indicator (F' a k n v) := by
    funext q
    simp only [hS, Function.comp, Prod.swap_swap]
  rw [e, ← Measure.volume_eq_prod] at hT
  exact (integrable_indicator_iff hR).mp hT

theorem main (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (F a k n v) (R v) := by
  rw [F_eq]
  exact integrableOn_F' a ha k n v hv

end FbInt

theorem solution
    (a : ℂ) (ha : -1 < a.re) (k : ℤ) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    IntegrableOn (fun q : ℝ × ℝ =>
        ((q.1 * q.2 - v : ℝ) : ℂ) ^ a * (q.2 : ℂ) ^ k *
          (Real.exp (-(Real.pi * (q.1 ^ 2 + q.2 ^ 2))) : ℂ) *
          ∫ z : ℝ, ((q.1 : ℂ) - Complex.I * (z : ℂ)) ^ n * (Real.exp (-(Real.pi * z ^ 2)) : ℂ))
      {q : ℝ × ℝ | 0 < q.1 ∧ 0 < q.2 ∧ v < q.1 * q.2} :=
  FbInt.main a ha k n v hv

end S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion
end P2MW
export P2MW.S_LanglandsTunnell_integrableOn_cpow_mul_zpow_mul_exp_mul_gaussMoment_hyperbolicRegion (solution)
