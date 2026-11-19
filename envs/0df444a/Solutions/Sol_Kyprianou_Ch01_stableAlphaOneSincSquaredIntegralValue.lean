-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneSincSquaredIntegralValue
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T08:29:46.000257+00:00
-- url     : https://prove2.me/submissions/3c961598-d614-47c5-a93e-709e2bc0db98

import Mathlib

open MeasureTheory Set Complex

/-- Laplace transform of `sin²`: `∫₀^∞ e^{-tx} sin² x dx = 2 / (t (t² + 4))`. -/
lemma laplace_sin_sq (t : ℝ) (ht : 0 < t) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-t * x) * Real.sin x ^ 2 = 2 / (t * (t ^ 2 + 4)) := by
  set a : ℂ := (-t : ℂ) with ha
  set b : ℂ := (-t : ℂ) + 2 * I with hb
  have hare : a.re < 0 := by simp [ha]; linarith
  have hbre : b.re < 0 := by simp [hb]; linarith
  have hpt : ∀ x : ℝ, Real.exp (-t * x) * Real.sin x ^ 2 =
      RCLike.re ((Complex.exp (a * x) - Complex.exp (b * x)) / 2) := by
    intro x
    have e1 : Complex.exp (a * x) = ((Real.exp (-t * x) : ℝ) : ℂ) := by
      rw [ha]; push_cast; ring_nf
    have e2 : Complex.exp (b * x) = ((Real.exp (-t * x) : ℝ) : ℂ) * Complex.exp ((2 * x : ℝ) * I) := by
      rw [hb, Complex.ofReal_exp, ← Complex.exp_add]; congr 1; push_cast; ring
    rw [e1, e2, RCLike.re_to_complex]
    simp only [Complex.div_ofNat_re, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, zero_mul, sub_zero, Complex.exp_ofReal_mul_I_re]
    rw [Real.cos_two_mul, Real.cos_sq']
    ring
  simp_rw [hpt]
  have hia := integrableOn_exp_mul_complex_Ioi hare 0
  have hib := integrableOn_exp_mul_complex_Ioi hbre 0
  have hint : Integrable (fun x : ℝ => (Complex.exp (a * x) - Complex.exp (b * x)) / 2)
      (volume.restrict (Ioi 0)) := (hia.sub hib).div_const 2
  rw [integral_re hint, integral_div, integral_sub hia hib,
    integral_exp_mul_complex_Ioi hare, integral_exp_mul_complex_Ioi hbre]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, RCLike.re_to_complex]
  rw [ha, hb]
  have h4 : (t : ℝ) ^ 2 + 4 ≠ 0 := by positivity
  simp [Complex.div_re, Complex.normSq_apply]
  field_simp
  ring

/-- `∫₀^∞ t e^{-xt} dt = 1/x²` for `x > 0`. -/
lemma inner_inv_sq (x : ℝ) (hx : 0 < x) :
    ∫ t in Ioi (0 : ℝ), t * Real.exp (-x * t) = 1 / x ^ 2 := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := x) (by norm_num) hx
  have h2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.Gamma_add_one (by norm_num), Real.Gamma_one]; norm_num
  rw [h2, mul_one] at h
  rw [show (1 / x ^ 2) = (1 / x) ^ (2 : ℝ) by rw [Real.rpow_two, div_pow, one_pow], ← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  rw [show (2 : ℝ) - 1 = 1 by norm_num, Real.rpow_one, neg_mul]

/-- `∫₀^∞ t · 2/(t (t²+4)) dt = π/2`. -/
lemma outer_value : ∫ t in Ioi (0 : ℝ), t * (2 / (t * (t ^ 2 + 4))) = Real.pi / 2 := by
  have hcongr : ∀ t ∈ Ioi (0 : ℝ), t * (2 / (t * (t ^ 2 + 4))) = (1 / 2) * (1 + (t / 2) ^ 2)⁻¹ := by
    intro t ht
    have : 0 < t := ht
    field_simp
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hcongr, integral_const_mul]
  have hsub := integral_comp_mul_left_Ioi (fun u : ℝ => (1 + u ^ 2)⁻¹) 0 (by norm_num : (0:ℝ) < 1 / 2)
  simp only [mul_zero, smul_eq_mul] at hsub
  rw [show (fun a : ℝ => (1 + (a / 2) ^ 2)⁻¹) = fun a : ℝ => (1 + (1 / 2 * a) ^ 2)⁻¹ by
    funext a; ring_nf]
  rw [hsub, integral_Ioi_inv_one_add_sq, Real.arctan_zero]
  ring

theorem solution : (∫ x in Set.Ioi (0 : ℝ), (Real.sin x / x) ^ 2) = Real.pi / 2 := by
  set F : ℝ × ℝ → ℝ := fun p => p.2 * Real.exp (-p.1 * p.2) * Real.sin p.1 ^ 2 with hF
  have hFc : Continuous F := by rw [hF]; fun_prop
  have hFnn : ∀ p : ℝ × ℝ, p.2 ∈ Ioi (0 : ℝ) → 0 ≤ F p := fun p hp => by
    have : (0 : ℝ) < p.2 := hp
    simp only [hF]; positivity
  -- inner integral in x, for fixed t
  have hlap : ∀ t ∈ Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F (x, t) = t * (2 / (t * (t ^ 2 + 4))) := by
    intro t ht
    rw [← laplace_sin_sq t ht, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x _ => ?_)
    simp only [hF]; ring_nf
  have hint : Integrable F ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    rw [integrable_prod_iff' hFc.aestronglyMeasurable]
    constructor
    · refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have : (0 : ℝ) < t := ht
      have hexp : IntegrableOn (fun x : ℝ => Real.exp (-t * x)) (Ioi 0) :=
        (integrableOn_exp_mul_Ioi (by linarith : -t < 0) 0)
      refine Integrable.mono' (hexp.const_mul t) (hFc.comp (by fun_prop)).aestronglyMeasurable ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun x _ => ?_
      simp only [hF, Function.comp, Real.norm_eq_abs]
      rw [abs_of_nonneg (by positivity)]
      have := Real.sin_sq_le_one x
      have h1 : 0 ≤ t * Real.exp (-x * t) := by positivity
      calc t * Real.exp (-x * t) * Real.sin x ^ 2 ≤ t * Real.exp (-x * t) * 1 := by gcongr
        _ = t * Real.exp (-t * x) := by ring_nf
    · have hg : Integrable (fun t : ℝ => (1 / 2 : ℝ) * (1 + (t / 2) ^ 2)⁻¹) :=
        (integrable_inv_one_add_sq.comp_div (by norm_num : (2 : ℝ) ≠ 0)).const_mul _
      refine (hg.integrableOn (s := Ioi 0)).congr ?_
      refine (ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_
      have ht0 : (0 : ℝ) < t := ht
      have hn : ∫ x in Ioi (0 : ℝ), ‖F (x, t)‖ = ∫ x in Ioi (0 : ℝ), F (x, t) :=
        setIntegral_congr_fun measurableSet_Ioi (fun x _ => Real.norm_of_nonneg (hFnn (x, t) ht))
      simp only
      rw [hn, hlap t ht]
      field_simp
      ring
  have hinner : ∀ x ∈ Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F (x, t) = (Real.sin x / x) ^ 2 := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    simp only [hF]
    rw [integral_mul_const, inner_inv_sq x hx0]
    field_simp
  calc (∫ x in Ioi (0 : ℝ), (Real.sin x / x) ^ 2)
      = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), F (x, t) :=
        (setIntegral_congr_fun measurableSet_Ioi hinner).symm
    _ = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), F (x, t) :=
        integral_integral_swap (f := fun x t => F (x, t)) hint
    _ = ∫ t in Ioi (0 : ℝ), t * (2 / (t * (t ^ 2 + 4))) := setIntegral_congr_fun measurableSet_Ioi hlap
    _ = Real.pi / 2 := outer_value
