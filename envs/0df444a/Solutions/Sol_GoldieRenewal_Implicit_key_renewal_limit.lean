-- Prove2me | solution 1 for GoldieRenewal.Implicit.key_renewal_limit
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-18T01:57:19.096884+00:00
-- url     : https://prove2.me/submissions/63dfff6d-db45-490b-8195-1b61fab3e276

import Mathlib
import Definitions.Def_GoldieRenewal_Implicit_CramerConditions
import Definitions.Def_GoldieRenewal_Implicit_DRi
import Definitions.Def_GoldieRenewal_Implicit_TailConstants
import Definitions.Def_GoldieRenewal_Implicit_RenewalMeasures

set_option autoImplicit false

open MeasureTheory Filter Topology Real

namespace GoldieRenewal.Implicit.KRT

/-! ## C1: the Fejer kernel `F_a(y) = (1/π) ∫₀^a (1 - θ/a) cos(θ y) dθ` -/

noncomputable def fej (a y : ℝ) : ℝ := (1 / π) * ∫ θ in (0:ℝ)..a, (1 - θ / a) * Real.cos (θ * y)

lemma fej_integral_closed (a y : ℝ) (ha : 0 < a) (hy : y ≠ 0) :
    ∫ θ in (0:ℝ)..a, (1 - θ / a) * Real.cos (θ * y) = (1 - Real.cos (a * y)) / (a * y ^ 2) := by
  have hderiv : ∀ θ ∈ Set.uIcc (0:ℝ) a, HasDerivAt
      (fun θ => (1 - θ / a) * Real.sin (θ * y) / y - Real.cos (θ * y) / (a * y ^ 2))
      ((1 - θ / a) * Real.cos (θ * y)) θ := by
    intro θ _
    have h1 : HasDerivAt (fun θ => θ * y) y θ := by simpa using (hasDerivAt_id θ).mul_const y
    have hs := (Real.hasDerivAt_sin (θ * y)).comp θ h1
    have hc := (Real.hasDerivAt_cos (θ * y)).comp θ h1
    have hl : HasDerivAt (fun θ => 1 - θ / a) (-(1 / a)) θ := by
      have := ((hasDerivAt_id θ).div_const a).const_sub 1
      simpa using this
    have := ((hl.mul hs).div_const y).sub (hc.div_const (a * y ^ 2))
    refine this.congr_deriv ?_
    simp only [Function.comp_apply]
    have ha' : a ≠ 0 := ha.ne'
    field_simp
    ring
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · have : a / a = 1 := div_self ha.ne'
    simp only [this, sub_self, zero_mul, zero_div, zero_sub, Real.sin_zero, mul_zero,
      Real.cos_zero, zero_div]
    field_simp
    ring
  · apply Continuous.intervalIntegrable; fun_prop

lemma fej_eq (a y : ℝ) (ha : 0 < a) (hy : y ≠ 0) :
    fej a y = (1 - Real.cos (a * y)) / (π * a * y ^ 2) := by
  rw [fej, fej_integral_closed a y ha hy]
  field_simp

lemma fej_zero (a : ℝ) (ha : 0 < a) : fej a 0 = a / (2 * π) := by
  rw [fej]
  simp only [mul_zero, Real.cos_zero, mul_one]
  rw [intervalIntegral.integral_sub (by simp) (by apply Continuous.intervalIntegrable; fun_prop)]
  simp only [intervalIntegral.integral_const, intervalIntegral.integral_div, integral_id]
  field_simp
  ring

lemma fej_nonneg (a y : ℝ) (ha : 0 < a) : 0 ≤ fej a y := by
  rcases eq_or_ne y 0 with rfl | hy
  · rw [fej_zero a ha]; positivity
  · rw [fej_eq a y ha hy]
    have := Real.cos_le_one (a * y)
    apply div_nonneg (by linarith); positivity

lemma fej_le_sq (a y : ℝ) (ha : 0 < a) (hy : y ≠ 0) : fej a y ≤ 2 / (π * a * y ^ 2) := by
  rw [fej_eq a y ha hy]
  have := Real.neg_one_le_cos (a * y)
  apply div_le_div_of_nonneg_right (by linarith); positivity

lemma fej_le (a y : ℝ) (ha : 0 < a) : fej a y ≤ a / (2 * π) := by
  rw [fej, ← fej_zero a ha, fej]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply intervalIntegral.integral_mono_on ha.le
  · apply Continuous.intervalIntegrable; fun_prop
  · apply Continuous.intervalIntegrable; fun_prop
  · intro θ hθ
    have h1 : 0 ≤ 1 - θ / a := by
      rw [sub_nonneg, div_le_one ha]; exact hθ.2
    simp only [mul_zero, Real.cos_zero, mul_one]
    exact mul_le_of_le_one_right h1 (Real.cos_le_one _)

/-- `(1 - cos y)/y^2 ≤ 4/(1+y^2)`. -/
lemma one_sub_cos_div_sq_le (y : ℝ) (hy : y ≠ 0) :
    (1 - Real.cos y) / y ^ 2 ≤ 4 * (1 + y ^ 2)⁻¹ := by
  have hy2 : 0 < y ^ 2 := by positivity
  have hc1 : 1 - y ^ 2 / 2 ≤ Real.cos y := Real.one_sub_sq_div_two_le_cos
  have hc2 := Real.neg_one_le_cos y
  rw [div_le_iff₀ hy2, ← div_eq_mul_inv, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  rcases le_total (y ^ 2) 1 with h | h
  · nlinarith
  · nlinarith

end GoldieRenewal.Implicit.KRT

namespace GoldieRenewal.Implicit.KRT

lemma inv_sq_eq_integral (y : ℝ) (hy : 0 < y) :
    ∫ t in Set.Ioi (0:ℝ), t * Real.exp (-(y * t)) = (y ^ 2)⁻¹ := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (r := y) two_pos hy
  have h2 : ((2:ℝ) - 1) = 1 := by norm_num
  simp only [h2, Real.rpow_one, Real.Gamma_two, mul_one] at this
  rw [this, Real.rpow_two, one_div, inv_pow]

lemma integral_exp_neg_mul_Ioi' (t : ℝ) (ht : 0 < t) :
    ∫ y in Set.Ioi (0:ℝ), Real.exp (-(t * y)) = 1 / t := by
  have := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) (r := t) one_pos ht
  simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one, mul_one] at this
  exact this

lemma integral_exp_neg_mul_cos_Ioi (t : ℝ) (ht : 0 < t) :
    IntegrableOn (fun y : ℝ => Real.exp (-(t * y)) * Real.cos y) (Set.Ioi 0) ∧
    ∫ y in Set.Ioi (0:ℝ), Real.exp (-(t * y)) * Real.cos y = t / (1 + t ^ 2) := by
  set a : ℂ := -(t : ℂ) + Complex.I with ha_def
  have ha : a.re < 0 := by simp [a, ht]
  have hre : ∀ y : ℝ, (Complex.exp (a * y)).re = Real.exp (-(t * y)) * Real.cos y := by
    intro y
    rw [Complex.exp_re]
    simp [a]
  have hint := integrableOn_exp_mul_complex_Ioi ha 0
  have hint_re : IntegrableOn (fun y : ℝ => Real.exp (-(t * y)) * Real.cos y) (Set.Ioi 0) := by
    exact hint.re.congr (Eventually.of_forall fun y => by
      simp only [RCLike.re_to_complex]; exact hre y)
  refine ⟨hint_re, ?_⟩
  have h1 : ∫ y in Set.Ioi (0:ℝ), Real.exp (-(t * y)) * Real.cos y
      = (∫ y in Set.Ioi (0:ℝ), Complex.exp (a * y)).re := by
    rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm _ hint]
    simp only [Complex.reCLM_apply, hre]
  rw [h1, integral_exp_mul_complex_Ioi ha 0]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [Complex.div_re]
  simp [a, Complex.normSq_apply]
  field_simp
  ring

lemma integral_one_sub_cos_mul_exp (t : ℝ) (ht : 0 < t) :
    ∫ y in Set.Ioi (0:ℝ), (1 - Real.cos y) * (t * Real.exp (-(y * t))) = (1 + t ^ 2)⁻¹ := by
  obtain ⟨hi, hv⟩ := integral_exp_neg_mul_cos_Ioi t ht
  have he : IntegrableOn (fun y : ℝ => Real.exp (-(t * y))) (Set.Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [integral_exp_neg_mul_Ioi' t ht]; positivity
  have hpt : ∀ y : ℝ, (1 - Real.cos y) * (t * Real.exp (-(y * t)))
      = t * (Real.exp (-(t * y)) - Real.exp (-(t * y)) * Real.cos y) := by
    intro y; rw [mul_comm y t]; ring
  simp_rw [hpt]
  rw [integral_const_mul, integral_sub he hi, integral_exp_neg_mul_Ioi' t ht, hv]
  field_simp
  ring

lemma integrableOn_one_sub_cos_div_sq :
    IntegrableOn (fun y : ℝ => (1 - Real.cos y) / y ^ 2) (Set.Ioi 0) := by
  refine Integrable.mono' ((integrable_inv_one_add_sq.const_mul 4).integrableOn) ?_ ?_
  · exact (by fun_prop : Measurable (fun y : ℝ => (1 - Real.cos y) / y ^ 2)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have h0 : 0 ≤ (1 - Real.cos y) / y ^ 2 := by
      have := Real.cos_le_one y
      apply div_nonneg (by linarith); positivity
    rw [Real.norm_of_nonneg h0]
    exact one_sub_cos_div_sq_le y hy0

lemma integral_Ioi_one_sub_cos_div_sq :
    ∫ y in Set.Ioi (0:ℝ), (1 - Real.cos y) / y ^ 2 = π / 2 := by
  have step1 : ∫ y in Set.Ioi (0:ℝ), (1 - Real.cos y) / y ^ 2
      = ∫ y in Set.Ioi (0:ℝ), ∫ t in Set.Ioi (0:ℝ), (1 - Real.cos y) * (t * Real.exp (-(y * t))) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
    rw [integral_const_mul, inv_sq_eq_integral y hy, div_eq_mul_inv]
  have hcont : Continuous (Function.uncurry fun (y t : ℝ) =>
      (1 - Real.cos y) * (t * Real.exp (-(y * t)))) := by
    simp only [Function.uncurry_def]; fun_prop
  have hint : Integrable (Function.uncurry fun (y t : ℝ) =>
      (1 - Real.cos y) * (t * Real.exp (-(y * t))))
      ((volume.restrict (Set.Ioi (0:ℝ))).prod (volume.restrict (Set.Ioi (0:ℝ)))) := by
    rw [integrable_prod_iff hcont.aestronglyMeasurable]
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      simp only [Function.uncurry_apply_pair]
      apply Integrable.const_mul
      apply Integrable.of_integral_ne_zero
      rw [inv_sq_eq_integral y hy]; exact inv_ne_zero (pow_ne_zero 2 (ne_of_gt hy))
    · refine Integrable.congr integrableOn_one_sub_cos_div_sq ?_
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      have hy' : (0:ℝ) < y := hy
      simp only [Function.uncurry_apply_pair]
      have : ∀ t ∈ Set.Ioi (0:ℝ), ‖(1 - Real.cos y) * (t * Real.exp (-(y * t)))‖
          = (1 - Real.cos y) * (t * Real.exp (-(y * t))) := by
        intro t ht
        have ht' : (0:ℝ) < t := ht
        apply Real.norm_of_nonneg
        have := Real.cos_le_one y
        apply mul_nonneg (by linarith); positivity
      rw [setIntegral_congr_fun measurableSet_Ioi this, integral_const_mul,
        inv_sq_eq_integral y hy', div_eq_mul_inv]
  rw [step1, integral_integral_swap hint]
  have step3 : ∫ t in Set.Ioi (0:ℝ), ∫ y in Set.Ioi (0:ℝ), (1 - Real.cos y) * (t * Real.exp (-(y * t)))
      = ∫ t in Set.Ioi (0:ℝ), (1 + t ^ 2)⁻¹ :=
    setIntegral_congr_fun measurableSet_Ioi (fun t ht => integral_one_sub_cos_mul_exp t ht)
  rw [step3, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero]

lemma one_sub_cos_div_sq_nonneg (y : ℝ) : 0 ≤ (1 - Real.cos y) / y ^ 2 := by
  have := Real.cos_le_one y
  apply div_nonneg (by linarith); positivity

lemma one_sub_cos_div_sq_le' (y : ℝ) : (1 - Real.cos y) / y ^ 2 ≤ 4 * (1 + y ^ 2)⁻¹ := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · exact one_sub_cos_div_sq_le y hy

lemma integrable_one_sub_cos_div_sq : Integrable (fun y : ℝ => (1 - Real.cos y) / y ^ 2) := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul 4) ?_ ?_
  · exact (by fun_prop : Measurable (fun y : ℝ => (1 - Real.cos y) / y ^ 2)).aestronglyMeasurable
  · refine Eventually.of_forall (fun y => ?_)
    rw [Real.norm_of_nonneg (one_sub_cos_div_sq_nonneg y)]
    exact one_sub_cos_div_sq_le' y

lemma integral_one_sub_cos_div_sq : ∫ y, (1 - Real.cos y) / y ^ 2 = π := by
  have hneg := integral_comp_neg_Ioi (0:ℝ) (fun y : ℝ => (1 - Real.cos y) / y ^ 2)
  simp only [neg_zero, Real.cos_neg, even_two.neg_pow] at hneg
  rw [← integral_add_compl measurableSet_Ioi integrable_one_sub_cos_div_sq, Set.compl_Ioi,
    ← hneg, integral_Ioi_one_sub_cos_div_sq]
  ring

lemma fej_ae_eq (a : ℝ) (ha : 0 < a) :
    (fun y => fej a y) =ᵐ[volume] fun y => (a / π) * ((1 - Real.cos (a * y)) / (a * y) ^ 2) := by
  have h0 : ∀ᵐ y : ℝ ∂volume, y ≠ 0 := by
    rw [ae_iff]; simp
  filter_upwards [h0] with y hy
  rw [fej_eq a y ha hy]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

lemma integral_fej (a : ℝ) (ha : 0 < a) : ∫ y, fej a y = 1 := by
  have hc := Measure.integral_comp_mul_left (fun y : ℝ => (1 - Real.cos y) / y ^ 2) a
  rw [integral_congr_ae (fej_ae_eq a ha), integral_const_mul, hc, integral_one_sub_cos_div_sq,
    abs_of_pos (inv_pos.2 ha), smul_eq_mul]
  have ha' : a ≠ 0 := ha.ne'
  field_simp

lemma integrable_fej (a : ℝ) (ha : 0 < a) : Integrable (fun y => fej a y) := by
  apply Integrable.of_integral_ne_zero; rw [integral_fej a ha]; norm_num

lemma fej_ge (a y : ℝ) (ha : 0 < a) (hy : |a * y| ≤ 1) : a / (3 * π) ≤ fej a y := by
  rcases eq_or_ne y 0 with rfl | hy0
  · rw [fej_zero a ha]
    apply div_le_div_of_nonneg_left ha.le (by positivity)
    nlinarith [Real.pi_pos]
  · rw [fej_eq a y ha hy0]
    have hb := Real.cos_bound hy
    have hx2 : (a * y) ^ 2 ≤ 1 := by
      have := sq_abs (a * y)
      nlinarith [abs_nonneg (a * y)]
    have h4 : |a * y| ^ 4 = ((a * y) ^ 2) ^ 2 := by rw [← sq_abs (a * y)]; ring
    rw [h4] at hb
    have hc : Real.cos (a * y) ≤ 1 - (a * y) ^ 2 / 2 + ((a * y) ^ 2) ^ 2 * (5 / 96) := by
      linarith [(abs_le.1 hb).2]
    have h1 : (a * y) ^ 2 / 3 ≤ 1 - Real.cos (a * y) := by nlinarith [sq_nonneg (a * y)]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left h1 Real.pi_pos.le]

end GoldieRenewal.Implicit.KRT

/-! ## C3: Fourier formula for `A_s(t) = Σ sⁿ ∫ F_a(t - x) dη^{*n}` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit Complex

lemma convPow_isProb (η : Measure ℝ) [IsProbabilityMeasure η] :
    ∀ n, IsProbabilityMeasure (convPow η n)
  | 0 => by rw [convPow]; infer_instance
  | n + 1 => by
      have := convPow_isProb η n
      rw [convPow]; infer_instance

lemma charFun_convPow (η : Measure ℝ) [IsProbabilityMeasure η] (θ : ℝ) :
    ∀ n, charFun (convPow η n) θ = charFun η θ ^ n
  | 0 => by rw [convPow, charFun_dirac]; simp
  | n + 1 => by
      have := convPow_isProb η n
      rw [convPow, charFun_conv, charFun_convPow η θ n, pow_succ, mul_comm]

lemma integrable_cexp_ofReal_mul_I (ρ : Measure ℝ) [IsFiniteMeasure ρ] (f : ℝ → ℝ)
    (hf : Continuous f) : Integrable (fun x => Complex.exp ((f x : ℂ) * Complex.I)) ρ := by
  refine Integrable.mono' (integrable_const (1:ℝ)) (Continuous.aestronglyMeasurable (by fun_prop))
    (Eventually.of_forall fun x => ?_)
  rw [Complex.norm_exp_ofReal_mul_I]

lemma integrable_bdd_cont (ρ : Measure ℝ) [IsFiniteMeasure ρ] (f : ℝ → ℝ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ x, |f x| ≤ C) : Integrable f ρ :=
  Integrable.mono' (integrable_const C) hf.aestronglyMeasurable
    (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hC x)

lemma charFun_neg_eq (ρ : Measure ℝ) (θ : ℝ) :
    charFun ρ (-θ) = ∫ x, Complex.exp (((-(θ * x) : ℝ) : ℂ) * Complex.I) ∂ρ := by
  rw [charFun_apply_real]
  congr 1; ext x; push_cast; ring_nf

lemma charFun_neg_re (ρ : Measure ℝ) [IsFiniteMeasure ρ] (θ : ℝ) :
    (charFun ρ (-θ)).re = ∫ x, Real.cos (θ * x) ∂ρ := by
  rw [charFun_neg_eq]
  have h := integral_re (𝕜 := ℂ) (μ := ρ)
    (integrable_cexp_ofReal_mul_I ρ (fun x => -(θ * x)) (by fun_prop))
  simp only [RCLike.re_to_complex] at h
  rw [← h]
  congr 1; ext x
  rw [Complex.exp_ofReal_mul_I_re, Real.cos_neg]

lemma charFun_neg_im (ρ : Measure ℝ) [IsFiniteMeasure ρ] (θ : ℝ) :
    (charFun ρ (-θ)).im = -∫ x, Real.sin (θ * x) ∂ρ := by
  rw [charFun_neg_eq]
  have h := integral_im (𝕜 := ℂ) (μ := ρ)
    (integrable_cexp_ofReal_mul_I ρ (fun x => -(θ * x)) (by fun_prop))
  simp only [RCLike.im_to_complex] at h
  rw [← h, ← integral_neg]
  congr 1; ext x
  rw [Complex.exp_ofReal_mul_I_im, Real.sin_neg]

lemma integral_cos_shift (ρ : Measure ℝ) [IsFiniteMeasure ρ] (θ t : ℝ) :
    ∫ x, Real.cos (θ * (t - x)) ∂ρ
      = (Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun ρ (-θ)).re := by
  rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    charFun_neg_re, charFun_neg_im]
  have hc := integrable_bdd_cont ρ (fun x => Real.cos (θ * x)) (by fun_prop) 1
    (fun x => Real.abs_cos_le_one _)
  have hs := integrable_bdd_cont ρ (fun x => Real.sin (θ * x)) (by fun_prop) 1
    (fun x => Real.abs_sin_le_one _)
  have : ∀ x, Real.cos (θ * (t - x))
      = Real.cos (θ * t) * Real.cos (θ * x) + Real.sin (θ * t) * Real.sin (θ * x) := by
    intro x; rw [mul_sub, Real.cos_sub]
  simp_rw [this]
  rw [integral_add (hc.const_mul _) (hs.const_mul _), integral_const_mul, integral_const_mul]
  ring

lemma integral_fej_shift (ρ : Measure ℝ) [IsFiniteMeasure ρ] (a t : ℝ) (ha : 0 < a) :
    ∫ x, fej a (t - x) ∂ρ = (1 / π) * ∫ θ in Set.Ioc 0 a,
      (1 - θ / a) * (Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun ρ (-θ)).re := by
  simp_rw [fej, intervalIntegral.integral_of_le ha.le]
  rw [integral_const_mul]
  congr 1
  have hcont : Continuous (Function.uncurry fun (x θ : ℝ) => (1 - θ / a) * Real.cos (θ * (t - x))) := by
    simp only [Function.uncurry_def]; fun_prop
  have hint : Integrable (Function.uncurry fun (x θ : ℝ) => (1 - θ / a) * Real.cos (θ * (t - x)))
      (ρ.prod (volume.restrict (Set.Ioc 0 a))) := by
    refine Integrable.mono' (integrable_const (1:ℝ)) hcont.aestronglyMeasurable ?_
    have e : ρ.prod (volume.restrict (Set.Ioc (0:ℝ) a))
        = (ρ.prod volume).restrict (Set.univ ×ˢ Set.Ioc (0:ℝ) a) := by
      rw [← Measure.prod_restrict, Measure.restrict_univ]
    have : ∀ᵐ p ∂(ρ.prod (volume.restrict (Set.Ioc (0:ℝ) a))), p.2 ∈ Set.Ioc 0 a := by
      rw [e]
      filter_upwards [ae_restrict_mem (MeasurableSet.univ.prod measurableSet_Ioc)] with p hp
      exact hp.2
    filter_upwards [this] with p hp
    simp only [Function.uncurry_def, Real.norm_eq_abs]
    have h1 : 0 ≤ 1 - p.2 / a := by rw [sub_nonneg, div_le_one ha]; exact hp.2
    have h2 : 1 - p.2 / a ≤ 1 := by
      have : 0 ≤ p.2 / a := div_nonneg hp.1.le ha.le
      linarith
    rw [abs_mul, abs_of_nonneg h1]
    calc (1 - p.2 / a) * |Real.cos (p.2 * (t - p.1))| ≤ 1 * 1 :=
          mul_le_mul h2 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := by ring
  rw [integral_integral_swap hint]
  refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  rw [integral_const_mul, integral_cos_shift]

end GoldieRenewal.Implicit.KRT

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit

/-- `a(θ) = ∫ (1 - cos θx) dη`. -/
noncomputable def aF (η : Measure ℝ) (θ : ℝ) : ℝ := ∫ x, (1 - Real.cos (θ * x)) ∂η

/-- `b(θ) = ∫ sin θx dη`. -/
noncomputable def bF (η : Measure ℝ) (θ : ℝ) : ℝ := ∫ x, Real.sin (θ * x) ∂η

/-- `Re (1 - s ψ(θ))⁻¹`, written with `a` and `b`. -/
noncomputable def realKer (η : Measure ℝ) (s θ : ℝ) : ℝ :=
  (1 - s + s * aF η θ) / ((1 - s + s * aF η θ) ^ 2 + (s * bF η θ) ^ 2)

/-- `A_s(t) = Σ sⁿ ∫ F_a(t - x) dη^{*n}`. -/
noncomputable def Aser (η : Measure ℝ) (a s t : ℝ) : ℝ :=
  ∑' n : ℕ, s ^ n * ∫ x, fej a (t - x) ∂(convPow η n)

lemma charFun_neg_re_eq (η : Measure ℝ) [IsProbabilityMeasure η] (θ : ℝ) :
    (charFun η (-θ)).re = 1 - aF η θ := by
  rw [charFun_neg_re, aF, integral_sub (integrable_const _)
    (integrable_bdd_cont η _ (by fun_prop) 1 (fun x => Real.abs_cos_le_one _))]
  simp

lemma measurable_charFun_neg (η : Measure ℝ) [IsProbabilityMeasure η] :
    Measurable (fun θ : ℝ => charFun η (-θ)) :=
  (measurable_charFun (μ := η)).comp measurable_neg

lemma norm_charFun_neg_le (η : Measure ℝ) [IsProbabilityMeasure η] (θ : ℝ) :
    ‖charFun η (-θ)‖ ≤ 1 := norm_charFun_le_one _

lemma T_mem (a θ : ℝ) (ha : 0 < a) (hθ : θ ∈ Set.Ioc 0 a) : 0 ≤ 1 - θ / a ∧ 1 - θ / a ≤ 1 := by
  constructor
  · rw [sub_nonneg, div_le_one ha]; exact hθ.2
  · have : 0 ≤ θ / a := div_nonneg hθ.1.le ha.le
    linarith

lemma Aser_eq (η : Measure ℝ) [IsProbabilityMeasure η] (a s t : ℝ) (ha : 0 < a)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Aser η a s t = (1 / π) * ∫ θ in Set.Ioc 0 a, (1 - θ / a) *
      (Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * (1 - (s : ℂ) * charFun η (-θ))⁻¹).re := by
  set F : ℕ → ℝ → ℝ := fun n θ => (1 / π) * (s ^ n * ((1 - θ / a) *
      (Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun η (-θ) ^ n).re)) with hF
  have hterm : ∀ n : ℕ, s ^ n * ∫ x, fej a (t - x) ∂(convPow η n)
      = ∫ θ in Set.Ioc 0 a, F n θ := by
    intro n
    have := convPow_isProb η n
    rw [integral_fej_shift _ a t ha, ← integral_const_mul, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
    simp only [hF, charFun_convPow η (-θ) n]
    ring
  have hm := measurable_charFun_neg η
  have hFm : ∀ n, Measurable (F n) := by
    intro n; simp only [hF]; fun_prop
  have hFb : ∀ n, ∀ θ ∈ Set.Ioc (0:ℝ) a, ‖F n θ‖ ≤ (1 / π) * s ^ n := by
    intro n θ hθ
    obtain ⟨h1, h2⟩ := T_mem a θ ha hθ
    simp only [hF, Real.norm_eq_abs, abs_mul, abs_of_nonneg h1, abs_of_nonneg (pow_nonneg hs0 n),
      abs_of_pos (by positivity : (0:ℝ) < 1 / π)]
    have hre : |(Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun η (-θ) ^ n).re| ≤ 1 := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_charFun_neg_le η θ)
    have : (1 - θ / a) * |(Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun η (-θ) ^ n).re|
        ≤ 1 := by nlinarith [abs_nonneg ((Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) *
          charFun η (-θ) ^ n).re)]
    have hpi : (0:ℝ) < 1 / π := by positivity
    have hsn : 0 ≤ s ^ n := pow_nonneg hs0 n
    calc 1 / π * (s ^ n * ((1 - θ / a) *
          |(Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) * charFun η (-θ) ^ n).re|))
        ≤ 1 / π * (s ^ n * 1) := by gcongr
      _ = 1 / π * s ^ n := by ring
  have hFi : ∀ n, Integrable (F n) (volume.restrict (Set.Ioc 0 a)) := by
    intro n
    refine Integrable.mono' (integrable_const ((1 / π) * s ^ n)) (hFm n).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    exact hFb n θ hθ
  have hFs : Summable fun n => ∫ θ in Set.Ioc 0 a, ‖F n θ‖ := by
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun θ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_lt_one hs0 hs1).mul_left ((1 / π) * a))
    calc ∫ θ in Set.Ioc 0 a, ‖F n θ‖ ≤ ∫ θ in Set.Ioc 0 a, (1 / π) * s ^ n := by
          refine setIntegral_mono_on (hFi n).norm (integrable_const _) measurableSet_Ioc ?_
          exact fun θ hθ => hFb n θ hθ
      _ = (1 / π) * a * s ^ n := by
          rw [setIntegral_const]; simp [ha.le]; ring
  rw [Aser, tsum_congr hterm, integral_tsum_of_summable_integral_norm hFi hFs,
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
  have hnorm : ‖(s : ℂ) * charFun η (-θ)‖ < 1 := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
    calc s * ‖charFun η (-θ)‖ ≤ s * 1 := by gcongr; exact norm_charFun_neg_le η θ
      _ < 1 := by linarith
  set e := Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I)
  have hs := ((hasSum_geometric_of_norm_lt_one hnorm).mul_left e)
  have hre := (Complex.hasSum_re hs).mul_left ((1 / π) * (1 - θ / a))
  rw [← mul_assoc, ← hre.tsum_eq]
  refine tsum_congr (fun n => ?_)
  simp only [hF]
  have : e * ((s : ℂ) * charFun η (-θ)) ^ n = ((s ^ n : ℝ) : ℂ) * (e * charFun η (-θ) ^ n) := by
    push_cast; ring
  rw [this, Complex.re_ofReal_mul]
  ring

lemma Aser_add_neg (η : Measure ℝ) [IsProbabilityMeasure η] (a s t : ℝ) (ha : 0 < a)
    (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Aser η a s t + Aser η a s (-t)
      = (2 / π) * ∫ θ in Set.Ioc 0 a, (1 - θ / a) * Real.cos (θ * t) * realKer η s θ := by
  have hm := measurable_charFun_neg η
  have hw : ∀ θ, ‖(1 - (s : ℂ) * charFun η (-θ))⁻¹‖ ≤ (1 - s)⁻¹ := by
    intro θ
    rw [norm_inv]
    apply inv_anti₀ (by linarith)
    have h1 : ‖(s : ℂ) * charFun η (-θ)‖ ≤ s := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0]
      calc s * ‖charFun η (-θ)‖ ≤ s * 1 := by gcongr; exact norm_charFun_neg_le η θ
        _ = s := by ring
    have := norm_sub_norm_le (1 : ℂ) ((s : ℂ) * charFun η (-θ))
    rw [norm_one] at this
    linarith
  have hint : ∀ u : ℝ, Integrable (fun θ => (1 - θ / a) *
      (Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I) * (1 - (s : ℂ) * charFun η (-θ))⁻¹).re)
      (volume.restrict (Set.Ioc 0 a)) := by
    intro u
    refine Integrable.mono' (integrable_const ((1 - s)⁻¹)) (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    obtain ⟨h1, h2⟩ := T_mem a θ ha hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1]
    have hre : |(Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I) *
        (1 - (s : ℂ) * charFun η (-θ))⁻¹).re| ≤ (1 - s)⁻¹ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
      exact hw θ
    calc (1 - θ / a) * |(Complex.exp (((θ * u : ℝ) : ℂ) * Complex.I) *
        (1 - (s : ℂ) * charFun η (-θ))⁻¹).re| ≤ 1 * (1 - s)⁻¹ :=
          mul_le_mul h2 hre (abs_nonneg _) zero_le_one
      _ = (1 - s)⁻¹ := one_mul _
  rw [Aser_eq η a s t ha hs0 hs1, Aser_eq η a s (-t) ha hs0 hs1, ← mul_add,
    ← integral_add (hint t) (hint (-t))]
  have key : ∀ θ ∈ Set.Ioc (0:ℝ) a,
      (1 - θ / a) * (Complex.exp (((θ * t : ℝ) : ℂ) * Complex.I) *
        (1 - (s : ℂ) * charFun η (-θ))⁻¹).re +
      (1 - θ / a) * (Complex.exp (((θ * -t : ℝ) : ℂ) * Complex.I) *
        (1 - (s : ℂ) * charFun η (-θ))⁻¹).re
      = 2 * ((1 - θ / a) * Real.cos (θ * t) * realKer η s θ) := by
    intro θ _
    set w := (1 - (s : ℂ) * charFun η (-θ))⁻¹ with hwdef
    have hwre : w.re = realKer η s θ := by
      rw [hwdef, Complex.inv_re, Complex.normSq_apply]
      have hre : (1 - (s : ℂ) * charFun η (-θ)).re = 1 - s + s * aF η θ := by
        rw [Complex.sub_re, Complex.one_re, Complex.re_ofReal_mul, charFun_neg_re_eq]; ring
      have him : (1 - (s : ℂ) * charFun η (-θ)).im = s * bF η θ := by
        rw [Complex.sub_im, Complex.one_im, Complex.im_ofReal_mul, charFun_neg_im, bF]; ring
      rw [hre, him, realKer]
      congr 1; ring
    rw [Complex.mul_re, Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, hwre]
    rw [show θ * -t = -(θ * t) by ring, Real.cos_neg, Real.sin_neg]
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc key, integral_const_mul]
  ring

end GoldieRenewal.Implicit.KRT

/-! ## C4 prep: properties of `a(θ)` and `b(θ)` -/

namespace GoldieRenewal.Implicit.KRT

lemma one_sub_cos_le_abs (u : ℝ) : 1 - Real.cos u ≤ |u| := by
  have h1 : 1 - u ^ 2 / 2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  have h2 := Real.neg_one_le_cos u
  have hu : u ^ 2 = |u| ^ 2 := (sq_abs u).symm
  rcases le_total |u| 2 with h | h
  · nlinarith [abs_nonneg u]
  · linarith

lemma one_sub_cos_le_sq (u : ℝ) : 1 - Real.cos u ≤ u ^ 2 / 2 := by
  have h1 : 1 - u ^ 2 / 2 ≤ Real.cos u := Real.one_sub_sq_div_two_le_cos
  linarith

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma aF_nonneg (θ : ℝ) : 0 ≤ aF η θ :=
  integral_nonneg fun x => by have := Real.cos_le_one (θ * x); simp only [Pi.zero_apply]; linarith

lemma continuous_aF : Continuous (aF η) := by
  show Continuous (fun θ => ∫ x, (1 - Real.cos (θ * x)) ∂η)
  refine continuous_of_dominated (bound := fun _ => (2:ℝ)) (fun θ => ?_) (fun θ => ?_)
    (integrable_const _) (Eventually.of_forall fun x => by fun_prop)
  · exact (by fun_prop : Continuous fun x : ℝ => 1 - Real.cos (θ * x)).aestronglyMeasurable
  · refine Eventually.of_forall fun x => ?_
    rw [Real.norm_eq_abs, abs_le]
    have := Real.cos_le_one (θ * x); have := Real.neg_one_le_cos (θ * x)
    constructor <;> linarith

lemma continuous_bF : Continuous (bF η) := by
  show Continuous (fun θ => ∫ x, Real.sin (θ * x) ∂η)
  refine continuous_of_dominated (bound := fun _ => (1:ℝ)) (fun θ => ?_) (fun θ => ?_)
    (integrable_const _) (Eventually.of_forall fun x => by fun_prop)
  · exact (by fun_prop : Continuous fun x : ℝ => Real.sin (θ * x)).aestronglyMeasurable
  · exact Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact Real.abs_sin_le_one _

lemma tendsto_aF_div (h1 : Integrable (fun x => x) η) :
    Tendsto (fun θ => aF η θ / θ) (𝓝[>] 0) (𝓝 0) := by
  have e : (fun θ => aF η θ / θ) = fun θ => ∫ x, (1 - Real.cos (θ * x)) / θ ∂η := by
    ext θ; rw [aF, integral_div]
  rw [e]
  rw [show (𝓝 (0:ℝ)) = 𝓝 (∫ x, (0:ℝ) ∂η) by simp]
  refine tendsto_integral_filter_of_dominated_convergence (fun x => |x|)
    (Eventually.of_forall fun θ => (by fun_prop : Continuous fun x : ℝ =>
      (1 - Real.cos (θ * x)) / θ).aestronglyMeasurable) ?_ h1.abs ?_
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    refine Eventually.of_forall fun x => ?_
    have hθ' : (0:ℝ) < θ := hθ
    have hc := Real.cos_le_one (θ * x)
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by linarith) hθ'.le), div_le_iff₀ hθ']
    calc 1 - Real.cos (θ * x) ≤ |θ * x| := one_sub_cos_le_abs _
      _ = |x| * θ := by rw [abs_mul, abs_of_pos hθ']; ring
  · refine Eventually.of_forall fun x => ?_
    have hup : Tendsto (fun θ : ℝ => θ * x ^ 2 / 2) (𝓝[>] 0) (𝓝 0) := by
      have : Tendsto (fun θ : ℝ => θ * x ^ 2 / 2) (𝓝 0) (𝓝 (0 * x ^ 2 / 2)) :=
        ((continuous_id.mul continuous_const).div_const 2).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : (0:ℝ) < θ := hθ
      have hc := Real.cos_le_one (θ * x)
      exact div_nonneg (by linarith) hθ'.le
    · filter_upwards [self_mem_nhdsWithin] with θ hθ
      have hθ' : (0:ℝ) < θ := hθ
      rw [div_le_iff₀ hθ']
      have := one_sub_cos_le_sq (θ * x)
      nlinarith

lemma tendsto_bF_div (h1 : Integrable (fun x => x) η) :
    Tendsto (fun θ => bF η θ / θ) (𝓝[>] 0) (𝓝 (∫ x, x ∂η)) := by
  have hcont : Continuous (fun θ => ∫ x, x * Real.sinc (θ * x) ∂η) := by
    refine continuous_of_dominated (bound := fun x => |x|) (fun θ => ?_) (fun θ => ?_)
      h1.abs (Eventually.of_forall fun x => by fun_prop)
    · exact (by fun_prop : Continuous fun x : ℝ => x * Real.sinc (θ * x)).aestronglyMeasurable
    · refine Eventually.of_forall fun x => ?_
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sinc_le_one _)
  have hlim := (hcont.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0:ℝ)))
  simp only [zero_mul, Real.sinc_zero, mul_one] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with θ hθ
  have hθ' : (0:ℝ) < θ := hθ
  rw [bF, ← integral_div]
  congr 1; ext x
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · rw [Real.sinc_of_ne_zero (mul_ne_zero hθ'.ne' hx)]
    field_simp

/-- A `δ ∈ (0, a]` below which `b(θ) ≥ μ θ / 2`. -/
lemma exists_delta (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η) (a : ℝ) (ha : 0 < a) :
    ∃ δ, 0 < δ ∧ δ ≤ a ∧ ∀ θ ∈ Set.Ioc 0 δ, (∫ x, x ∂η) * θ / 2 ≤ bF η θ := by
  have hev : ∀ᶠ θ in 𝓝[>] (0:ℝ), (∫ x, x ∂η) / 2 < bF η θ / θ :=
    (tendsto_bF_div η h1).eventually (lt_mem_nhds (half_lt_self hμ))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu' : (0:ℝ) < u := hu
  refine ⟨min (u / 2) a, lt_min (by linarith) ha, min_le_right _ _, fun θ hθ => ?_⟩
  have hθu : θ ∈ Set.Ioo 0 u := ⟨hθ.1, lt_of_le_of_lt (hθ.2.trans (min_le_left _ _)) (by linarith)⟩
  have := hsub hθu
  simp only [Set.mem_ofPred_eq] at this
  rw [lt_div_iff₀ hθ.1] at this
  linarith

/-- On `[δ, a]`, `a(θ)` is bounded below by a positive constant. -/
lemma exists_aF_min (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (δ a : ℝ) (hδ : 0 < δ) (hδa : δ ≤ a) :
    ∃ m, 0 < m ∧ ∀ θ ∈ Set.Icc δ a, m ≤ aF η θ := by
  obtain ⟨θ0, hθ0, hmin⟩ := isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 hδa)
    (continuous_aF η).continuousOn
  exact ⟨aF η θ0, hpos θ0 (lt_of_lt_of_le hδ hθ0.1), fun θ hθ => hmin hθ⟩

end GoldieRenewal.Implicit.KRT

/-! ## C4a: the approximate-identity part `T1` -/

namespace GoldieRenewal.Implicit.KRT

lemma integral_Ioi_inv_one_add_mul_sq (μ : ℝ) (hμ : 0 < μ) :
    ∫ u in Set.Ioi (0:ℝ), (1 + (μ * u) ^ 2)⁻¹ = π / (2 * μ) := by
  have := integral_comp_mul_left_Ioi (fun v : ℝ => (1 + v ^ 2)⁻¹) 0 hμ
  simp only [mul_zero] at this
  rw [this, integral_Ioi_inv_one_add_sq, Real.arctan_zero, sub_zero, smul_eq_mul]
  field_simp

lemma T1_limit (A B g : ℝ → ℝ) (μ δ : ℝ) (hμ : 0 < μ) (hδ : 0 < δ)
    (hA : Continuous A) (hB : Continuous B) (hg : Continuous g)
    (hA0 : ∀ θ, 0 ≤ A θ) (hAl : Tendsto (fun θ => A θ / θ) (𝓝[>] 0) (𝓝 0))
    (hBl : Tendsto (fun θ => B θ / θ) (𝓝[>] 0) (𝓝 μ))
    (hBδ : ∀ θ ∈ Set.Ioc 0 δ, μ * θ / 2 ≤ B θ) (hg1 : ∀ θ ∈ Set.Ioc 0 δ, |g θ| ≤ 1) :
    Tendsto (fun ε => ∫ θ in Set.Ioc 0 δ,
        g θ * (ε / ((ε + (1 - ε) * A θ) ^ 2 + ((1 - ε) * B θ) ^ 2)))
      (𝓝[>] 0) (𝓝 (π / (2 * μ) * g 0)) := by
  -- the rescaled integrand
  set G : ℝ → ℝ → ℝ := fun ε u => Set.indicator (Set.Ioc 0 (δ / ε)) (fun u =>
      g (ε * u) / ((1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 + ((1 - ε) * (B (ε * u) / ε)) ^ 2)) u
    with hG
  have hden : ∀ ε θ, 0 < ε → ε < 1 → 0 < (ε + (1 - ε) * A θ) ^ 2 + ((1 - ε) * B θ) ^ 2 := by
    intro ε θ h0 h1
    have : 0 < ε + (1 - ε) * A θ := by nlinarith [hA0 θ]
    positivity
  -- step 1: change of variables
  have hsub : ∀ ε, 0 < ε → ε < 1 → ∫ θ in Set.Ioc 0 δ,
      g θ * (ε / ((ε + (1 - ε) * A θ) ^ 2 + ((1 - ε) * B θ) ^ 2)) = ∫ u, G ε u := by
    intro ε h0 h1
    set φ : ℝ → ℝ := fun θ => g θ * (ε / ((ε + (1 - ε) * A θ) ^ 2 + ((1 - ε) * B θ) ^ 2))
      with hφ
    have hεδ : ε * (δ / ε) = δ := by field_simp
    have hcv := intervalIntegral.integral_comp_mul_left φ (c := ε) (a := 0) (b := δ / ε) h0.ne'
    rw [mul_zero, hεδ, smul_eq_mul] at hcv
    have h2 : ∫ θ in (0:ℝ)..δ, φ θ = ε * ∫ u in (0:ℝ)..δ / ε, φ (ε * u) := by
      rw [hcv, ← mul_assoc, mul_inv_cancel₀ h0.ne', one_mul]
    show ∫ θ in Set.Ioc 0 δ, φ θ = _
    rw [← intervalIntegral.integral_of_le hδ.le, h2,
      intervalIntegral.integral_of_le (div_pos hδ h0).le, ← integral_const_mul, hG]
    rw [integral_indicator measurableSet_Ioc]
    refine setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    simp only [hφ]
    have hd := hden ε (ε * u) h0 h1
    have he : ε ≠ 0 := h0.ne'
    have heq : (1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 + ((1 - ε) * (B (ε * u) / ε)) ^ 2
        = ((ε + (1 - ε) * A (ε * u)) ^ 2 + ((1 - ε) * B (ε * u)) ^ 2) / ε ^ 2 := by
      field_simp
    rw [heq]
    field_simp
  -- step 2: dominated convergence for `G`
  have hAm := hA.measurable
  have hBm := hB.measurable
  have hgm := hg.measurable
  set f : ℝ → ℝ := fun u => Set.indicator (Set.Ioi 0) (fun u => g 0 * (1 + (μ * u) ^ 2)⁻¹) u
    with hf
  have hlimG : Tendsto (fun ε => ∫ u, G ε u) (𝓝[>] 0) (𝓝 (∫ u, f u)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun u => Set.indicator (Set.Ioi 0) (fun u => (1 + (μ / 4 * u) ^ 2)⁻¹) u) ?_ ?_ ?_ ?_
    · refine Eventually.of_forall fun ε => ?_
      simp only [hG]
      exact (Measurable.indicator (by fun_prop) measurableSet_Ioc).aestronglyMeasurable
    · have hev1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 / 2 :=
        mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num))
      filter_upwards [hev1, self_mem_nhdsWithin] with ε hε1 hε0
      have hε0' : (0:ℝ) < ε := hε0
      refine Eventually.of_forall fun u => ?_
      simp only [hG]
      by_cases hu : u ∈ Set.Ioc 0 (δ / ε)
      · have hu0 : 0 < u := hu.1
        rw [Set.indicator_of_mem hu, Set.indicator_of_mem (show u ∈ Set.Ioi (0:ℝ) from hu0)]
        have hεu : ε * u ∈ Set.Ioc 0 δ := ⟨mul_pos hε0' hu0, by
          have := mul_le_mul_of_nonneg_left hu.2 hε0'.le
          rwa [show ε * (δ / ε) = δ by field_simp] at this⟩
        have hgb := hg1 _ hεu
        have hBb := hBδ _ hεu
        have hA1 : 0 ≤ (1 - ε) * (A (ε * u) / ε) :=
          mul_nonneg (by linarith) (div_nonneg (hA0 _) hε0'.le)
        have h4 : 0 ≤ μ * u / 2 := by positivity
        have h3 : μ * u / 2 ≤ B (ε * u) / ε := by
          rw [le_div_iff₀ hε0']; linarith
        have hB1 : μ / 4 * u ≤ (1 - ε) * (B (ε * u) / ε) := by
          calc μ / 4 * u = (1 / 2) * (μ * u / 2) := by ring
            _ ≤ (1 - ε) * (B (ε * u) / ε) := mul_le_mul (by linarith) h3 h4 (by linarith)
        have h4' : 0 ≤ μ / 4 * u := by positivity
        have hden1 : 1 + (μ / 4 * u) ^ 2 ≤
            (1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 + ((1 - ε) * (B (ε * u) / ε)) ^ 2 := by
          have hY := pow_le_pow_left₀ h4' hB1 2
          have hX : 1 ≤ (1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 := by nlinarith
          linarith
        rw [Real.norm_eq_abs, abs_div, abs_of_pos (by positivity : (0:ℝ) <
          (1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 + ((1 - ε) * (B (ε * u) / ε)) ^ 2)]
        calc |g (ε * u)| / ((1 + (1 - ε) * (A (ε * u) / ε)) ^ 2 + ((1 - ε) * (B (ε * u) / ε)) ^ 2)
            ≤ 1 / (1 + (μ / 4 * u) ^ 2) := by
              apply div_le_div₀ zero_le_one hgb (by positivity) hden1
          _ = (1 + (μ / 4 * u) ^ 2)⁻¹ := one_div _
      · rw [Set.indicator_of_notMem hu, norm_zero]
        apply Set.indicator_nonneg
        intro u _; positivity
    · exact ((integrable_inv_one_add_sq.comp_mul_left' (by positivity : μ / 4 ≠ 0)).indicator
        measurableSet_Ioi)
    · refine Eventually.of_forall fun u => ?_
      rcases le_or_gt u 0 with hu | hu
      · have h1 : ∀ ε, G ε u = 0 := fun ε => by
          simp only [hG]; exact Set.indicator_of_notMem (fun h => absurd h.1 (not_lt.2 hu)) _
        have h2 : f u = 0 := by
          simp only [hf]; exact Set.indicator_of_notMem (fun h => absurd h (not_lt.2 hu)) _
        simp only [h1, h2]; exact tendsto_const_nhds
      · have hεu : Tendsto (fun ε : ℝ => ε * u) (𝓝[>] 0) (𝓝[>] 0) := by
          refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
          · have : Tendsto (fun ε : ℝ => ε * u) (𝓝 0) (𝓝 (0 * u)) :=
              (continuous_id.mul continuous_const).tendsto 0
            rw [zero_mul] at this
            exact this.mono_left nhdsWithin_le_nhds
          · filter_upwards [self_mem_nhdsWithin] with ε hε
            exact mul_pos hε hu
        have hεu' : Tendsto (fun ε : ℝ => ε * u) (𝓝[>] 0) (𝓝 0) :=
          hεu.mono_right nhdsWithin_le_nhds
        have hev : ∀ᶠ ε in 𝓝[>] (0:ℝ), G ε u = g (ε * u) /
            ((1 + (1 - ε) * (u * (A (ε * u) / (ε * u)))) ^ 2 +
              ((1 - ε) * (u * (B (ε * u) / (ε * u)))) ^ 2) := by
          have hsmall : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < δ / u :=
            mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (div_pos hδ hu))
          filter_upwards [hsmall, self_mem_nhdsWithin] with ε hε1 hε0
          have hε0' : (0:ℝ) < ε := hε0
          have hmem : u ∈ Set.Ioc 0 (δ / ε) := ⟨hu, by
            rw [le_div_iff₀ hε0']; rw [lt_div_iff₀ hu] at hε1; linarith⟩
          simp only [hG]
          rw [Set.indicator_of_mem hmem]
          have h1 : A (ε * u) / ε = u * (A (ε * u) / (ε * u)) := by field_simp
          have h2 : B (ε * u) / ε = u * (B (ε * u) / (ε * u)) := by field_simp
          rw [h1, h2]
        have hfu : f u = g 0 / ((1 + (1 - 0) * (u * 0)) ^ 2 + ((1 - 0) * (u * μ)) ^ 2) := by
          simp only [hf]
          rw [Set.indicator_of_mem (show u ∈ Set.Ioi (0:ℝ) from hu)]
          ring_nf
        rw [hfu]
        refine Tendsto.congr' (EventuallyEq.symm hev) ?_
        have hgl : Tendsto (fun ε => g (ε * u)) (𝓝[>] 0) (𝓝 (g 0)) :=
          (hg.tendsto 0).comp hεu'
        have hAl' : Tendsto (fun ε => A (ε * u) / (ε * u)) (𝓝[>] 0) (𝓝 0) := hAl.comp hεu
        have hBl' : Tendsto (fun ε => B (ε * u) / (ε * u)) (𝓝[>] 0) (𝓝 μ) := hBl.comp hεu
        have hid : Tendsto (fun ε : ℝ => 1 - ε) (𝓝[>] 0) (𝓝 (1 - 0)) :=
          ((continuous_const.sub continuous_id).tendsto 0).mono_left nhdsWithin_le_nhds
        refine hgl.div ?_ (by simp only [sub_zero, mul_zero, add_zero, one_mul, one_pow]; positivity)
        exact ((tendsto_const_nhds.add (hid.mul (tendsto_const_nhds.mul hAl'))).pow 2).add
          ((hid.mul (tendsto_const_nhds.mul hBl')).pow 2)
  have hfint : ∫ u, f u = π / (2 * μ) * g 0 := by
    simp only [hf]
    rw [integral_indicator measurableSet_Ioi, integral_const_mul,
      integral_Ioi_inv_one_add_mul_sq μ hμ]
    ring
  rw [← hfint]
  refine hlimG.congr' ?_
  have hev1 : ∀ᶠ ε in 𝓝[>] (0:ℝ), ε < 1 := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds one_pos)
  filter_upwards [hev1, self_mem_nhdsWithin] with ε h1 h0
  exact (hsub ε h0 h1).symm

end GoldieRenewal.Implicit.KRT

/-! ## C4b: `a(θ)/θ²` is integrable near `0`; the `T2` and tail limits; assembly -/

namespace GoldieRenewal.Implicit.KRT

lemma one_sub_cos_mul_div_sq (x : ℝ) :
    IntegrableOn (fun θ : ℝ => (1 - Real.cos (θ * x)) / θ ^ 2) (Set.Ioi 0) ∧
    ∫ θ in Set.Ioi (0:ℝ), (1 - Real.cos (θ * x)) / θ ^ 2 = |x| * (π / 2) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hc : 0 < |x| := abs_pos.2 hx
    have hpt : ∀ θ ∈ Set.Ioi (0:ℝ), (1 - Real.cos (θ * x)) / θ ^ 2
        = |x| ^ 2 * ((1 - Real.cos (|x| * θ)) / (|x| * θ) ^ 2) := by
      intro θ hθ
      have hθ' : (0:ℝ) < θ := hθ
      have : Real.cos (θ * x) = Real.cos (|x| * θ) := by
        rw [← Real.cos_abs (θ * x), abs_mul, abs_of_pos hθ', mul_comm]
      rw [this]
      field_simp
    have hint : IntegrableOn (fun θ : ℝ => |x| ^ 2 * ((1 - Real.cos (|x| * θ)) / (|x| * θ) ^ 2))
        (Set.Ioi 0) :=
      ((integrable_one_sub_cos_div_sq.comp_mul_left' hc.ne').const_mul _).integrableOn
    refine ⟨hint.congr_fun (fun θ hθ => (hpt θ hθ).symm) measurableSet_Ioi, ?_⟩
    rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul]
    have := integral_comp_mul_left_Ioi (fun v : ℝ => (1 - Real.cos v) / v ^ 2) 0 hc
    simp only [mul_zero] at this
    rw [this, integral_Ioi_one_sub_cos_div_sq, smul_eq_mul]
    field_simp

lemma one_sub_cos_div_sq_nonneg' (θ x : ℝ) : 0 ≤ (1 - Real.cos (θ * x)) / θ ^ 2 := by
  have := Real.cos_le_one (θ * x)
  apply div_nonneg (by linarith); positivity

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma integrableOn_aF_div_sq (h1 : Integrable (fun x => x) η) :
    IntegrableOn (fun θ => aF η θ / θ ^ 2) (Set.Ioi 0) := by
  have hmeas : AEStronglyMeasurable (fun p : ℝ × ℝ => (1 - Real.cos (p.1 * p.2)) / p.1 ^ 2)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod η) :=
    (by fun_prop : Measurable fun p : ℝ × ℝ => (1 - Real.cos (p.1 * p.2)) / p.1 ^ 2).aestronglyMeasurable
  have hF : Integrable (fun p : ℝ × ℝ => (1 - Real.cos (p.1 * p.2)) / p.1 ^ 2)
      ((volume.restrict (Set.Ioi (0:ℝ))).prod η) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun x => (one_sub_cos_mul_div_sq x).1, ?_⟩
    have : (fun x => ∫ θ in Set.Ioi (0:ℝ), ‖(1 - Real.cos (θ * x)) / θ ^ 2‖)
        = fun x => |x| * (π / 2) := by
      ext x
      rw [← (one_sub_cos_mul_div_sq x).2]
      refine setIntegral_congr_fun measurableSet_Ioi (fun θ _ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (one_sub_cos_div_sq_nonneg' θ x)]
    rw [this]
    exact h1.abs.mul_const _
  have := hF.integral_prod_left
  refine this.congr (Eventually.of_forall fun θ => ?_)
  simp only
  rw [aF, integral_div]

end GoldieRenewal.Implicit.KRT

/-! ## C4c: the `s → 1⁻` limit of the real-part integral -/

namespace GoldieRenewal.Implicit.KRT

/-- `|1 - s ψ(θ)|²`. -/
noncomputable def Dk (η : Measure ℝ) (s θ : ℝ) : ℝ :=
  (1 - s + s * aF η θ) ^ 2 + (s * bF η θ) ^ 2

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma realKer_eq (s θ : ℝ) :
    realKer η s θ = (1 - s) / Dk η s θ + s * aF η θ / Dk η s θ := by
  rw [realKer, Dk, ← add_div]

lemma Dk_ge_aF (s θ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (s * aF η θ) ^ 2 ≤ Dk η s θ := by
  have hA := aF_nonneg η θ
  have h : s * aF η θ ≤ 1 - s + s * aF η θ := by linarith
  have h0 : 0 ≤ s * aF η θ := mul_nonneg hs0 hA
  unfold Dk
  nlinarith [sq_nonneg (s * bF η θ)]

lemma Dk_ge_bF (s θ : ℝ) : (s * bF η θ) ^ 2 ≤ Dk η s θ := by
  unfold Dk; nlinarith [sq_nonneg (1 - s + s * aF η θ)]

lemma Dk_ge_one_sub (s θ : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : (1 - s) ^ 2 ≤ Dk η s θ := by
  have hA := aF_nonneg η θ
  have h : 1 - s ≤ 1 - s + s * aF η θ := by nlinarith
  have h0 : 0 ≤ 1 - s := by linarith
  unfold Dk
  nlinarith [sq_nonneg (s * bF η θ)]

lemma Dk_pos (s θ : ℝ) (hs0 : 0 ≤ s) (hs1 : s < 1) : 0 < Dk η s θ :=
  lt_of_lt_of_le (by have : 0 < 1 - s := by linarith
                     positivity) (Dk_ge_one_sub η s θ hs0 hs1.le)

lemma measurable_Dk (s : ℝ) : Measurable (Dk η s) := by
  have hAm := (continuous_aF η).measurable
  have hBm := (continuous_bF η).measurable
  unfold Dk; fun_prop

lemma aF_le_two (θ : ℝ) : aF η θ ≤ 2 := by
  calc aF η θ ≤ ∫ x, (2:ℝ) ∂η := integral_mono
        (integrable_bdd_cont η _ (by fun_prop) 2 (fun x => by
          rw [abs_le]; constructor <;> linarith [Real.cos_le_one (θ * x), Real.neg_one_le_cos (θ * x)]))
        (integrable_const _) (fun x => by linarith [Real.neg_one_le_cos (θ * x)])
    _ = 2 := by simp

lemma tendsto_Dk_one (θ : ℝ) (hθ : 0 < aF η θ) :
    Tendsto (fun s => Dk η s θ) (𝓝[<] 1) (𝓝 (aF η θ ^ 2 + bF η θ ^ 2)) := by
  have : Continuous (fun s => Dk η s θ) := by unfold Dk; fun_prop
  have h := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
  simpa [Dk] using h

lemma T1_tail (a δ m : ℝ) (hm : 0 < m) (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (hδ : 0 < δ)
    (hma : ∀ θ ∈ Set.Icc δ a, m ≤ aF η θ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ θ ∈ Set.Ioc δ a, |g θ| ≤ 1) :
    Tendsto (fun s => ∫ θ in Set.Ioc δ a, g θ * ((1 - s) / Dk η s θ)) (𝓝[<] 1) (𝓝 0) := by
  have hgm := hg.measurable
  have hD := measurable_Dk η
  have h0 : ∫ θ in Set.Ioc δ a, (0:ℝ) = 0 := by simp
  rw [← h0]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => 4 / m ^ 2) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s => Measurable.aestronglyMeasurable (by fun_prop)
  · have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 1 / 2 < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s < 1 := hs1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hmθ := hma θ ⟨hθ.1.le, hθ.2⟩
    have hDp := Dk_pos η s θ (by linarith) hs1'
    have hDa := Dk_ge_aF η s θ (by linarith) hs1'.le
    have hsm : m / 2 ≤ s * aF η θ := by nlinarith
    have hsq : (m / 2) ^ 2 ≤ (s * aF η θ) ^ 2 := pow_le_pow_left₀ (by positivity) hsm 2
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos hDp, abs_of_pos (by linarith : (0:ℝ) < 1 - s)]
    calc |g θ| * ((1 - s) / Dk η s θ) ≤ 1 * (1 / (m / 2) ^ 2) := by
          apply mul_le_mul (hg1 θ hθ) _ (by positivity) zero_le_one
          apply div_le_div₀ zero_le_one (by linarith) (by positivity) (hsq.trans hDa)
      _ = 4 / m ^ 2 := by field_simp; ring
  · exact integrable_const _
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hA := hpos θ (lt_of_lt_of_le hδ hθ.1.le)
    have hlim := tendsto_Dk_one η θ hA
    have hne : aF η θ ^ 2 + bF η θ ^ 2 ≠ 0 := by positivity
    have h1s : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝 (1 - 1)) :=
      ((continuous_const.sub continuous_id).tendsto 1).mono_left nhdsWithin_le_nhds
    have := (tendsto_const_nhds (x := g θ)).mul (h1s.div hlim hne)
    simpa using this

lemma T2_lim (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ)
    (a δ m : ℝ) (hδ : 0 < δ) (hm : 0 < m)
    (hbδ : ∀ θ ∈ Set.Ioc 0 δ, (∫ x, x ∂η) * θ / 2 ≤ bF η θ) (hma : ∀ θ ∈ Set.Icc δ a, m ≤ aF η θ)
    (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ θ ∈ Set.Ioc 0 a, |g θ| ≤ 1) :
    Tendsto (fun s => ∫ θ in Set.Ioc 0 a, g θ * (s * aF η θ / Dk η s θ)) (𝓝[<] 1)
      (𝓝 (∫ θ in Set.Ioc 0 a, g θ * (aF η θ / (aF η θ ^ 2 + bF η θ ^ 2)))) := by
  set μ := ∫ x, x ∂η with hμdef
  have hgm := hg.measurable
  have hD := measurable_Dk η
  have hAm := (continuous_aF η).measurable
  refine tendsto_integral_filter_of_dominated_convergence
    (fun θ => 16 / μ ^ 2 * (aF η θ / θ ^ 2) + 2 / m) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun s => Measurable.aestronglyMeasurable (by fun_prop)
  · have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 1 / 2 < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
    filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
    have hs1' : s < 1 := hs1
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hA := aF_nonneg η θ
    have hDp := Dk_pos η s θ (by linarith) hs1'
    have hT : 0 ≤ s * aF η θ / Dk η s θ := div_nonneg (by nlinarith) hDp.le
    have hb1 : 0 ≤ 16 / μ ^ 2 * (aF η θ / θ ^ 2) := by positivity
    have hb2 : 0 ≤ 2 / m := by positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hT]
    have hT' : s * aF η θ / Dk η s θ ≤ 16 / μ ^ 2 * (aF η θ / θ ^ 2) + 2 / m := by
      by_cases hθδ : θ ≤ δ
      · have hb := hbδ θ ⟨hθ0, hθδ⟩
        have hbs : μ * θ / 4 ≤ s * bF η θ := by nlinarith [mul_pos hμ hθ0]
        have hsq : (μ * θ / 4) ^ 2 ≤ (s * bF η θ) ^ 2 := pow_le_pow_left₀ (by positivity) hbs 2
        have hDb := (hsq.trans (Dk_ge_bF η s θ))
        have : s * aF η θ / Dk η s θ ≤ aF η θ / (μ * θ / 4) ^ 2 := by
          apply div_le_div₀ hA (by nlinarith) (by positivity) hDb
        have e : aF η θ / (μ * θ / 4) ^ 2 = 16 / μ ^ 2 * (aF η θ / θ ^ 2) := by
          field_simp; ring
        linarith
      · replace hθδ : δ < θ := not_le.1 hθδ
        have hmθ := hma θ ⟨hθδ.le, hθ.2⟩
        have hsm : m / 2 ≤ s * aF η θ := by nlinarith
        have hsa : 0 < s * aF η θ := by linarith [show 0 < m / 2 by positivity]
        have hDa := Dk_ge_aF η s θ (by linarith) hs1'.le
        have : s * aF η θ / Dk η s θ ≤ s * aF η θ / (s * aF η θ) ^ 2 :=
          div_le_div_of_nonneg_left hsa.le (by positivity) hDa
        have e : s * aF η θ / (s * aF η θ) ^ 2 = 1 / (s * aF η θ) := by
          field_simp
        have h3 : 1 / (s * aF η θ) ≤ 2 / m := by
          rw [div_le_div_iff₀ hsa hm]; linarith
        linarith
    calc |g θ| * (s * aF η θ / Dk η s θ) ≤ 1 * (s * aF η θ / Dk η s θ) :=
          mul_le_mul_of_nonneg_right (hg1 θ hθ) hT
      _ ≤ 16 / μ ^ 2 * (aF η θ / θ ^ 2) + 2 / m := by rw [one_mul]; exact hT'
  · exact (((integrableOn_aF_div_sq η h1).mono_set Set.Ioc_subset_Ioi_self).const_mul _).add
      (integrable_const _)
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hA := hpos θ hθ.1
    have hlim := tendsto_Dk_one η θ hA
    have hne : aF η θ ^ 2 + bF η θ ^ 2 ≠ 0 := by positivity
    have hs : Tendsto (fun s : ℝ => s) (𝓝[<] 1) (𝓝 1) := tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    have := (tendsto_const_nhds (x := g θ)).mul
      ((hs.mul (tendsto_const_nhds (x := aF η θ))).div hlim hne)
    simpa using this

end GoldieRenewal.Implicit.KRT

namespace GoldieRenewal.Implicit.KRT

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma s_limit (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a : ℝ) (ha : 0 < a)
    (g : ℝ → ℝ) (hg : Continuous g) (hg1 : ∀ θ ∈ Set.Ioc 0 a, |g θ| ≤ 1) :
    Tendsto (fun s => ∫ θ in Set.Ioc 0 a, g θ * realKer η s θ) (𝓝[<] 1)
      (𝓝 (π / (2 * ∫ x, x ∂η) * g 0 +
        ∫ θ in Set.Ioc 0 a, g θ * (aF η θ / (aF η θ ^ 2 + bF η θ ^ 2)))) := by
  obtain ⟨δ, hδ, hδa, hbδ⟩ := exists_delta η h1 hμ a ha
  obtain ⟨m, hm, hma⟩ := exists_aF_min η hpos δ a hδ hδa
  have hgm := hg.measurable
  have hD := measurable_Dk η
  have hAm := (continuous_aF η).measurable
  have h1s : Tendsto (fun s : ℝ => 1 - s) (𝓝[<] 1) (𝓝[>] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have hc : Continuous (fun s : ℝ => 1 - s) := by fun_prop
      have := (hc.tendsto (1:ℝ)).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
      simpa using this
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact sub_pos.2 (show s < 1 from hs)
  have L1 := (T1_limit (aF η) (bF η) g (∫ x, x ∂η) δ hμ hδ (continuous_aF η) (continuous_bF η) hg
    (aF_nonneg η) (tendsto_aF_div η h1) (tendsto_bF_div η h1) hbδ
    (fun θ hθ => hg1 θ ⟨hθ.1, hθ.2.trans hδa⟩)).comp h1s
  have L1' : Tendsto (fun s => ∫ θ in Set.Ioc 0 δ, g θ * ((1 - s) / Dk η s θ)) (𝓝[<] 1)
      (𝓝 (π / (2 * ∫ x, x ∂η) * g 0)) := by
    refine L1.congr (fun s => ?_)
    simp only [Function.comp_apply, sub_sub_cancel, Dk]
  have L2 := T1_tail η a δ m hm hpos hδ hma g hg (fun θ hθ => hg1 θ ⟨lt_trans hδ hθ.1, hθ.2⟩)
  have L3 := T2_lim η h1 hμ hpos a δ m hδ hm hbδ hma g hg hg1
  have hsum := (L1'.add L2).add L3
  rw [add_zero] at hsum
  refine hsum.congr' ?_
  have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 1 / 2 < s :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num))
  filter_upwards [hev, self_mem_nhdsWithin] with s hs hs1
  have hs1' : s < 1 := hs1
  have h1s0 : 0 < 1 - s := by linarith
  set C : ℝ := 1 / (1 - s) + 2 / (1 - s) ^ 2 with hC
  have hC1 : 0 ≤ 1 / (1 - s) := by positivity
  have hC2 : 0 ≤ 2 / (1 - s) ^ 2 := by positivity
  have hDp : ∀ θ, 0 < Dk η s θ := fun θ => Dk_pos η s θ (by linarith) hs1'
  have hD1 : ∀ θ, (1 - s) ^ 2 ≤ Dk η s θ := fun θ => Dk_ge_one_sub η s θ (by linarith) hs1'.le
  have hI1 : IntegrableOn (fun θ => g θ * ((1 - s) / Dk η s θ)) (Set.Ioc 0 a) := by
    refine Integrable.mono' (integrable_const C) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_pos h1s0, abs_of_pos (hDp θ)]
    have : (1 - s) / Dk η s θ ≤ 1 / (1 - s) := by
      rw [div_le_div_iff₀ (hDp θ) h1s0]; nlinarith [hD1 θ]
    calc |g θ| * ((1 - s) / Dk η s θ) ≤ 1 * (1 / (1 - s)) :=
          mul_le_mul (hg1 θ hθ) this (div_nonneg h1s0.le (hDp θ).le) zero_le_one
      _ ≤ C := by rw [one_mul]; linarith
  have hI2 : IntegrableOn (fun θ => g θ * (s * aF η θ / Dk η s θ)) (Set.Ioc 0 a) := by
    refine Integrable.mono' (integrable_const C) (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    have hA := aF_nonneg η θ
    have hA2 := aF_le_two η θ
    have hsa : 0 ≤ s * aF η θ := by nlinarith
    rw [Real.norm_eq_abs, abs_mul, abs_div, abs_of_nonneg hsa, abs_of_pos (hDp θ)]
    have : s * aF η θ / Dk η s θ ≤ 2 / (1 - s) ^ 2 := by
      apply div_le_div₀ (by norm_num) (by nlinarith) (by positivity) (hD1 θ)
    calc |g θ| * (s * aF η θ / Dk η s θ) ≤ 1 * (2 / (1 - s) ^ 2) :=
          mul_le_mul (hg1 θ hθ) this (div_nonneg hsa (hDp θ).le) zero_le_one
      _ ≤ C := by rw [one_mul]; linarith
  have hdisj : Disjoint (Set.Ioc 0 δ) (Set.Ioc δ a) :=
    Set.disjoint_left.2 fun x hx hx' => by linarith [hx.2, hx'.1]
  have hsplit : ∫ θ in Set.Ioc 0 a, g θ * ((1 - s) / Dk η s θ)
      = (∫ θ in Set.Ioc 0 δ, g θ * ((1 - s) / Dk η s θ))
        + ∫ θ in Set.Ioc δ a, g θ * ((1 - s) / Dk η s θ) := by
    rw [← intervalIntegral.integral_of_le ha.le, ← intervalIntegral.integral_of_le hδ.le,
      ← intervalIntegral.integral_of_le hδa]
    have i1 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδ.le).2
        (hI1.mono_set (Set.Ioc_subset_Ioc_right hδa))
    have i2 := (intervalIntegrable_iff_integrableOn_Ioc_of_le hδa).2
        (hI1.mono_set (Set.Ioc_subset_Ioc_left hδ.le))
    exact (intervalIntegral.integral_add_adjacent_intervals i1 i2).symm
  have hfin : ∫ θ in Set.Ioc 0 a, g θ * realKer η s θ
      = (∫ θ in Set.Ioc 0 a, g θ * ((1 - s) / Dk η s θ))
        + ∫ θ in Set.Ioc 0 a, g θ * (s * aF η θ / Dk η s θ) := by
    rw [← integral_add hI1 hI2]
    refine setIntegral_congr_fun measurableSet_Ioc (fun θ _ => ?_)
    rw [realKer_eq, mul_add]
  rw [hfin, hsplit]

end GoldieRenewal.Implicit.KRT

/-! ## C5a: the renewal integral `A(t) = ∫ F_a(t - x) U(dx)` and `A(t) + A(-t)` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit
open scoped ENNReal

lemma continuous_fej (a : ℝ) : Continuous (fej a) := by
  unfold fej
  refine continuous_const.mul ?_
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun y θ => (1 - θ / a) * Real.cos (θ * y)) (by simp only [Function.uncurry_def]; fun_prop) 0 a

lemma tendsto_tsum_pow_mul (c : ℕ → ℝ≥0∞) :
    Tendsto (fun s : ℝ => ∑' n, ENNReal.ofReal (s ^ n) * c n) (𝓝[<] 1) (𝓝 (∑' n, c n)) := by
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ : ∃ N, b < ∑ n ∈ Finset.range N, c n :=
      ((ENNReal.tendsto_nat_tsum c).eventually (lt_mem_nhds hb)).exists
    have hcont : Tendsto (fun s : ℝ => ∑ n ∈ Finset.range N, ENNReal.ofReal (s ^ n) * c n)
        (𝓝[<] 1) (𝓝 (∑ n ∈ Finset.range N, c n)) := by
      have : ∀ n ∈ Finset.range N, Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ n) * c n) (𝓝[<] 1)
          (𝓝 (c n)) := by
        intro n _
        have h1 : Tendsto (fun s : ℝ => ENNReal.ofReal (s ^ n)) (𝓝[<] 1) (𝓝 1) := by
          have hc : Continuous (fun s : ℝ => ENNReal.ofReal (s ^ n)) :=
            ENNReal.continuous_ofReal.comp (continuous_pow n)
          have := (hc.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Set.Iio (1:ℝ)))
          simpa using this
        have := ENNReal.Tendsto.mul_const h1 (Or.inl one_ne_zero) (b := c n)
        simpa using this
      exact tendsto_finset_sum _ this
    filter_upwards [hcont.eventually (lt_mem_nhds hN)] with s hs
    exact lt_of_lt_of_le hs (ENNReal.sum_le_tsum _)
  · have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 0 < s :=
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
    filter_upwards [hev, self_mem_nhdsWithin] with s hs0 hs1
    have hs1' : s < 1 := hs1
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun n => ?_) hb
    refine mul_le_of_le_one_left zero_le ?_
    rw [ENNReal.ofReal_le_one]
    exact pow_le_one₀ hs0.le hs1'.le

/-- `A(t) = ∫ F_a(t - x) U(dx)` in `[0, ∞]`, `U` the renewal measure. -/
noncomputable def Afull (η : Measure ℝ) (a t : ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (fej a (t - x)) ∂(renewalMeasure η)

lemma Afull_eq (η : Measure ℝ) (a t : ℝ) :
    Afull η a t = ∑' n, ∫⁻ x, ENNReal.ofReal (fej a (t - x)) ∂(convPow η n) := by
  rw [Afull, renewalMeasure, lintegral_sum_measure]

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma integrable_fej_shift (ρ : Measure ℝ) [IsProbabilityMeasure ρ] (a t : ℝ) (ha : 0 < a) :
    Integrable (fun x => fej a (t - x)) ρ :=
  integrable_bdd_cont ρ _ ((continuous_fej a).comp (continuous_const.sub continuous_id)) (a / (2 * π))
    (fun x => by rw [abs_of_nonneg (fej_nonneg a _ ha)]; exact fej_le a _ ha)

lemma Aser_term_nonneg (a s t : ℝ) (ha : 0 < a) (hs0 : 0 ≤ s) (n : ℕ) :
    0 ≤ s ^ n * ∫ x, fej a (t - x) ∂(convPow η n) :=
  mul_nonneg (pow_nonneg hs0 n) (integral_nonneg fun x => fej_nonneg a _ ha)

lemma Aser_summable (a s t : ℝ) (ha : 0 < a) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    Summable (fun n => s ^ n * ∫ x, fej a (t - x) ∂(convPow η n)) := by
  refine Summable.of_nonneg_of_le (Aser_term_nonneg η a s t ha hs0) (fun n => ?_)
    ((summable_geometric_of_lt_one hs0 hs1).mul_right (a / (2 * π)))
  have := convPow_isProb η n
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hs0 n)
  calc ∫ x, fej a (t - x) ∂(convPow η n) ≤ ∫ x, a / (2 * π) ∂(convPow η n) :=
        integral_mono (integrable_fej_shift _ a t ha) (integrable_const _)
          (fun x => fej_le a _ ha)
    _ = a / (2 * π) := by simp

lemma Aser_nonneg (a s t : ℝ) (ha : 0 < a) (hs0 : 0 ≤ s) : 0 ≤ Aser η a s t :=
  tsum_nonneg (Aser_term_nonneg η a s t ha hs0)

lemma ofReal_Aser (a s t : ℝ) (ha : 0 < a) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ENNReal.ofReal (Aser η a s t) = ∑' n, ENNReal.ofReal (s ^ n) *
      ∫⁻ x, ENNReal.ofReal (fej a (t - x)) ∂(convPow η n) := by
  rw [Aser, ENNReal.ofReal_tsum_of_nonneg (Aser_term_nonneg η a s t ha hs0)
    (Aser_summable η a s t ha hs0 hs1)]
  refine tsum_congr (fun n => ?_)
  have := convPow_isProb η n
  rw [ENNReal.ofReal_mul (pow_nonneg hs0 n), ofReal_integral_eq_lintegral_ofReal
    (integrable_fej_shift _ a t ha) (Eventually.of_forall fun x => fej_nonneg a _ ha)]

lemma tendsto_ofReal_Aser (a t : ℝ) (ha : 0 < a) :
    Tendsto (fun s => ENNReal.ofReal (Aser η a s t)) (𝓝[<] 1) (𝓝 (Afull η a t)) := by
  rw [Afull_eq]
  refine (tendsto_tsum_pow_mul _).congr' ?_
  have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 0 < s :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
  filter_upwards [hev, self_mem_nhdsWithin] with s hs0 hs1
  exact (ofReal_Aser η a s t ha hs0.le hs1).symm

/-- The limit function `h(θ) = a(θ)/(a(θ)² + b(θ)²)`. -/
noncomputable def hLim (θ : ℝ) : ℝ := aF η θ / (aF η θ ^ 2 + bF η θ ^ 2)

lemma Afull_add_neg (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a : ℝ) (ha : 0 < a) (t : ℝ) :
    Afull η a t + Afull η a (-t) = ENNReal.ofReal (1 / (∫ x, x ∂η) +
      (2 / π) * ∫ θ in Set.Ioc 0 a, (1 - θ / a) * Real.cos (θ * t) * hLim η θ) := by
  have hg1 : ∀ θ ∈ Set.Ioc 0 a, |(1 - θ / a) * Real.cos (θ * t)| ≤ 1 := by
    intro θ hθ
    obtain ⟨h1, h2⟩ := T_mem a θ ha hθ
    rw [abs_mul, abs_of_nonneg h1]
    calc (1 - θ / a) * |Real.cos (θ * t)| ≤ 1 * 1 :=
          mul_le_mul h2 (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
      _ = 1 := one_mul 1
  have L := s_limit η h1 hμ hpos a ha (fun θ => (1 - θ / a) * Real.cos (θ * t)) (by fun_prop) hg1
  have hA := (tendsto_ofReal_Aser η a t ha).add (tendsto_ofReal_Aser η a (-t) ha)
  refine tendsto_nhds_unique hA ?_
  have hev : ∀ᶠ s in 𝓝[<] (1:ℝ), 0 < s :=
    mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds one_pos)
  have hL : Tendsto (fun s => ENNReal.ofReal ((2 / π) * ∫ θ in Set.Ioc 0 a,
      (1 - θ / a) * Real.cos (θ * t) * realKer η s θ)) (𝓝[<] 1)
      (𝓝 (ENNReal.ofReal (1 / (∫ x, x ∂η) +
        (2 / π) * ∫ θ in Set.Ioc 0 a, (1 - θ / a) * Real.cos (θ * t) * hLim η θ))) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp (L.const_mul (2 / π))
    convert this using 2
    · simp only [Function.comp_apply]
    · congr 1
      have hμ' : (∫ x, x ∂η) ≠ 0 := hμ.ne'
      simp only [hLim, zero_div, sub_zero, zero_mul, Real.cos_zero, mul_one]
      rw [mul_add]
      congr 1
      field_simp
  refine hL.congr' ?_
  filter_upwards [hev, self_mem_nhdsWithin] with s hs0 hs1
  have hs1' : s < 1 := hs1
  rw [← Aser_add_neg η a s t ha hs0.le hs1', ENNReal.ofReal_add (Aser_nonneg η a s t ha hs0.le)
    (Aser_nonneg η a s (-t) ha hs0.le)]

end GoldieRenewal.Implicit.KRT

/-! ## C5b: Riemann-Lebesgue, integrability of the limit kernel, Chernoff bound -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit
open scoped ENNReal

lemma tendsto_integral_mul_cos (h : ℝ → ℝ) (hh : Integrable h) :
    Tendsto (fun t => ∫ θ, h θ * Real.cos (θ * t)) atTop (𝓝 0) := by
  have RL := Real.tendsto_integral_exp_smul_cocompact (fun θ => (h θ : ℂ))
  have hmap : Tendsto (fun t : ℝ => t / (2 * π)) atTop (cocompact ℝ) :=
    (tendsto_id.atTop_div_const (by positivity)).mono_right atTop_le_cocompact
  have h2 := (Complex.continuous_re.tendsto 0).comp (RL.comp hmap)
  rw [Complex.zero_re] at h2
  refine h2.congr (fun t => ?_)
  simp only [Function.comp_apply]
  have hcont : Continuous (fun v : ℝ => Real.fourierChar (-(v * (t / (2 * π))))) :=
    Real.continuous_fourierChar.comp (by fun_prop)
  have hint : Integrable (fun v : ℝ => Real.fourierChar (-(v * (t / (2 * π)))) • (h v : ℂ)) := by
    refine Integrable.mono' hh.norm ?_ (Eventually.of_forall fun v => ?_)
    · exact hcont.aestronglyMeasurable.smul hh.ofReal.aestronglyMeasurable
    · rw [Circle.norm_smul, Complex.norm_real]
  have := integral_re hint
  simp only [RCLike.re_to_complex] at this
  rw [← this]
  congr 1; ext v
  rw [Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, Complex.re_mul_ofReal,
    Complex.exp_ofReal_mul_I_re]
  rw [show 2 * π * -(v * (t / (2 * π))) = -(v * t) by field_simp, Real.cos_neg]
  ring

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma hLim_nonneg (θ : ℝ) : 0 ≤ hLim η θ :=
  div_nonneg (aF_nonneg η θ) (by positivity)

lemma measurable_hLim : Measurable (hLim η) := by
  have hAm := (continuous_aF η).measurable
  have hBm := (continuous_bF η).measurable
  unfold hLim; fun_prop

lemma integrableOn_hLim (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a : ℝ) (ha : 0 < a) :
    IntegrableOn (hLim η) (Set.Ioc 0 a) := by
  obtain ⟨δ, hδ, hδa, hbδ⟩ := exists_delta η h1 hμ a ha
  obtain ⟨m, hm, hma⟩ := exists_aF_min η hpos δ a hδ hδa
  set μ := ∫ x, x ∂η with hμdef
  refine Integrable.mono' ((((integrableOn_aF_div_sq η h1).mono_set
    Set.Ioc_subset_Ioi_self).const_mul (4 / μ ^ 2)).add (integrable_const (1 / m)))
    (measurable_hLim η).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
  rw [Real.norm_eq_abs, abs_of_nonneg (hLim_nonneg η θ)]
  have hA := hpos θ hθ.1
  have hA0 := aF_nonneg η θ
  have hθ0 : 0 < θ := hθ.1
  have hb1 : 0 ≤ 4 / μ ^ 2 * (aF η θ / θ ^ 2) := by positivity
  have hb2 : 0 ≤ 1 / m := by positivity
  by_cases hθδ : θ ≤ δ
  · have hb := hbδ θ ⟨hθ0, hθδ⟩
    have hbpos : 0 < μ * θ / 2 := by positivity
    have hsq : (μ * θ / 2) ^ 2 ≤ bF η θ ^ 2 := pow_le_pow_left₀ hbpos.le hb 2
    have : hLim η θ ≤ aF η θ / (μ * θ / 2) ^ 2 := by
      unfold hLim
      apply div_le_div_of_nonneg_left hA0 (by positivity) (by nlinarith [sq_nonneg (aF η θ)])
    have e : aF η θ / (μ * θ / 2) ^ 2 = 4 / μ ^ 2 * (aF η θ / θ ^ 2) := by
      field_simp; ring
    calc hLim η θ ≤ aF η θ / (μ * θ / 2) ^ 2 := this
      _ = 4 / μ ^ 2 * (aF η θ / θ ^ 2) := e
      _ ≤ 4 / μ ^ 2 * (aF η θ / θ ^ 2) + 1 / m := le_add_of_nonneg_right hb2
  · replace hθδ : δ < θ := not_le.1 hθδ
    have hmθ := hma θ ⟨hθδ.le, hθ.2⟩
    have : hLim η θ ≤ 1 / aF η θ := by
      unfold hLim
      rw [div_le_div_iff₀ (by positivity) hA]
      nlinarith [sq_nonneg (bF η θ)]
    have h3 : 1 / aF η θ ≤ 1 / m := one_div_le_one_div_of_le hm hmθ
    calc hLim η θ ≤ 1 / aF η θ := this
      _ ≤ 1 / m := h3
      _ ≤ 4 / μ ^ 2 * (aF η θ / θ ^ 2) + 1 / m := le_add_of_nonneg_left hb1

lemma tendsto_cos_hLim (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => ∫ θ in Set.Ioc 0 a, (1 - θ / a) * Real.cos (θ * t) * hLim η θ)
      atTop (𝓝 0) := by
  have hI : Integrable (Set.indicator (Set.Ioc 0 a) (fun θ => (1 - θ / a) * hLim η θ)) := by
    rw [integrable_indicator_iff measurableSet_Ioc]
    have hm := measurable_hLim η
    refine Integrable.mono' (integrableOn_hLim η h1 hμ hpos a ha)
      (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    obtain ⟨h1', h2'⟩ := T_mem a θ ha hθ
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h1', abs_of_nonneg (hLim_nonneg η θ)]
    exact mul_le_of_le_one_left (hLim_nonneg η θ) h2'
  refine (tendsto_integral_mul_cos _ hI).congr (fun t => ?_)
  rw [← integral_indicator measurableSet_Ioc]
  congr 1; ext θ
  simp only [Set.indicator_apply]
  split_ifs <;> ring

/-- `∫ e^{-l x} ρ(dx)` in `[0, ∞]`. -/
noncomputable def expMom (l : ℝ) (ρ : Measure ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (Real.exp (-(l * x))) ∂ρ

lemma measurable_expden (l : ℝ) : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (-(l * x)))) := by
  fun_prop

omit [IsProbabilityMeasure η] in
lemma expMom_conv (l : ℝ) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    expMom l (ρ ∗ σ) = expMom l ρ * expMom l σ := by
  unfold expMom
  rw [Measure.lintegral_conv (measurable_expden l)]
  have : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-(l * (x + y)))) =
      ENNReal.ofReal (Real.exp (-(l * x))) * ENNReal.ofReal (Real.exp (-(l * y))) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; ring_nf
  simp only [this]
  simp only [lintegral_const_mul _ (measurable_expden l)]
  rw [lintegral_mul_const _ (measurable_expden l)]

lemma expMom_convPow (l : ℝ) : ∀ n, expMom l (convPow η n) = expMom l η ^ n
  | 0 => by simp [convPow, expMom, lintegral_dirac]
  | n + 1 => by
    have := convPow_isProb η n
    simp only [convPow]
    rw [expMom_conv, expMom_convPow l n, pow_succ, mul_comm]

lemma convPow_Iic_le (l : ℝ) (hl : 0 < l) (y : ℝ) (n : ℕ) :
    convPow η n (Set.Iic y) ≤ ENNReal.ofReal (Real.exp (l * y)) * expMom l η ^ n := by
  rw [← expMom_convPow η l n, expMom, ← lintegral_const_mul _ (measurable_expden l),
    ← lintegral_indicator_one measurableSet_Iic]
  refine lintegral_mono (fun x => ?_)
  simp only [Set.indicator_apply, Pi.one_apply]
  split_ifs with hx
  · rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add, ENNReal.one_le_ofReal,
      Real.one_le_exp_iff]
    have : x ≤ y := hx
    nlinarith
  · exact zero_le

lemma U_Iic_le (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1) (y : ℝ) :
    renewalMeasure η (Set.Iic y) ≤ ENNReal.ofReal (Real.exp (l * y)) * (1 - expMom l η)⁻¹ := by
  rw [renewalMeasure, Measure.sum_apply _ measurableSet_Iic, ← ENNReal.tsum_geometric,
    ← ENNReal.tsum_mul_left]
  exact ENNReal.tsum_le_tsum fun n => convPow_Iic_le η l hl y n

end GoldieRenewal.Implicit.KRT

/-! ## C5c: uniform bound, the left tail `A(-t) → 0`, and `A(t) → 1/μ` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit
open scoped ENNReal

lemma lintegral_Ioi_inv_sq (c t : ℝ) (hct : 0 < c + t) :
    ∫⁻ w in Set.Ioi c, ENNReal.ofReal (((w + t) ^ 2)⁻¹) = ENNReal.ofReal ((c + t)⁻¹) := by
  have hderiv : ∀ w ∈ Set.Ici c, HasDerivAt (fun w : ℝ => -(w + t)⁻¹) (((w + t) ^ 2)⁻¹) w := by
    intro w hw
    have hw' : w + t ≠ 0 := by have : c ≤ w := hw; linarith
    have := (((hasDerivAt_id' w).add_const t).inv hw').neg
    exact this.congr_deriv (by rw [neg_div, neg_neg, one_div])
  have hpos : ∀ w ∈ Set.Ioi c, 0 ≤ ((w + t) ^ 2)⁻¹ := fun w _ => by positivity
  have hlim : Tendsto (fun w : ℝ => -(w + t)⁻¹) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_right atTop t tendsto_id)).neg
    simpa using this
  have hint := integrableOn_Ioi_deriv_of_nonneg' hderiv hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg' hderiv hpos hlim
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall hpos)), hval]
  simp

variable (η : Measure ℝ) [IsProbabilityMeasure η]

instance renewal_sfinite : SFinite (renewalMeasure η) := by
  have : ∀ n, SFinite (convPow η n) := fun n => by have := convPow_isProb η n; infer_instance
  unfold renewalMeasure; infer_instance

/-- Smoothing domination: if `f ≤ F_a * φ` pointwise then `∫ f dU ≤ (sup A) ∫ φ`. -/
lemma lintegral_U_le (a : ℝ) (M : ℝ≥0∞) (hM : ∀ w, Afull η a w ≤ M)
    (φ : ℝ → ℝ≥0∞) (hφ : Measurable φ) (f : ℝ → ℝ≥0∞)
    (hf : ∀ x, f x ≤ ∫⁻ w, ENNReal.ofReal (fej a (w - x)) * φ w) :
    ∫⁻ x, f x ∂(renewalMeasure η) ≤ M * ∫⁻ w, φ w := by
  have hF : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (fej a (p.2 - p.1))) :=
    ENNReal.measurable_ofReal.comp ((continuous_fej a).measurable.comp
      (measurable_snd.sub measurable_fst))
  have hmeas : Measurable (Function.uncurry fun (x w : ℝ) =>
      ENNReal.ofReal (fej a (w - x)) * φ w) := by
    simp only [Function.uncurry_def]
    exact hF.mul (hφ.comp measurable_snd)
  have hFx : ∀ w, Measurable (fun x : ℝ => ENNReal.ofReal (fej a (w - x))) := fun w =>
    ENNReal.measurable_ofReal.comp ((continuous_fej a).measurable.comp
      (measurable_const.sub measurable_id))
  calc ∫⁻ x, f x ∂(renewalMeasure η)
      ≤ ∫⁻ x, (∫⁻ w, ENNReal.ofReal (fej a (w - x)) * φ w) ∂(renewalMeasure η) :=
        lintegral_mono hf
    _ = ∫⁻ w, ∫⁻ x, ENNReal.ofReal (fej a (w - x)) * φ w ∂(renewalMeasure η) :=
        lintegral_lintegral_swap (μ := renewalMeasure η) (ν := volume) hmeas.aemeasurable
    _ = ∫⁻ w, Afull η a w * φ w := by
        congr 1; ext w; rw [lintegral_mul_const _ (hFx w), Afull]
    _ ≤ ∫⁻ w, M * φ w := lintegral_mono fun w => by gcongr; exact hM w
    _ = M * ∫⁻ w, φ w := lintegral_const_mul _ hφ

/-- The uniform bound `M_a` for `A`. -/
noncomputable def Mbd (a : ℝ) : ℝ := 1 / (∫ x, x ∂η) + (2 / π) * ∫ θ in Set.Ioc 0 a, hLim η θ

lemma Afull_le (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a : ℝ) (ha : 0 < a) (w : ℝ) :
    Afull η a w ≤ ENNReal.ofReal (Mbd η a) := by
  have hI := integrableOn_hLim η h1 hμ hpos a ha
  have hm := measurable_hLim η
  have hI2 : IntegrableOn (fun θ => (1 - θ / a) * Real.cos (θ * w) * hLim η θ) (Set.Ioc 0 a) := by
    refine Integrable.mono' hI (Measurable.aestronglyMeasurable (by fun_prop)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with θ hθ
    obtain ⟨h1', h2'⟩ := T_mem a θ ha hθ
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg h1', abs_of_nonneg (hLim_nonneg η θ)]
    have : (1 - θ / a) * |Real.cos (θ * w)| ≤ 1 := by
      calc (1 - θ / a) * |Real.cos (θ * w)| ≤ 1 * 1 :=
            mul_le_mul h2' (Real.abs_cos_le_one _) (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    nlinarith [hLim_nonneg η θ]
  calc Afull η a w ≤ Afull η a w + Afull η a (-w) := le_self_add
    _ = _ := Afull_add_neg η h1 hμ hpos a ha w
    _ ≤ ENNReal.ofReal (Mbd η a) := by
        apply ENNReal.ofReal_le_ofReal
        rw [Mbd]
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        refine setIntegral_mono_on hI2 hI measurableSet_Ioc (fun θ hθ => ?_)
        obtain ⟨h1', h2'⟩ := T_mem a θ ha hθ
        have hc := Real.cos_le_one (θ * w)
        have hc' := Real.neg_one_le_cos (θ * w)
        have hh := hLim_nonneg η θ
        have : (1 - θ / a) * Real.cos (θ * w) ≤ 1 := by nlinarith
        nlinarith

end GoldieRenewal.Implicit.KRT

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit
open scoped ENNReal

lemma fej_shift_bound (a t x : ℝ) (ha : 0 < a) (ht : 0 < t) :
    ENNReal.ofReal (fej a (-t - x)) ≤
      Set.indicator (Set.Iic (-t / 2)) (fun _ => ENNReal.ofReal (a / (2 * π))) x +
      ENNReal.ofReal (2 / (π * a)) *
        Set.indicator (Set.Ioi (-t / 2)) (fun x => ENNReal.ofReal (((x + t) ^ 2)⁻¹)) x := by
  by_cases hx : x ≤ -t / 2
  · rw [Set.indicator_of_mem (show x ∈ Set.Iic (-t / 2) from hx)]
    exact le_add_right (ENNReal.ofReal_le_ofReal (fej_le a _ ha))
  · have hx' : -t / 2 < x := not_le.1 hx
    rw [Set.indicator_of_notMem (show x ∉ Set.Iic (-t / 2) from hx),
      Set.indicator_of_mem (show x ∈ Set.Ioi (-t / 2) from hx'), zero_add,
      ← ENNReal.ofReal_mul (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    have hne : -t - x ≠ 0 := (by linarith : -t - x < 0).ne
    have hxt : x + t ≠ 0 := (by linarith : 0 < x + t).ne'
    calc fej a (-t - x) ≤ 2 / (π * a * (-t - x) ^ 2) := fej_le_sq a _ ha hne
      _ = 2 / (π * a) * ((x + t) ^ 2)⁻¹ := by
        have : (-t - x) ^ 2 = (x + t) ^ 2 := by ring
        rw [this]; field_simp

lemma tail_dom (a t : ℝ) (ha : 0 < a) (ht : 4 / a ≤ t) (x : ℝ) :
    Set.indicator (Set.Ioi (-t / 2)) (fun x => ENNReal.ofReal (((x + t) ^ 2)⁻¹)) x ≤
      ∫⁻ w, ENNReal.ofReal (fej a (w - x)) * (ENNReal.ofReal (6 * π) *
        Set.indicator (Set.Ioi (t / 4 - t)) (fun w => ENNReal.ofReal (((w + t) ^ 2)⁻¹)) w) := by
  by_cases hx : x ∈ Set.Ioi (-t / 2)
  · rw [Set.indicator_of_mem hx]
    have hx' : -t / 2 < x := hx
    have h4a : 0 < 4 / a := by positivity
    have hta : 0 < t := by linarith
    have h1a : 1 / a ≤ t / 4 := by
      rw [div_le_iff₀ ha] at ht ⊢; rw [div_mul_eq_mul_div, le_div_iff₀ (by norm_num : (0:ℝ) < 4)]
      linarith
    set z := x + t with hz
    have hz1 : t / 2 < z := by linarith
    have hz0 : 0 < z := by linarith
    have hza : 1 / a ≤ z := by linarith
    have hmeas : Measurable (fun w : ℝ => ENNReal.ofReal (fej a (w - x)) * (ENNReal.ofReal (6 * π) *
        Set.indicator (Set.Ioi (t / 4 - t)) (fun w => ENNReal.ofReal (((w + t) ^ 2)⁻¹)) w)) := by
      refine (ENNReal.measurable_ofReal.comp ((continuous_fej a).measurable.comp
        (measurable_id.sub measurable_const))).mul (measurable_const.mul (Measurable.indicator
          (by fun_prop) measurableSet_Ioi))
    calc ENNReal.ofReal ((z ^ 2)⁻¹)
        = ∫⁻ w in Set.Icc (x - 1 / a) (x + 1 / a), ENNReal.ofReal (a / 2 * (z ^ 2)⁻¹) := by
          rw [setLIntegral_const, Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          field_simp; ring
      _ ≤ ∫⁻ w in Set.Icc (x - 1 / a) (x + 1 / a), ENNReal.ofReal (fej a (w - x)) *
            (ENNReal.ofReal (6 * π) * Set.indicator (Set.Ioi (t / 4 - t))
              (fun w => ENNReal.ofReal (((w + t) ^ 2)⁻¹)) w) := by
          refine setLIntegral_mono hmeas (fun w hw => ?_)
          have hw1 : x - 1 / a ≤ w := hw.1
          have hw2 : w ≤ x + 1 / a := hw.2
          have hwt : t / 4 - t < w := by linarith
          rw [Set.indicator_of_mem (show w ∈ Set.Ioi (t / 4 - t) from hwt),
            ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (fej_nonneg a _ ha)]
          apply ENNReal.ofReal_le_ofReal
          have hfe : a / (3 * π) ≤ fej a (w - x) := by
            apply fej_ge a _ ha
            rw [abs_le]
            constructor
            · have : -(1 / a) ≤ w - x := by linarith
              have h := mul_le_mul_of_nonneg_left this ha.le
              rw [mul_neg, mul_one_div_cancel ha.ne'] at h
              linarith
            · have : w - x ≤ 1 / a := by linarith
              have h := mul_le_mul_of_nonneg_left this ha.le
              rwa [mul_one_div_cancel ha.ne'] at h
          have hwt0 : 0 < w + t := by linarith
          have hwz : w + t ≤ 2 * z := by linarith
          have hsq : (w + t) ^ 2 ≤ 4 * z ^ 2 := by nlinarith
          have hinv : (4 * z ^ 2)⁻¹ ≤ ((w + t) ^ 2)⁻¹ :=
            inv_anti₀ (by positivity) hsq
          have hpi : 0 < π := Real.pi_pos
          calc a / 2 * (z ^ 2)⁻¹ = a / (3 * π) * (6 * π * (4 * z ^ 2)⁻¹) := by
                field_simp; ring
            _ ≤ fej a (w - x) * (6 * π * ((w + t) ^ 2)⁻¹) := by
                apply mul_le_mul hfe (by gcongr) (by positivity) (fej_nonneg a _ ha)
      _ ≤ _ := setLIntegral_le_lintegral _ _
  · rw [Set.indicator_of_notMem hx]; exact zero_le

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma tendsto_Afull_neg (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => Afull η a (-t)) atTop (𝓝 0) := by
  set M := ENNReal.ofReal (Mbd η a) with hMdef
  have hM := Afull_le η h1 hμ hpos a ha
  set B : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (a / (2 * π)) *
      (ENNReal.ofReal (Real.exp (l * (-t / 2))) * (1 - expMom l η)⁻¹) +
      ENNReal.ofReal (2 / (π * a)) * (M * (ENNReal.ofReal (6 * π) * ENNReal.ofReal ((t / 4)⁻¹)))
    with hB
  have hle : ∀ t, 4 / a ≤ t → Afull η a (-t) ≤ B t := by
    intro t ht
    have hta : 0 < t := lt_of_lt_of_le (by positivity) ht
    have hm1 : Measurable (Set.indicator (Set.Iic (-t / 2))
        (fun _ : ℝ => ENNReal.ofReal (a / (2 * π)))) :=
      measurable_const.indicator measurableSet_Iic
    have hm2 : Measurable (Set.indicator (Set.Ioi (-t / 2))
        (fun x : ℝ => ENNReal.ofReal (((x + t) ^ 2)⁻¹))) :=
      Measurable.indicator (by fun_prop) measurableSet_Ioi
    have hφ : Measurable (fun w : ℝ => ENNReal.ofReal (6 * π) *
        Set.indicator (Set.Ioi (t / 4 - t)) (fun w => ENNReal.ofReal (((w + t) ^ 2)⁻¹)) w) :=
      measurable_const.mul (Measurable.indicator (by fun_prop) measurableSet_Ioi)
    have hφint : ∫⁻ w, ENNReal.ofReal (6 * π) *
        Set.indicator (Set.Ioi (t / 4 - t)) (fun w => ENNReal.ofReal (((w + t) ^ 2)⁻¹)) w
        = ENNReal.ofReal (6 * π) * ENNReal.ofReal ((t / 4)⁻¹) := by
      rw [lintegral_const_mul _ (Measurable.indicator (by fun_prop) measurableSet_Ioi),
        lintegral_indicator measurableSet_Ioi, lintegral_Ioi_inv_sq _ _ (by linarith)]
      congr 2; ring
    rw [Afull]
    calc ∫⁻ x, ENNReal.ofReal (fej a (-t - x)) ∂(renewalMeasure η)
        ≤ ∫⁻ x, (Set.indicator (Set.Iic (-t / 2)) (fun _ => ENNReal.ofReal (a / (2 * π))) x +
            ENNReal.ofReal (2 / (π * a)) * Set.indicator (Set.Ioi (-t / 2))
              (fun x => ENNReal.ofReal (((x + t) ^ 2)⁻¹)) x) ∂(renewalMeasure η) :=
          lintegral_mono (fun x => fej_shift_bound a t x ha hta)
      _ = ∫⁻ x, Set.indicator (Set.Iic (-t / 2)) (fun _ => ENNReal.ofReal (a / (2 * π))) x
              ∂(renewalMeasure η) + ENNReal.ofReal (2 / (π * a)) *
            ∫⁻ x, Set.indicator (Set.Ioi (-t / 2))
              (fun x => ENNReal.ofReal (((x + t) ^ 2)⁻¹)) x ∂(renewalMeasure η) := by
          rw [lintegral_add_left hm1, lintegral_const_mul _ hm2]
      _ ≤ B t := by
          refine add_le_add ?_ ?_
          · rw [lintegral_indicator_const measurableSet_Iic]
            gcongr
            exact U_Iic_le η l hl hr _
          · gcongr
            rw [← hφint]
            exact lintegral_U_le η a M hM _ hφ _ (tail_dom a t ha ht)
  have hr' : (1 - expMom l η)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 (tsub_pos_of_lt hr).ne'
  have he : Tendsto (fun t : ℝ => ENNReal.ofReal (Real.exp (l * (-t / 2)))) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => l * (-t / 2)) atTop atBot := by
      have : Tendsto (fun t : ℝ => -t / 2) atTop atBot :=
        (tendsto_neg_atTop_atBot.atBot_div_const (by norm_num))
      exact this.const_mul_atBot hl
    have := (ENNReal.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h2)
    simpa [Function.comp_def] using this
  have hi : Tendsto (fun t : ℝ => ENNReal.ofReal ((t / 4)⁻¹)) atTop (𝓝 0) := by
    have h2 : Tendsto (fun t : ℝ => (t / 4)⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_id.atTop_div_const (by norm_num))
    have := (ENNReal.continuous_ofReal.tendsto 0).comp h2
    simpa [Function.comp_def] using this
  have hBt : Tendsto B atTop (𝓝 0) := by
    have t1 := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.mul_const he (Or.inr hr'))
      (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (a / (2 * π)))
    have t2 := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.const_mul
      (ENNReal.Tendsto.const_mul hi (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (6 * π)))
      (Or.inr ENNReal.ofReal_ne_top) (a := M)) (Or.inr ENNReal.ofReal_ne_top)
      (a := ENNReal.ofReal (2 / (π * a)))
    have := t1.add t2
    simpa [hB] using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hBt
    (Eventually.of_forall fun _ => zero_le) (eventually_atTop.2 ⟨4 / a, hle⟩)

/-- **C5 (Fejér renewal limit)**: `∫ F_a(t - x) U(dx) → 1/μ`. -/
theorem fejer_renewal_limit (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun t => Afull η a t) atTop (𝓝 (ENNReal.ofReal (1 / ∫ x, x ∂η))) := by
  have hsum : Tendsto (fun t => Afull η a t + Afull η a (-t)) atTop
      (𝓝 (ENNReal.ofReal (1 / ∫ x, x ∂η))) := by
    have := (ENNReal.continuous_ofReal.tendsto _).comp
      (((tendsto_cos_hLim η h1 hμ hpos a ha).const_mul (2 / π)).const_add (1 / ∫ x, x ∂η))
    simp only [mul_zero, add_zero] at this
    refine this.congr (fun t => ?_)
    simp only [Function.comp_apply]
    rw [Afull_add_neg η h1 hμ hpos a ha t]
  have hneg := tendsto_Afull_neg η h1 hμ hpos l hl hr a ha
  have := ENNReal.Tendsto.sub hsum hneg (Or.inl ENNReal.ofReal_ne_top)
  rw [tsub_zero] at this
  refine this.congr (fun t => ?_)
  have hfin : Afull η a (-t) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (Afull_le η h1 hμ hpos a ha (-t))
  exact ENNReal.add_sub_cancel_right hfin

end GoldieRenewal.Implicit.KRT

/-! ## C7: the kernel `k(y) = e^{-y} 1_{y ≥ 0}`: `H = k ⋆ U` is bounded and `H(t) → 1/μ` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit
open scoped ENNReal

/-- `k(y) = e^{-y} 1_{y ≥ 0}` in `[0,∞]`. -/
noncomputable def kE (y : ℝ) : ℝ≥0∞ :=
  Set.indicator (Set.Ici 0) (fun y => ENNReal.ofReal (Real.exp (-y))) y

lemma measurable_kE : Measurable kE := by
  show Measurable (Set.indicator (Set.Ici (0:ℝ)) (fun y => ENNReal.ofReal (Real.exp (-y))))
  exact Measurable.indicator (by fun_prop) measurableSet_Ici

lemma kE_of_nonneg {y : ℝ} (hy : 0 ≤ y) : kE y = ENNReal.ofReal (Real.exp (-y)) := by
  unfold kE; rw [Set.indicator_apply, if_pos (Set.mem_Ici.2 hy)]

lemma kE_of_neg {y : ℝ} (hy : y < 0) : kE y = 0 := by
  unfold kE; rw [Set.indicator_apply, if_neg (fun h => absurd (Set.mem_Ici.1 h) (not_le.2 hy))]

lemma lintegral_kE : ∫⁻ y, kE y = 1 := by
  have hi : IntegrableOn (fun y : ℝ => Real.exp (-y)) (Set.Ici 0) := by
    rw [integrableOn_Ici_iff_integrableOn_Ioi]; simpa using integrableOn_exp_neg_Ioi 0
  unfold kE
  rw [lintegral_indicator measurableSet_Ici, ← ofReal_integral_eq_lintegral_ofReal hi
    (Eventually.of_forall fun y => (Real.exp_pos _).le), integral_Ici_eq_integral_Ioi,
    integral_exp_neg_Ioi_zero, ENNReal.ofReal_one]

noncomputable def kp (d u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (2 * d)) * kE (u + d)
noncomputable def km (d u : ℝ) : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-(2 * d))) * kE (u - d)

lemma measurable_kp (d : ℝ) : Measurable (kp d) :=
  measurable_const.mul (measurable_kE.comp (measurable_id.add_const d))

lemma measurable_km (d : ℝ) : Measurable (km d) :=
  measurable_const.mul (measurable_kE.comp (measurable_id.sub_const d))

lemma lintegral_kp (d : ℝ) : ∫⁻ u, kp d u = ENNReal.ofReal (Real.exp (2 * d)) := by
  unfold kp
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_right_eq_self kE d,
    lintegral_kE, mul_one]

lemma lintegral_km (d : ℝ) : ∫⁻ u, km d u = ENNReal.ofReal (Real.exp (-(2 * d))) := by
  unfold km
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_right_eq_self kE d,
    lintegral_kE, mul_one]

lemma kE_le_kp (d y v : ℝ) (hv : |v| ≤ d) : kE y ≤ kp d (y - v) := by
  rcases lt_or_ge y 0 with hy | hy
  · rw [kE_of_neg hy]; exact zero_le
  · have h1 : 0 ≤ y - v + d := by have := le_abs_self v; linarith
    rw [kp, kE_of_nonneg hy, kE_of_nonneg h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have := neg_abs_le v
    linarith

lemma km_le_kE_of (d y v : ℝ) (hv : |v| ≤ d) : km d (y - v) ≤ kE y := by
  rcases lt_or_ge (y - v - d) 0 with hy | hy
  · rw [km, kE_of_neg hy, mul_zero]; exact zero_le
  · have h1 : 0 ≤ y := by have := le_abs_self v; have := neg_abs_le v; linarith
    rw [km, kE_of_nonneg hy, kE_of_nonneg h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    have := le_abs_self v
    linarith

lemma km_le_kE (d z : ℝ) (hd : 0 ≤ d) : km d z ≤ kE z := by
  rcases lt_or_ge (z - d) 0 with hy | hy
  · rw [km, kE_of_neg hy, mul_zero]; exact zero_le
  · have h1 : 0 ≤ z := by linarith
    rw [km, kE_of_nonneg hy, kE_of_nonneg h1, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.2
    linarith

lemma measurable_ofReal_fej (a : ℝ) : Measurable (fun v => ENNReal.ofReal (fej a v)) :=
  ENNReal.measurable_ofReal.comp (continuous_fej a).measurable

lemma lintegral_fej (a : ℝ) (ha : 0 < a) : ∫⁻ v, ENNReal.ofReal (fej a v) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_fej a ha)
    (Eventually.of_forall fun v => fej_nonneg a v ha), integral_fej a ha, ENNReal.ofReal_one]

/-- Fejér mass near `0` and its complement. -/
noncomputable def qF (a d : ℝ) : ℝ≥0∞ := ∫⁻ v in {v : ℝ | |v| ≤ d}, ENNReal.ofReal (fej a v)
noncomputable def epsF (a d : ℝ) : ℝ≥0∞ := ∫⁻ v in {v : ℝ | d < |v|}, ENNReal.ofReal (fej a v)

lemma measurableSet_absle (d : ℝ) : MeasurableSet {v : ℝ | |v| ≤ d} :=
  measurableSet_le continuous_abs.measurable measurable_const

lemma measurableSet_absgt (d : ℝ) : MeasurableSet {v : ℝ | d < |v|} :=
  measurableSet_lt measurable_const continuous_abs.measurable

lemma qF_add_epsF (a d : ℝ) (ha : 0 < a) : qF a d + epsF a d = 1 := by
  have hc : {v : ℝ | |v| ≤ d}ᶜ = {v : ℝ | d < |v|} := by ext v; simp [not_le]
  rw [qF, epsF, ← hc, lintegral_add_compl _ (measurableSet_absle d), lintegral_fej a ha]

lemma epsF_le (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    epsF a d ≤ ENNReal.ofReal (4 / (π * a * d)) := by
  set G : ℝ → ℝ≥0∞ := Set.indicator (Set.Ioi d)
    (fun v => ENNReal.ofReal (2 / (π * a)) * ENNReal.ofReal (((v + 0) ^ 2)⁻¹)) with hG
  have hGm : Measurable G := by
    rw [hG]; exact Measurable.indicator (by fun_prop) measurableSet_Ioi
  have hpt : ∀ v, Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v ≤
      G v + G (-v) := by
    intro v
    by_cases hv : d < |v|
    · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | d < |v|} from hv)]
      have hv0 : v ≠ 0 := by intro h; rw [h, abs_zero] at hv; linarith
      have hb : ENNReal.ofReal (fej a v) ≤
          ENNReal.ofReal (2 / (π * a)) * ENNReal.ofReal (((v + 0) ^ 2)⁻¹) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc fej a v ≤ 2 / (π * a * v ^ 2) := fej_le_sq a v ha hv0
          _ = 2 / (π * a) * ((v + 0) ^ 2)⁻¹ := by rw [add_zero]; field_simp
      rcases le_or_gt 0 v with h0 | h0
      · have : d < v := by rwa [abs_of_nonneg h0] at hv
        rw [hG, Set.indicator_of_mem (show v ∈ Set.Ioi d from this)]
        exact hb.trans le_self_add
      · have : d < -v := by rwa [abs_of_neg h0] at hv
        rw [hG, Set.indicator_of_mem (show -v ∈ Set.Ioi d from this)]
        have : ((-v + 0) ^ 2)⁻¹ = ((v + 0) ^ 2)⁻¹ := by ring
        rw [this]
        exact hb.trans le_add_self
    · rw [Set.indicator_of_notMem (show v ∉ {v : ℝ | d < |v|} from hv)]; exact zero_le
  have hGi : ∫⁻ v, G v = ENNReal.ofReal (2 / (π * a)) * ENNReal.ofReal d⁻¹ := by
    rw [hG, lintegral_indicator measurableSet_Ioi, lintegral_const_mul _ (by fun_prop),
      lintegral_Ioi_inv_sq d 0 (by linarith), add_zero]
  calc epsF a d = ∫⁻ v, Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v := by
        rw [epsF, lintegral_indicator (measurableSet_absgt d)]
    _ ≤ ∫⁻ v, (G v + G (-v)) := lintegral_mono hpt
    _ = (∫⁻ v, G v) + ∫⁻ v, G (-v) := lintegral_add_left hGm (fun v => G (-v))
    _ = ENNReal.ofReal (4 / (π * a * d)) := by
        have hGi' : ∫⁻ v, G (-v) = ENNReal.ofReal (2 / (π * a)) * ENNReal.ofReal d⁻¹ := by
          rw [lintegral_neg_eq_self G]; exact hGi
        rw [hGi, hGi', ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1; field_simp; ring

lemma qF_ge (a d : ℝ) (ha : 0 < a) (hd : 0 < d) :
    ENNReal.ofReal (1 - 4 / (π * a * d)) ≤ qF a d := by
  have h1 := qF_add_epsF a d ha
  have hfin : epsF a d ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (epsF_le a d ha hd)
  have hq : qF a d = 1 - epsF a d := ENNReal.eq_sub_of_add_eq hfin h1
  rw [hq, ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
  exact tsub_le_tsub_left (epsF_le a d ha hd) 1

lemma qF_le_one (a d : ℝ) (ha : 0 < a) : qF a d ≤ 1 := by
  rw [← qF_add_epsF a d ha]; exact le_self_add

/-- pointwise upper smoothing: `k(y) q ≤ (k_d^+ ⋆ F_a)(y)`. -/
lemma upper_pt (a d y : ℝ) :
    kE y * qF a d ≤ ∫⁻ u, kp d u * ENNReal.ofReal (fej a (y - u)) := by
  rw [← lintegral_sub_left_eq_self (fun u => kp d u * ENNReal.ofReal (fej a (y - u))) y]
  simp only [sub_sub_cancel]
  calc kE y * qF a d = ∫⁻ v in {v : ℝ | |v| ≤ d}, kE y * ENNReal.ofReal (fej a v) := by
        rw [qF, lintegral_const_mul _ (measurable_ofReal_fej a)]
    _ ≤ ∫⁻ v in {v : ℝ | |v| ≤ d}, kp d (y - v) * ENNReal.ofReal (fej a v) := by
        refine lintegral_mono_ae ((ae_restrict_iff' (measurableSet_absle d)).2
          (Eventually.of_forall fun v hv => ?_))
        gcongr
        exact kE_le_kp d y v hv
    _ ≤ ∫⁻ v, kp d (y - v) * ENNReal.ofReal (fej a v) := setLIntegral_le_lintegral _ _

/-- pointwise lower smoothing: `(k_d^- ⋆ F_a)(y) ≤ k(y) + ∫_{|v|>d} F_a(v) k(y - v) dv`. -/
lemma lower_pt (a d y : ℝ) (ha : 0 < a) (hd : 0 ≤ d) :
    ∫⁻ u, km d u * ENNReal.ofReal (fej a (y - u)) ≤ kE y +
      ∫⁻ v, Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v * kE (y - v) := by
  rw [← lintegral_sub_left_eq_self (fun u => km d u * ENNReal.ofReal (fej a (y - u))) y]
  simp only [sub_sub_cancel]
  have hpt : ∀ v, km d (y - v) * ENNReal.ofReal (fej a v) ≤ kE y * ENNReal.ofReal (fej a v) +
      Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v * kE (y - v) := by
    intro v
    by_cases hv : |v| ≤ d
    · refine le_trans ?_ le_self_add
      gcongr
      exact km_le_kE_of d y v hv
    · rw [Set.indicator_of_mem (show v ∈ {v : ℝ | d < |v|} from not_le.1 hv)]
      refine le_trans ?_ le_add_self
      rw [mul_comm]
      gcongr
      exact km_le_kE d _ hd
  calc ∫⁻ v, km d (y - v) * ENNReal.ofReal (fej a v)
      ≤ ∫⁻ v, (kE y * ENNReal.ofReal (fej a v) +
          Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v * kE (y - v)) :=
        lintegral_mono hpt
    _ = kE y * (∫⁻ v, ENNReal.ofReal (fej a v)) +
          ∫⁻ v, Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) v * kE (y - v) := by
        rw [lintegral_add_left (f := fun v => kE y * ENNReal.ofReal (fej a v))
          ((measurable_ofReal_fej a).const_mul _), lintegral_const_mul _ (measurable_ofReal_fej a)]
    _ = _ := by rw [lintegral_fej a ha, mul_one]

variable (η : Measure ℝ) [IsProbabilityMeasure η]

/-- `H(t) = ∫ k(t - x) U(dx)`. -/
noncomputable def Hk (t : ℝ) : ℝ≥0∞ := ∫⁻ x, kE (t - x) ∂(renewalMeasure η)

lemma measurable_kerU (K : ℝ → ℝ≥0∞) (hK : Measurable K) :
    Measurable (fun t => ∫⁻ x, K (t - x) ∂(renewalMeasure η)) :=
  (hK.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'

lemma measurable_Afull (a : ℝ) : Measurable (Afull η a) :=
  measurable_kerU η _ (measurable_ofReal_fej a)

lemma measurable_Hk : Measurable (Hk η) := measurable_kerU η _ measurable_kE

/-- Tonelli: `∫ (g ⋆ K)(t - x) U(dx) = ∫ g(u) (K ⋆ U)(t - u) du`. -/
lemma swapK (K : ℝ → ℝ≥0∞) (hK : Measurable K) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (t : ℝ) :
    ∫⁻ x, (∫⁻ u, g u * K (t - x - u)) ∂(renewalMeasure η) =
      ∫⁻ u, g u * ∫⁻ x, K (t - u - x) ∂(renewalMeasure η) := by
  have hmeas : Measurable (Function.uncurry fun (x u : ℝ) => g u * K (t - x - u)) := by
    simp only [Function.uncurry_def]
    exact (hg.comp measurable_snd).mul
      (hK.comp ((measurable_const.sub measurable_fst).sub measurable_snd))
  rw [lintegral_lintegral_swap hmeas.aemeasurable]
  congr 1; ext u
  have hKx : Measurable (fun x => K (t - x - u)) :=
    hK.comp ((measurable_const.sub measurable_id).sub measurable_const)
  rw [lintegral_const_mul _ hKx]
  congr 1
  refine lintegral_congr fun x => ?_
  congr 1; ring

lemma smooth_limit (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1)
    (a : ℝ) (ha : 0 < a) (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hgi : ∫⁻ u, g u ≠ ∞) :
    Tendsto (fun t => ∫⁻ u, g u * Afull η a (t - u)) atTop
      (𝓝 ((∫⁻ u, g u) * ENNReal.ofReal (1 / ∫ x, x ∂η))) := by
  rw [← lintegral_mul_const _ hg]
  refine tendsto_lintegral_filter_of_dominated_convergence
    (fun u => g u * ENNReal.ofReal (Mbd η a)) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t =>
      hg.mul ((measurable_Afull η a).comp (measurable_const.sub measurable_id))
  · exact Eventually.of_forall fun t => Eventually.of_forall fun u => by
      gcongr; exact Afull_le η h1 hμ hpos a ha _
  · rw [lintegral_mul_const _ hg]; exact ENNReal.mul_ne_top hgi ENNReal.ofReal_ne_top
  · refine Eventually.of_forall fun u => ?_
    have hu : Tendsto (fun t : ℝ => t - u) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-u) tendsto_id
    exact ENNReal.Tendsto.const_mul ((fejer_renewal_limit η h1 hμ hpos l hl hr a ha).comp hu)
      (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')

lemma upper_int (a d t : ℝ) :
    Hk η t * qF a d ≤ ∫⁻ u, kp d u * Afull η a (t - u) := by
  calc Hk η t * qF a d = ∫⁻ x, kE (t - x) * qF a d ∂(renewalMeasure η) := by
        have hk : Measurable (fun x => kE (t - x)) := measurable_kE.comp (measurable_const.sub measurable_id)
        rw [Hk, lintegral_mul_const _ hk]
    _ ≤ ∫⁻ x, (∫⁻ u, kp d u * ENNReal.ofReal (fej a (t - x - u))) ∂(renewalMeasure η) :=
        lintegral_mono fun x => upper_pt a d (t - x)
    _ = _ := swapK η _ (measurable_ofReal_fej a) _ (measurable_kp d) t

/-- the uniform bound for `H`. -/
noncomputable def C0 : ℝ≥0∞ := ENNReal.ofReal (Real.exp 2 * Mbd η 4 / (1 - 1 / π))

lemma one_sub_inv_pi_pos : 0 < 1 - 1 / π := by
  have := Real.pi_gt_three
  rw [sub_pos, div_lt_one (by positivity)]; linarith

lemma Hk_le (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (t : ℝ) : Hk η t ≤ C0 η := by
  have hq := qF_ge 4 1 (by norm_num) one_pos
  have hc : (4:ℝ) / (π * 4 * 1) = 1 / π := by field_simp
  rw [hc] at hq
  have hq0 : qF 4 1 ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 one_sub_inv_pi_pos) hq).ne'
  have hqt : qF 4 1 ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top (qF_le_one 4 1 (by norm_num))
  have hup : Hk η t * qF 4 1 ≤ ENNReal.ofReal (Real.exp 2 * Mbd η 4) := by
    calc Hk η t * qF 4 1 ≤ ∫⁻ u, kp 1 u * Afull η 4 (t - u) := upper_int η 4 1 t
      _ ≤ ∫⁻ u, kp 1 u * ENNReal.ofReal (Mbd η 4) :=
          lintegral_mono fun u => by gcongr; exact Afull_le η h1 hμ hpos 4 (by norm_num) _
      _ = ENNReal.ofReal (Real.exp 2 * Mbd η 4) := by
          rw [lintegral_mul_const _ (measurable_kp 1), lintegral_kp, mul_one,
            ← ENNReal.ofReal_mul (Real.exp_pos _).le]
  calc Hk η t ≤ ENNReal.ofReal (Real.exp 2 * Mbd η 4) / qF 4 1 :=
        (ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hqt)).2 hup
    _ ≤ ENNReal.ofReal (Real.exp 2 * Mbd η 4) / ENNReal.ofReal (1 - 1 / π) :=
        ENNReal.div_le_div_left hq _
    _ = C0 η := by rw [C0, ENNReal.ofReal_div_of_pos one_sub_inv_pi_pos]

lemma C0_ne_top : C0 η ≠ ∞ := ENNReal.ofReal_ne_top

lemma lower_int (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (a d t : ℝ) (ha : 0 < a) (hd : 0 ≤ d) :
    ∫⁻ u, km d u * Afull η a (t - u) ≤ Hk η t + C0 η * epsF a d := by
  set I : ℝ → ℝ≥0∞ := Set.indicator {v : ℝ | d < |v|} (fun v => ENNReal.ofReal (fej a v)) with hI
  have hIm : Measurable I := by
    rw [hI]; exact (measurable_ofReal_fej a).indicator (measurableSet_absgt d)
  calc ∫⁻ u, km d u * Afull η a (t - u)
      = ∫⁻ x, (∫⁻ u, km d u * ENNReal.ofReal (fej a (t - x - u))) ∂(renewalMeasure η) :=
        (swapK η _ (measurable_ofReal_fej a) _ (measurable_km d) t).symm
    _ ≤ ∫⁻ x, (kE (t - x) + ∫⁻ v, I v * kE (t - x - v)) ∂(renewalMeasure η) :=
        lintegral_mono fun x => lower_pt a d (t - x) ha hd
    _ = Hk η t + ∫⁻ x, (∫⁻ v, I v * kE (t - x - v)) ∂(renewalMeasure η) := by
        have hk : Measurable (fun x => kE (t - x)) := measurable_kE.comp (measurable_const.sub measurable_id)
        rw [lintegral_add_left hk]; rfl
    _ = Hk η t + ∫⁻ v, I v * Hk η (t - v) := by
        rw [swapK η _ measurable_kE _ hIm t]; rfl
    _ ≤ Hk η t + ∫⁻ v, I v * C0 η := by
        gcongr with v; exact Hk_le η h1 hμ hpos _
    _ = Hk η t + C0 η * epsF a d := by
        rw [lintegral_mul_const _ hIm, hI, lintegral_indicator (measurableSet_absgt d), epsF,
          mul_comm]

lemma tendsto_delta : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

lemma delta_pos (n : ℕ) : 0 < 1 / ((n : ℝ) + 1) := by positivity

lemma delta_le_one (n : ℕ) : 1 / ((n : ℝ) + 1) ≤ 1 := by
  rw [div_le_one (by positivity)]; have := n.cast_nonneg (α := ℝ); linarith

/-- **C7 (kernel renewal limit)**: `H(t) = ∫ e^{-(t-x)} 1_{x ≤ t} U(dx) → 1/μ`. -/
theorem Hk_tendsto (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1) :
    Tendsto (Hk η) atTop (𝓝 (ENNReal.ofReal (1 / ∫ x, x ∂η))) := by
  set L : ℝ := 1 / ∫ x, x ∂η with hL
  have hL0 : 0 < L := by positivity
  obtain ⟨δ, hδ⟩ : ∃ δ : ℕ → ℝ, δ = fun n : ℕ => 1 / ((n : ℝ) + 1) := ⟨_, rfl⟩
  have hδp : ∀ n, 0 < δ n := fun n => by rw [hδ]; exact delta_pos n
  have hδ1 : ∀ n, δ n ≤ 1 := fun n => by rw [hδ]; exact delta_le_one n
  have hδt : Tendsto δ atTop (𝓝 0) := by rw [hδ]; exact tendsto_delta
  -- parameters: d = δ, a = 4 / δ^3, so 4 / (π a d) = δ^2 / π
  have hcd : ∀ n, 4 / (π * (4 / δ n ^ 3) * δ n) = δ n ^ 2 / π := by
    intro n; have := hδp n; field_simp
  have hc1 : ∀ n, δ n ^ 2 / π < 1 := by
    intro n
    have h0 := hδp n; have h1' := hδ1 n; have := Real.pi_gt_three
    rw [div_lt_one (by positivity)]; nlinarith
  have ha : ∀ n, 0 < 4 / δ n ^ 3 := fun n => by have := hδp n; positivity
  refine tendsto_order.2 ⟨fun b hb => ?_, fun b hb => ?_⟩
  · -- lower bound
    have hlo : Tendsto (fun n => ENNReal.ofReal (Real.exp (-(2 * δ n)) * L) -
        C0 η * ENNReal.ofReal (δ n ^ 2 / π)) atTop (𝓝 (ENNReal.ofReal L)) := by
      have e1 : Tendsto (fun n => Real.exp (-(2 * δ n)) * L) atTop (𝓝 L) := by
        have hc : Continuous (fun x : ℝ => Real.exp (-(2 * x)) * L) := by fun_prop
        have := (hc.tendsto 0).comp hδt
        simpa [Function.comp_def] using this
      have e2 : Tendsto (fun n => δ n ^ 2 / π) atTop (𝓝 0) := by
        simpa using (hδt.pow 2).div_const π
      have := ENNReal.Tendsto.sub (ENNReal.tendsto_ofReal e1)
        (ENNReal.Tendsto.const_mul (ENNReal.tendsto_ofReal e2) (Or.inr (C0_ne_top η)))
        (Or.inl ENNReal.ofReal_ne_top)
      simpa using this
    obtain ⟨n, hn⟩ := (hlo.eventually (lt_mem_nhds hb)).exists
    have hlim := smooth_limit η h1 hμ hpos l hl hr (4 / δ n ^ 3) (ha n) (km (δ n))
      (measurable_km _) (by rw [lintegral_km]; exact ENNReal.ofReal_ne_top)
    rw [lintegral_km, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hlim
    have hlim2 := ENNReal.Tendsto.sub hlim
      (tendsto_const_nhds (x := C0 η * ENNReal.ofReal (δ n ^ 2 / π)))
      (Or.inl ENNReal.ofReal_ne_top)
    filter_upwards [hlim2.eventually (lt_mem_nhds hn)] with t ht
    refine lt_of_lt_of_le ht ?_
    rw [tsub_le_iff_right]
    refine (lower_int η h1 hμ hpos (4 / δ n ^ 3) (δ n) t (ha n) (hδp n).le).trans ?_
    gcongr
    rw [← hcd n]
    exact epsF_le _ _ (ha n) (hδp n)
  · -- upper bound
    have hup : Tendsto (fun n => ENNReal.ofReal (Real.exp (2 * δ n) * L / (1 - δ n ^ 2 / π)))
        atTop (𝓝 (ENNReal.ofReal L)) := by
      refine ENNReal.tendsto_ofReal ?_
      have hf : ContinuousAt (fun x : ℝ => Real.exp (2 * x) * L / (1 - x ^ 2 / π)) 0 := by
        refine ContinuousAt.div (by fun_prop) (by fun_prop) ?_
        simp
      have := hf.tendsto.comp hδt
      simpa [Function.comp_def] using this
    obtain ⟨n, hn⟩ := (hup.eventually (gt_mem_nhds hb)).exists
    have hlim := smooth_limit η h1 hμ hpos l hl hr (4 / δ n ^ 3) (ha n) (kp (δ n))
      (measurable_kp _) (by rw [lintegral_kp]; exact ENNReal.ofReal_ne_top)
    rw [lintegral_kp, ← ENNReal.ofReal_mul (Real.exp_pos _).le] at hlim
    have hpos1 : 0 < 1 - δ n ^ 2 / π := by linarith [hc1 n]
    have hlim2 := ENNReal.Tendsto.div_const hlim
      (Or.inr (ENNReal.ofReal_pos.2 hpos1).ne' : _ ∨ ENNReal.ofReal (1 - δ n ^ 2 / π) ≠ 0)
    rw [← ENNReal.ofReal_div_of_pos hpos1] at hlim2
    filter_upwards [hlim2.eventually (gt_mem_nhds hn)] with t ht
    refine lt_of_le_of_lt ?_ ht
    have hq := qF_ge (4 / δ n ^ 3) (δ n) (ha n) (hδp n)
    rw [hcd n] at hq
    have hq0 : qF (4 / δ n ^ 3) (δ n) ≠ 0 := (lt_of_lt_of_le (ENNReal.ofReal_pos.2 hpos1) hq).ne'
    have hqt : qF (4 / δ n ^ 3) (δ n) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.one_ne_top (qF_le_one _ _ (ha n))
    calc Hk η t ≤ (∫⁻ u, kp (δ n) u * Afull η (4 / δ n ^ 3) (t - u)) / qF (4 / δ n ^ 3) (δ n) :=
          (ENNReal.le_div_iff_mul_le (Or.inl hq0) (Or.inl hqt)).2 (upper_int η _ _ t)
      _ ≤ (∫⁻ u, kp (δ n) u * Afull η (4 / δ n ^ 3) (t - u)) /
            ENNReal.ofReal (1 - δ n ^ 2 / π) := ENNReal.div_le_div_left hq _

end GoldieRenewal.Implicit.KRT

/-! ## C2: the tilted law `η = e^{κy} P(log M ∈ dy, M > 0)` satisfies the KRT hypotheses -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit ProbabilityTheory
open scoped ENNReal

noncomputable def tiltOn (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) : Measure ℝ :=
  ((μ.restrict s).map (fun x => Real.log |x|)).withDensity
    (fun u => ENNReal.ofReal (Real.exp (κ * u)))

lemma meas_logabs : Measurable (fun x : ℝ => Real.log |x|) :=
  Real.measurable_log.comp continuous_abs.measurable

lemma meas_expden (κ : ℝ) : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (κ * u))) :=
  (Real.continuous_exp.comp (continuous_const.mul continuous_id)).measurable.ennreal_ofReal

lemma lintegral_tiltOn (κ : ℝ) (μ : Measure ℝ) (s : Set ℝ) (f : ℝ → ℝ≥0∞)
    (hf : Measurable f) :
    ∫⁻ y, f y ∂(tiltOn κ μ s) =
      ∫⁻ x in s, ENNReal.ofReal (Real.exp (κ * Real.log |x|)) * f (Real.log |x|) ∂μ := by
  unfold tiltOn
  rw [lintegral_withDensity_eq_lintegral_mul _ (meas_expden κ) hf,
    lintegral_map ((meas_expden κ).mul hf) meas_logabs]
  rfl

lemma exp_kappa_log_abs (κ x : ℝ) (hx : x ≠ 0) :
    Real.exp (κ * Real.log |x|) = |x| ^ κ := by
  rw [Real.rpow_def_of_pos (abs_pos.mpr hx), mul_comm]

lemma meas_rpow_abs (κ : ℝ) : Measurable (fun x : ℝ => |x| ^ κ) :=
  (continuous_abs.measurable).pow_const κ

/-- transfer of integrals from `η = tiltOn κ ν (0,∞)` to `ν` when `ν (-∞,0) = 0`. -/
lemma lintegral_eta (κ : ℝ) (hκ : 0 < κ) (ν : Measure ℝ) (hν0 : ν (Set.Iio 0) = 0)
    (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(tiltOn κ ν (Set.Ioi 0)) =
      ∫⁻ x, ENNReal.ofReal (|x| ^ κ) * f (Real.log |x|) ∂ν := by
  rw [lintegral_tiltOn κ ν _ f hf]
  have h1 : ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (Real.exp (κ * Real.log |x|)) * f (Real.log |x|) ∂ν =
      ∫⁻ x in Set.Ioi 0, ENNReal.ofReal (|x| ^ κ) * f (Real.log |x|) ∂ν :=
    setLIntegral_congr_fun measurableSet_Ioi (fun x hx => by
      rw [exp_kappa_log_abs κ x (ne_of_gt hx)])
  rw [h1]
  have h2 : ∫⁻ x in (Set.Ioi (0:ℝ))ᶜ, ENNReal.ofReal (|x| ^ κ) * f (Real.log |x|) ∂ν = 0 := by
    rw [Set.compl_Ioi, ← Set.Iio_union_right]
    refine le_antisymm ((lintegral_union_le _ _ _).trans ?_) zero_le
    rw [setLIntegral_measure_zero _ _ hν0, lintegral_singleton]
    simp [Real.zero_rpow hκ.ne']
  have h3 := lintegral_add_compl (μ := ν) (fun x => ENNReal.ofReal (|x| ^ κ) * f (Real.log |x|))
    (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))
  rw [h2, add_zero] at h3
  exact h3

/-- `y log y ≥ y - 1` with `y = |x|^κ`. -/
lemma key_ineq (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    |x| ^ κ - 1 ≤ κ * (|x| ^ κ * Real.log |x|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hκ.ne']
  · have hy : 0 < |x| ^ κ := Real.rpow_pos_of_pos (abs_pos.2 hx) κ
    have hl : Real.log (|x| ^ κ) = κ * Real.log |x| := Real.log_rpow (abs_pos.2 hx) κ
    have h := Real.log_le_sub_one_of_pos (inv_pos.2 hy)
    rw [Real.log_inv, hl] at h
    have h2 := mul_le_mul_of_nonneg_left h hy.le
    rw [mul_sub, mul_inv_cancel₀ hy.ne', mul_one] at h2
    nlinarith

lemma key_ineq_strict (κ : ℝ) (hκ : 0 < κ) (x : ℝ) (hx1 : |x| ^ κ ≠ 1) :
    |x| ^ κ - 1 < κ * (|x| ^ κ * Real.log |x|) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Real.zero_rpow hκ.ne']
  · have hy : 0 < |x| ^ κ := Real.rpow_pos_of_pos (abs_pos.2 hx) κ
    have hl : Real.log (|x| ^ κ) = κ * Real.log |x| := Real.log_rpow (abs_pos.2 hx) κ
    have hne : (|x| ^ κ)⁻¹ ≠ 1 := by
      intro h; apply hx1; rw [inv_eq_one] at h; exact h
    have h := Real.log_lt_sub_one_of_pos (inv_pos.2 hy) hne
    rw [Real.log_inv, hl] at h
    have h2 := mul_lt_mul_of_pos_left h hy
    rw [mul_sub, mul_inv_cancel₀ hy.ne', mul_one] at h2
    nlinarith

lemma abs_phi_le (κ : ℝ) (hκ : 0 < κ) (x : ℝ) :
    |x| ^ κ * abs (Real.log |x|) ≤ |x| ^ κ * max (Real.log |x|) 0 + 1 / κ := by
  have hy : 0 ≤ |x| ^ κ := Real.rpow_nonneg (abs_nonneg x) κ
  have hk : 0 < 1 / κ := by positivity
  rcases le_or_gt 0 (Real.log |x|) with h | h
  · rw [abs_of_nonneg h, max_eq_left h]; linarith
  · rw [abs_of_neg h, max_eq_right h.le, mul_zero, zero_add]
    have := key_ineq κ hκ x
    have h3 : |x| ^ κ * -Real.log |x| * κ ≤ 1 := by nlinarith
    rw [le_div_iff₀ hκ]; exact h3

lemma arith_of (ν : Measure ℝ) (l : ℝ) (hl : 0 < l)
    (h : ∀ᵐ x ∂ν, x ≠ 0 → Real.log |x| ∈ Set.range (fun n : ℤ => (n : ℝ) * l)) :
    IsArithmetic ((ν[|{x : ℝ | x ≠ 0}]).map (fun x => Real.log |x|)) := by
  refine ⟨l, hl, ?_⟩
  have hR : MeasurableSet (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ :=
    (Set.countable_range _).measurableSet.compl
  have hS : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton (0:ℝ)).compl
  rw [Measure.map_apply meas_logabs hR, ProbabilityTheory.cond_apply hS]
  have : ν ({x : ℝ | x ≠ 0} ∩ (fun x => Real.log |x|) ⁻¹' (Set.range (fun n : ℤ => (n : ℝ) * l))ᶜ)
      = 0 := by
    rw [ae_iff] at h
    refine measure_mono_null (fun x hx => ?_) h
    exact fun h' => hx.2 (h' hx.1)
  rw [this, mul_zero]

lemma sqrt_ineq (κ : ℝ) (x : ℝ) : |x| ^ (κ / 2) ≤ (1 + |x| ^ κ) / 2 := by
  have hs : |x| ^ κ = (|x| ^ (κ / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]; norm_num
  rw [hs]; nlinarith [sq_nonneg (|x| ^ (κ / 2) - 1)]

lemma sqrt_ineq_strict (κ : ℝ) (x : ℝ) (h : |x| ^ κ ≠ 1) : |x| ^ (κ / 2) < (1 + |x| ^ κ) / 2 := by
  have hs : |x| ^ κ = (|x| ^ (κ / 2)) ^ 2 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg x)]; norm_num
  have hne : |x| ^ (κ / 2) - 1 ≠ 0 := by
    intro h0; apply h; rw [hs, show |x| ^ (κ / 2) = 1 by linarith]; norm_num
  rw [hs]; nlinarith [sq_pos_of_ne_zero hne]

variable (κ : ℝ) (ν : Measure ℝ) [IsProbabilityMeasure ν]

lemma not_ae_one (hC : CramerConditions κ ν) : ¬ ∀ᵐ x ∂ν, |x| ^ κ = 1 := by
  intro h
  apply hC.nonarithmetic
  apply arith_of ν 1 one_pos
  filter_upwards [h] with x hx hx0
  have h2 := congrArg Real.log hx
  rw [Real.log_rpow (abs_pos.2 hx0), Real.log_one] at h2
  have : Real.log |x| = 0 := (mul_eq_zero.1 h2).resolve_left hC.pos.ne'
  exact ⟨0, by simp [this]⟩

lemma integrable_rpow_abs (hC : CramerConditions κ ν) : Integrable (fun x => |x| ^ κ) ν := by
  refine ⟨(meas_rpow_abs κ).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ x : ℝ, ‖|x| ^ κ‖ₑ = ENNReal.ofReal (|x| ^ κ) := fun x => by
    rw [Real.enorm_eq_ofReal (Real.rpow_nonneg (abs_nonneg x) κ)]
  simp only [this, hC.moment_eq_one]
  exact ENNReal.one_lt_top

lemma integral_rpow_abs (hC : CramerConditions κ ν) : ∫ x, |x| ^ κ ∂ν = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun x =>
    Real.rpow_nonneg (abs_nonneg x) κ) (meas_rpow_abs κ).aestronglyMeasurable, hC.moment_eq_one,
    ENNReal.toReal_one]

lemma lintegral_abs_phi_lt (hC : CramerConditions κ ν) :
    ∫⁻ x, ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) ∂ν < ∞ := by
  calc ∫⁻ x, ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) ∂ν
      ≤ ∫⁻ x, (ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) + ENNReal.ofReal (1 / κ)) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_add (by
          have := Real.rpow_nonneg (abs_nonneg x) κ; positivity) (by have := hC.pos; positivity)]
        exact ENNReal.ofReal_le_ofReal (abs_phi_le κ hC.pos x)
    _ = ∫⁻ x, ENNReal.ofReal (|x| ^ κ * max (Real.log |x|) 0) ∂ν + ENNReal.ofReal (1 / κ) := by
        rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hC.moment_log_finite, ENNReal.ofReal_lt_top⟩

lemma integrable_phi (hC : CramerConditions κ ν) :
    Integrable (fun x => |x| ^ κ * Real.log |x|) ν := by
  refine ⟨((meas_rpow_abs κ).mul meas_logabs).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have : ∀ x : ℝ, ‖|x| ^ κ * Real.log |x|‖ₑ = ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) κ)]
  simp only [this]
  exact lintegral_abs_phi_lt κ ν hC

/-- Lemma 2.2: `m = E|M|^κ log|M| > 0`. -/
lemma cramerMean_pos (hC : CramerConditions κ ν) : 0 < cramerMean κ ν := by
  have hκ := hC.pos
  set ψ : ℝ → ℝ := fun x => κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ + 1 with hψ
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => by have := key_ineq κ hκ x; simp only [hψ]; linarith
  have hψi : Integrable ψ ν :=
    (((integrable_phi κ ν hC).const_mul κ).sub (integrable_rpow_abs κ ν hC)).add
      (integrable_const 1)
  have hψint : ∫ x, ψ x ∂ν = κ * cramerMean κ ν := by
    have ha : Integrable (fun x => κ * (|x| ^ κ * Real.log |x|)) ν :=
      (integrable_phi κ ν hC).const_mul κ
    have hb : Integrable (fun x => κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ν :=
      ha.sub (integrable_rpow_abs κ ν hC)
    have e1 : ∫ x, ψ x ∂ν = ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ∂ν + ∫ _x, (1:ℝ) ∂ν :=
      integral_add (f := fun x => κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) (g := fun _ => (1:ℝ))
        hb (integrable_const 1)
    have e2 : ∫ x, (κ * (|x| ^ κ * Real.log |x|) - |x| ^ κ) ∂ν =
        ∫ x, κ * (|x| ^ κ * Real.log |x|) ∂ν - ∫ x, |x| ^ κ ∂ν :=
      integral_sub (f := fun x => κ * (|x| ^ κ * Real.log |x|)) (g := fun x => |x| ^ κ)
        ha (integrable_rpow_abs κ ν hC)
    rw [e1, e2, integral_const_mul, integral_rpow_abs κ ν hC, integral_const]
    simp [cramerMean]
  by_contra hle
  push_neg at hle
  have hz : ∫ x, ψ x ∂ν = 0 :=
    le_antisymm (by rw [hψint]; nlinarith) (integral_nonneg hψ0)
  have hae := (integral_eq_zero_iff_of_nonneg hψ0 hψi).1 hz
  apply not_ae_one κ ν hC
  filter_upwards [hae] with x hx
  by_contra hne
  have := key_ineq_strict κ hκ x hne
  have : ψ x = 0 := hx
  simp only [hψ] at this
  linarith

variable (hν0 : ν (Set.Iio 0) = 0)
include hν0

lemma eta_prob (hC : CramerConditions κ ν) : IsProbabilityMeasure (tiltOn κ ν (Set.Ioi 0)) := by
  constructor
  rw [← lintegral_one, lintegral_eta κ hC.pos ν hν0 _ measurable_const]
  simp only [mul_one]
  exact hC.moment_eq_one

lemma eta_integrable (hC : CramerConditions κ ν) :
    Integrable (fun y => y) (tiltOn κ ν (Set.Ioi 0)) := by
  refine ⟨measurable_id.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  simp only [Real.enorm_eq_ofReal_abs]
  rw [lintegral_eta κ hC.pos ν hν0 (fun y => ENNReal.ofReal |y|)
    (ENNReal.measurable_ofReal.comp continuous_abs.measurable)]
  have : ∀ x : ℝ, ENNReal.ofReal (|x| ^ κ) * ENNReal.ofReal (abs (Real.log |x|)) =
      ENNReal.ofReal (|x| ^ κ * abs (Real.log |x|)) := fun x => by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ)]
  simp only [this]
  exact lintegral_abs_phi_lt κ ν hC

lemma eta_mean (hC : CramerConditions κ ν) :
    ∫ y, y ∂(tiltOn κ ν (Set.Ioi 0)) = cramerMean κ ν := by
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part (eta_integrable κ ν hν0 hC),
    cramerMean, integral_eq_lintegral_pos_part_sub_lintegral_neg_part (integrable_phi κ ν hC),
    lintegral_eta κ hC.pos ν hν0 (fun y => ENNReal.ofReal y) ENNReal.measurable_ofReal,
    lintegral_eta κ hC.pos ν hν0 (fun y => ENNReal.ofReal (-y))
      (ENNReal.measurable_ofReal.comp measurable_neg)]
  have h1 : ∀ x : ℝ, ENNReal.ofReal (|x| ^ κ) * ENNReal.ofReal (Real.log |x|) =
      ENNReal.ofReal (|x| ^ κ * Real.log |x|) := fun x => by
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ)]
  have h2 : ∀ x : ℝ, ENNReal.ofReal (|x| ^ κ) * ENNReal.ofReal (-Real.log |x|) =
      ENNReal.ofReal (-(|x| ^ κ * Real.log |x|)) := fun x => by
    rw [← mul_neg, ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ)]
  simp only [h1, h2]

lemma eta_expMom (hC : CramerConditions κ ν) : expMom (κ / 2) (tiltOn κ ν (Set.Ioi 0)) < 1 := by
  have hκ := hC.pos
  unfold expMom
  rw [lintegral_eta κ hκ ν hν0 _ (by fun_prop)]
  have hpt : ∀ x : ℝ, ENNReal.ofReal (|x| ^ κ) * ENNReal.ofReal (Real.exp (-(κ / 2 * Real.log |x|)))
      = ENNReal.ofReal (|x| ^ (κ / 2)) := by
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp [Real.zero_rpow hκ.ne', Real.zero_rpow (by positivity : κ / 2 ≠ 0)]
    · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ), ← exp_kappa_log_abs κ x hx,
        ← exp_kappa_log_abs (κ / 2) x hx, ← Real.exp_add]
      congr 2; ring
  simp only [hpt]
  have hint2 : Integrable (fun x => |x| ^ (κ / 2)) ν := by
    refine Integrable.mono' (((integrable_const 1).add (integrable_rpow_abs κ ν hC)).div_const 2)
      ((meas_rpow_abs _).aestronglyMeasurable) (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _)]
    exact sqrt_ineq κ x
  rw [← ofReal_integral_eq_lintegral_ofReal hint2
    (Eventually.of_forall fun x => Real.rpow_nonneg (abs_nonneg x) _)]
  rw [ENNReal.ofReal_lt_one]
  set ψ : ℝ → ℝ := fun x => (1 + |x| ^ κ) / 2 - |x| ^ (κ / 2) with hψ
  have hψ0 : ∀ x, 0 ≤ ψ x := fun x => by have := sqrt_ineq κ x; simp only [hψ]; linarith
  have hψi : Integrable ψ ν :=
    (((integrable_const 1).add (integrable_rpow_abs κ ν hC)).div_const 2).sub hint2
  have hψint : ∫ x, ψ x ∂ν = 1 - ∫ x, |x| ^ (κ / 2) ∂ν := by
    have ha : Integrable (fun x => (1 + |x| ^ κ) / 2) ν :=
      ((integrable_const 1).add (integrable_rpow_abs κ ν hC)).div_const 2
    have e1 : ∫ x, ψ x ∂ν = ∫ x, (1 + |x| ^ κ) / 2 ∂ν - ∫ x, |x| ^ (κ / 2) ∂ν :=
      integral_sub (f := fun x => (1 + |x| ^ κ) / 2) (g := fun x => |x| ^ (κ / 2)) ha hint2
    have e2 : ∫ x, (1 + |x| ^ κ) ∂ν = ∫ _x, (1:ℝ) ∂ν + ∫ x, |x| ^ κ ∂ν :=
      integral_add (f := fun _ => (1:ℝ)) (g := fun x => |x| ^ κ) (integrable_const 1)
        (integrable_rpow_abs κ ν hC)
    rw [e1, integral_div, e2, integral_rpow_abs κ ν hC, integral_const]
    simp
  by_contra hle
  push_neg at hle
  have hz : ∫ x, ψ x ∂ν = 0 := le_antisymm (by rw [hψint]; linarith) (integral_nonneg hψ0)
  have hae := (integral_eq_zero_iff_of_nonneg hψ0 hψi).1 hz
  apply not_ae_one κ ν hC
  filter_upwards [hae] with x hx
  by_contra hne
  have := sqrt_ineq_strict κ x hne
  have : ψ x = 0 := hx
  simp only [hψ] at this
  linarith

lemma eta_aF_pos (hC : CramerConditions κ ν) (θ : ℝ) (hθ : 0 < θ) :
    0 < aF (tiltOn κ ν (Set.Ioi 0)) θ := by
  have hκ := hC.pos
  haveI := eta_prob κ ν hν0 hC
  set η := tiltOn κ ν (Set.Ioi 0) with hη
  have hint : Integrable (fun y => 1 - Real.cos (θ * y)) η :=
    integrable_bdd_cont η _ (by fun_prop) 2 (fun y => by
      have := Real.cos_le_one (θ * y); have := Real.neg_one_le_cos (θ * y)
      rw [abs_le]; constructor <;> linarith)
  have hnn : ∀ y, 0 ≤ 1 - Real.cos (θ * y) := fun y => by
    have := Real.cos_le_one (θ * y); linarith
  by_contra hle
  push_neg at hle
  have h0 : aF η θ = 0 := le_antisymm hle (aF_nonneg η θ)
  have hae := (integral_eq_zero_iff_of_nonneg hnn hint).1 h0
  set l : ℝ := 2 * π / θ with hl
  have hlpos : 0 < l := by positivity
  set R : Set ℝ := Set.range (fun n : ℤ => (n : ℝ) * l) with hR
  have hRm : MeasurableSet Rᶜ := (Set.countable_range _).measurableSet.compl
  have hηR : η Rᶜ = 0 := by
    rw [Filter.EventuallyEq, ae_iff] at hae
    refine measure_mono_null (fun y hy => ?_) hae
    intro h1
    apply hy
    have hc : Real.cos (θ * y) = 1 := by
      have : 1 - Real.cos (θ * y) = 0 := h1
      linarith
    obtain ⟨n, hn⟩ := (Real.cos_eq_one_iff _).1 hc
    refine ⟨n, ?_⟩
    rw [hl]; field_simp; linarith
  rw [← lintegral_indicator_one hRm, hη, lintegral_eta κ hκ ν hν0 (Rᶜ.indicator 1)
    (measurable_one.indicator hRm)] at hηR
  have hae2 := (lintegral_eq_zero_iff (by
    exact ENNReal.measurable_ofReal.comp (meas_rpow_abs κ) |>.mul
      ((measurable_one.indicator hRm).comp meas_logabs))).1 hηR
  apply hC.nonarithmetic
  apply arith_of ν l hlpos
  filter_upwards [hae2] with x hx hx0
  by_contra hnot
  have hpos : ENNReal.ofReal (|x| ^ κ) ≠ 0 :=
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (abs_pos.2 hx0) κ)).ne'
  have : Set.indicator Rᶜ (1 : ℝ → ℝ≥0∞) (Real.log |x|) = 1 :=
    Set.indicator_of_mem (show Real.log |x| ∈ Rᶜ from hnot) _
  simp only [Pi.zero_apply] at hx
  rw [this, mul_one] at hx
  exact hpos hx

end GoldieRenewal.Implicit.KRT

/-! ## C8: the renewal equation `r = g₁ + r ∗ η`, its smoothed solution `ř = ∫ g₁(w) H(t - w) dw` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit ProbabilityTheory
open scoped ENNReal

/-- `F ⊛ ρ (t) = ∫⁻ F(t - y) ρ(dy)` -/
noncomputable def cv (F : ℝ → ℝ≥0∞) (ρ : Measure ℝ) (t : ℝ) : ℝ≥0∞ := ∫⁻ y, F (t - y) ∂ρ

lemma cv_meas (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ : Measure ℝ) [SFinite ρ] :
    Measurable (cv F ρ) := by
  unfold cv
  exact (hF.comp (measurable_fst.sub measurable_snd)).lintegral_prod_right'

lemma cv_conv (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ σ : Measure ℝ) [SFinite ρ] [SFinite σ] :
    cv F (ρ ∗ σ) = cv (cv F σ) ρ := by
  funext t
  unfold cv
  rw [Measure.lintegral_conv (f := fun z => F (t - z))
    (hF.comp (measurable_const.sub measurable_id))]
  refine lintegral_congr (fun x => lintegral_congr (fun y => ?_))
  congr 1; ring

lemma cv_dirac (F : ℝ → ℝ≥0∞) : cv F (Measure.dirac 0) = F := by
  funext t; unfold cv; rw [lintegral_dirac]; simp

lemma cv_zero (F : ℝ → ℝ≥0∞) : cv F 0 = 0 := by
  funext t; unfold cv; simp

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `e^{κs} P(e^s < R)` in `[0,∞]` -/
noncomputable def Fp (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.exp (κ * s)) * P {ω | Real.exp s < R ω}

lemma tail_anti (P : Measure Ω) (R : Ω → ℝ) : Antitone (fun s => P {ω | Real.exp s < R ω}) := by
  intro a b hab
  apply measure_mono
  intro ω hω
  exact lt_of_le_of_lt (Real.exp_le_exp.mpr hab) hω

lemma Fp_meas (P : Measure Ω) (R : Ω → ℝ) (κ : ℝ) : Measurable (Fp P R κ) := by
  unfold Fp
  exact (meas_expden κ).mul (tail_anti P R).measurable

lemma set_pos (t x : ℝ) (hx : 0 < x) (R : Ω → ℝ) :
    {ω | Real.exp t < x * R ω} = {ω | Real.exp (t - Real.log |x|) < R ω} := by
  rw [abs_of_pos hx, Real.exp_sub, Real.exp_log hx]
  ext ω
  change Real.exp t < x * R ω ↔ Real.exp t / x < R ω
  rw [div_lt_iff₀' hx]

lemma set_neg (t x : ℝ) (hx : x < 0) (R : Ω → ℝ) :
    {ω | Real.exp t < x * R ω} = {ω | Real.exp (t - Real.log |x|) < -R ω} := by
  rw [abs_of_neg hx, Real.exp_sub, Real.exp_log (neg_pos.mpr hx)]
  ext ω
  change Real.exp t < x * R ω ↔ Real.exp t / -x < -R ω
  rw [div_lt_iff₀ (neg_pos.mpr hx)]
  constructor <;> intro h <;> nlinarith

lemma ofReal_exp_split (κ t y : ℝ) :
    ENNReal.ofReal (Real.exp (κ * t)) =
      ENNReal.ofReal (Real.exp (κ * y)) * ENNReal.ofReal (Real.exp (κ * (t - y))) := by
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  congr 2; ring

/-- `e^{κt} P(MR > e^t) = (r₊ ⊛ A)(t) + (r₋ ⊛ B)(t)` for `R` independent of `M`. -/
lemma tail_prod_eq (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hind : IndepFun R M P) (t : ℝ) :
    ENNReal.ofReal (Real.exp (κ * t)) * P {ω | Real.exp t < M ω * R ω} =
      cv (Fp P R κ) (tiltOn κ (P.map M) (Set.Ioi 0)) t +
        cv (Fp P (fun ω => -R ω) κ) (tiltOn κ (P.map M) (Set.Iio 0)) t := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hR.aemeasurable hM.aemeasurable).mp hind
  set S : Set (ℝ × ℝ) := {p | Real.exp t < p.2 * p.1} with hSdef
  have hS : MeasurableSet S := measurableSet_lt measurable_const (measurable_snd.mul measurable_fst)
  have h1 : P {ω | Real.exp t < M ω * R ω} = ((P.map R).prod (P.map M)) S := by
    rw [← hmap, Measure.map_apply (hR.prodMk hM) hS]; rfl
  have hpre : ∀ x : ℝ, (P.map R) ((fun r => (r, x)) ⁻¹' S) = P {ω | Real.exp t < x * R ω} := by
    intro x
    rw [Measure.map_apply hR]
    · rfl
    · exact measurableSet_lt measurable_const (measurable_const.mul measurable_id)
  rw [h1, Measure.prod_apply_symm hS]
  simp only [hpre]
  unfold cv
  rw [lintegral_tiltOn _ _ _ (fun y => Fp P R κ (t - y))
      ((Fp_meas P R κ).comp (measurable_const.sub measurable_id)),
    lintegral_tiltOn _ _ _ (fun y => Fp P (fun ω => -R ω) κ (t - y))
      ((Fp_meas P _ κ).comp (measurable_const.sub measurable_id)),
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, ← setLIntegral_univ]
  have hu : (Set.univ : Set ℝ) = (Set.Ioi 0 ∪ Set.Iio 0) ∪ {0} := by
    ext x
    simp only [Set.mem_univ, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, Set.mem_singleton_iff,
      true_iff]
    rcases lt_trichotomy x 0 with h | h | h
    · exact Or.inl (Or.inr h)
    · exact Or.inr h
    · exact Or.inl (Or.inl h)
  have hd1 : Disjoint (Set.Ioi (0:ℝ) ∪ Set.Iio 0) {0} := by
    rw [Set.disjoint_singleton_right]
    simp
  have hd2 : Disjoint (Set.Ioi (0:ℝ)) (Set.Iio 0) := by
    rw [Set.disjoint_left]
    intro x h1 h2
    exact lt_asymm (Set.mem_Ioi.mp h1) (Set.mem_Iio.mp h2)
  rw [hu, lintegral_union (measurableSet_singleton 0) hd1,
    lintegral_union measurableSet_Iio hd2, lintegral_singleton]
  have h0 : {ω | Real.exp t < (0:ℝ) * R ω} = ∅ := by
    ext ω
    simp only [zero_mul, Set.mem_empty_iff_false, iff_false]
    exact fun h => absurd h (not_lt.mpr (Real.exp_pos t).le)
  rw [h0, measure_empty, mul_zero, zero_mul, add_zero]
  congr 1
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp only [Function.comp, Fp]
    rw [set_pos t x hx R, ← mul_assoc, ← ofReal_exp_split]
  · refine setLIntegral_congr_fun measurableSet_Iio (fun x hx => ?_)
    simp only [Function.comp, Fp]
    rw [set_neg t x hx R, ← mul_assoc, ← ofReal_exp_split]

lemma tiltOn_Iio_zero (κ : ℝ) (ν : Measure ℝ) (hν0 : ν (Set.Iio 0) = 0) :
    tiltOn κ ν (Set.Iio 0) = 0 := by
  unfold tiltOn
  rw [Measure.restrict_eq_zero.2 hν0, Measure.map_zero, withDensity_zero_left]

/-- for `M ≥ 0`: `e^{κt} P(MR > e^t) = (r ⊛ η)(t)` (Goldie (9.6)-(9.8), Case 1). -/
lemma tail_eq (P : Measure Ω) [IsProbabilityMeasure P] (M R : Ω → ℝ) (hM : Measurable M)
    (hR : Measurable R) (κ : ℝ) (hind : IndepFun R M P) (hν0 : (P.map M) (Set.Iio 0) = 0)
    (t : ℝ) :
    ENNReal.ofReal (Real.exp (κ * t)) * P {ω | Real.exp t < M ω * R ω} =
      cv (Fp P R κ) (tiltOn κ (P.map M) (Set.Ioi 0)) t := by
  rw [tail_prod_eq P M R hM hR κ hind t, tiltOn_Iio_zero κ _ hν0, cv_zero, Pi.zero_apply,
    add_zero]

/-! ### the iterated renewal equation and its smoothing -/

/-- smoothing in `[0,∞]`: `Sm F t = ∫ k(t - u) F(u) du`. -/
noncomputable def Sm (F : ℝ → ℝ≥0∞) (t : ℝ) : ℝ≥0∞ := ∫⁻ u, kE (t - u) * F u

lemma kE_ne_top (y : ℝ) : kE y ≠ ∞ := by
  rcases lt_or_ge y 0 with h | h
  · rw [kE_of_neg h]; exact ENNReal.zero_ne_top
  · rw [kE_of_nonneg h]; exact ENNReal.ofReal_ne_top

lemma meas_kE_sub (t : ℝ) : Measurable (fun u => kE (t - u)) :=
  measurable_kE.comp (measurable_const.sub measurable_id)

lemma Sm_add (F G : ℝ → ℝ≥0∞) (hF : Measurable F) (t : ℝ) :
    Sm (fun u => F u + G u) t = Sm F t + Sm G t := by
  unfold Sm
  simp only [mul_add]
  exact lintegral_add_left ((meas_kE_sub t).mul hF) _

lemma Sm_sum (Fs : ℕ → ℝ → ℝ≥0∞) (h : ∀ k, Measurable (Fs k)) (n : ℕ) (t : ℝ) :
    Sm (fun u => ∑ k ∈ Finset.range n, Fs k u) t = ∑ k ∈ Finset.range n, Sm (Fs k) t := by
  unfold Sm
  simp only [Finset.mul_sum]
  exact lintegral_finset_sum _ (fun k _ => (meas_kE_sub t).mul (h k))

lemma Sm_cv (F : ℝ → ℝ≥0∞) (hF : Measurable F) (ρ : Measure ℝ) [SFinite ρ] (t : ℝ) :
    Sm (cv F ρ) t = ∫⁻ x, (∫⁻ w, F w * kE (t - x - w)) ∂ρ := by
  unfold Sm cv
  have hmeas : Measurable (Function.uncurry fun (u y : ℝ) => kE (t - u) * F (u - y)) := by
    simp only [Function.uncurry_def]
    exact (measurable_kE.comp (measurable_const.sub measurable_fst)).mul
      (hF.comp (measurable_fst.sub measurable_snd))
  calc ∫⁻ u, kE (t - u) * ∫⁻ y, F (u - y) ∂ρ = ∫⁻ u, ∫⁻ y, kE (t - u) * F (u - y) ∂ρ := by
        refine lintegral_congr fun u => ?_
        have hFu : Measurable (fun y => F (u - y)) := hF.comp (measurable_const.sub measurable_id)
        rw [lintegral_const_mul _ hFu]
    _ = ∫⁻ y, (∫⁻ u, kE (t - u) * F (u - y)) ∂ρ := lintegral_lintegral_swap hmeas.aemeasurable
    _ = ∫⁻ x, (∫⁻ w, F w * kE (t - x - w)) ∂ρ := by
        refine lintegral_congr fun y => ?_
        have := lintegral_add_right_eq_self (μ := volume) (fun u => kE (t - u) * F (u - y)) y
        rw [← this]
        refine lintegral_congr fun w => ?_
        rw [mul_comm, show w + y - y = w by ring, show t - (w + y) = t - y - w by ring]

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma convPow_sf (k : ℕ) : SFinite (convPow η k) := by
  have := convPow_isProb η k; infer_instance

lemma tsum_Sm_cv (F : ℝ → ℝ≥0∞) (hF : Measurable F) (t : ℝ) :
    ∑' k, Sm (cv F (convPow η k)) t = ∫⁻ w, F w * Hk η (t - w) := by
  have h : ∀ k, Sm (cv F (convPow η k)) t =
      ∫⁻ x, (∫⁻ w, F w * kE (t - x - w)) ∂(convPow η k) := fun k => by
    have := convPow_sf η k; exact Sm_cv F hF _ t
  simp only [h]
  rw [← lintegral_sum_measure, ← renewalMeasure, swapK η kE measurable_kE F hF t]
  rfl

section RhoN

variable (κ l : ℝ) (F : ℝ → ℝ≥0∞)

/-- `ρ_n(u) = ∫ ρ(u - y) η^{*n}(dy) ≤ e^{κu} Λ_κ^n` for `ρ(s) = e^{κs} F(s)`, `F ≤ 1`. -/
lemma rho_bound (hF1 : ∀ s, F s ≤ 1) (n : ℕ) (u : ℝ) :
    cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) (convPow η n) u ≤
      ENNReal.ofReal (Real.exp (κ * u)) * expMom κ η ^ n := by
  unfold cv
  rw [← expMom_convPow η κ n, expMom, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun y => ?_
  calc ENNReal.ofReal (Real.exp (κ * (u - y))) * F (u - y)
      ≤ ENNReal.ofReal (Real.exp (κ * (u - y))) * 1 := by gcongr; exact hF1 _
    _ = ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp (-(κ * y))) := by
        rw [mul_one, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
        congr 2; ring

lemma rho_split (hF1 : ∀ s, F s ≤ 1) (hFa : Antitone F) (hlk : l ≤ κ) (n : ℕ) (u K : ℝ) :
    cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) (convPow η n) u ≤
      ENNReal.ofReal (Real.exp (κ * u)) * F (u + K) * expMom κ η ^ n +
        ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp ((κ - l) * K)) *
          expMom l η ^ n := by
  rw [← expMom_convPow η κ n, ← expMom_convPow η l n]
  unfold cv expMom
  set A := ENNReal.ofReal (Real.exp (κ * u)) * F (u + K) with hA
  set B := ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp ((κ - l) * K)) with hB
  calc ∫⁻ y, (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) (u - y) ∂(convPow η n)
      ≤ ∫⁻ y, (A * ENNReal.ofReal (Real.exp (-(κ * y))) +
          B * ENNReal.ofReal (Real.exp (-(l * y)))) ∂(convPow η n) := by
        refine lintegral_mono fun y => ?_
        beta_reduce
        have hsplit : ENNReal.ofReal (Real.exp (κ * (u - y))) =
            ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp (-(κ * y))) := by
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]; congr 2; ring
        rcases lt_or_ge y (-K) with hy | hy
        · refine le_trans ?_ le_self_add
          rw [hsplit, hA]
          calc ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp (-(κ * y))) * F (u - y)
              ≤ ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp (-(κ * y))) *
                  F (u + K) := by gcongr; exact hFa (by linarith)
            _ = _ := by ring
        · refine le_trans ?_ le_add_self
          have hreal : Real.exp (κ * (u - y)) ≤
              Real.exp (κ * u) * Real.exp ((κ - l) * K) * Real.exp (-(l * y)) := by
            rw [← Real.exp_add, ← Real.exp_add]
            apply Real.exp_le_exp.2
            nlinarith [mul_nonneg (sub_nonneg.2 hlk) (show 0 ≤ K + y by linarith)]
          calc ENNReal.ofReal (Real.exp (κ * (u - y))) * F (u - y)
              ≤ ENNReal.ofReal (Real.exp (κ * (u - y))) := mul_le_of_le_one_right zero_le (hF1 _)
            _ ≤ ENNReal.ofReal (Real.exp (κ * u) * Real.exp ((κ - l) * K) * Real.exp (-(l * y))) :=
                ENNReal.ofReal_le_ofReal hreal
            _ = B * ENNReal.ofReal (Real.exp (-(l * y))) := by
                rw [hB, ENNReal.ofReal_mul (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le),
                  ENNReal.ofReal_mul (Real.exp_pos _).le]
    _ = A * ∫⁻ y, ENNReal.ofReal (Real.exp (-(κ * y))) ∂(convPow η n) +
          B * ∫⁻ y, ENNReal.ofReal (Real.exp (-(l * y))) ∂(convPow η n) := by
        rw [lintegral_add_left ((measurable_expden κ).const_mul A),
          lintegral_const_mul _ (measurable_expden κ), lintegral_const_mul _ (measurable_expden l)]

lemma rho_tendsto (hF1 : ∀ s, F s ≤ 1) (hFa : Antitone F) (hF0 : Tendsto F atTop (𝓝 0))
    (hl : 0 < l) (hlk : l ≤ κ) (hκ1 : expMom κ η ≤ 1) (hr : expMom l η < 1) (u : ℝ) :
    Tendsto (fun n => cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) (convPow η n) u)
      atTop (𝓝 0) := by
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  have hA : Tendsto (fun K => ENNReal.ofReal (Real.exp (κ * u)) * F (u + K)) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (hF0.comp (tendsto_atTop_add_const_left atTop u tendsto_id))
      (Or.inr ENNReal.ofReal_ne_top) (a := ENNReal.ofReal (Real.exp (κ * u)))
    simpa [Function.comp_def] using this
  obtain ⟨K, hK, -⟩ := (((ENNReal.tendsto_nhds_zero.1 hA) (ε / 2)
    (ENNReal.half_pos hε.ne')).and (eventually_ge_atTop (0:ℝ))).exists
  have hB : Tendsto (fun n : ℕ => ENNReal.ofReal (Real.exp (κ * u)) *
      ENNReal.ofReal (Real.exp ((κ - l) * K)) * expMom l η ^ n) atTop (𝓝 0) := by
    have := ENNReal.Tendsto.const_mul (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hr)
      (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top))
      (a := ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp ((κ - l) * K)))
    simpa using this
  filter_upwards [(ENNReal.tendsto_nhds_zero.1 hB) (ε / 2) (ENNReal.half_pos hε.ne')] with n hn
  calc _ ≤ ENNReal.ofReal (Real.exp (κ * u)) * F (u + K) * expMom κ η ^ n +
        ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp ((κ - l) * K)) *
          expMom l η ^ n := rho_split η κ l F hF1 hFa hlk n u K
    _ ≤ ENNReal.ofReal (Real.exp (κ * u)) * F (u + K) * 1 +
        ENNReal.ofReal (Real.exp (κ * u)) * ENNReal.ofReal (Real.exp ((κ - l) * K)) *
          expMom l η ^ n := by gcongr; exact pow_le_one₀ zero_le hκ1
    _ ≤ ε / 2 + ε / 2 := by rw [mul_one]; exact add_le_add hK hn
    _ = ε := ENNReal.add_halves ε

lemma Sm_rho_tendsto (hκ : 0 < κ) (hF1 : ∀ s, F s ≤ 1) (hFa : Antitone F)
    (hF0 : Tendsto F atTop (𝓝 0)) (hFm : Measurable F)
    (hl : 0 < l) (hlk : l ≤ κ) (hκ1 : expMom κ η ≤ 1) (hr : expMom l η < 1) (t : ℝ) :
    Tendsto (fun n => Sm (cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s)
      (convPow η n)) t) atTop (𝓝 0) := by
  have hρm : Measurable (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) :=
    (meas_expden κ).mul hFm
  have h := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun n u => kE (t - u) * cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s)
      (convPow η n) u) (f := fun _ => 0)
    (fun u => ENNReal.ofReal (Real.exp (κ * t)) * kE (t - u))
    (fun n => by
      have := convPow_sf η n
      exact (meas_kE_sub t).mul (cv_meas _ hρm _))
    (fun n => Eventually.of_forall fun u => by
      have hb := (rho_bound η κ F hF1 n u).trans
        (mul_le_of_le_one_right zero_le (pow_le_one₀ zero_le hκ1))
      rcases lt_or_ge (t - u) 0 with h0 | h0
      · simp [kE_of_neg h0]
      · calc kE (t - u) * cv _ (convPow η n) u ≤ kE (t - u) * ENNReal.ofReal (Real.exp (κ * u)) := by
              gcongr
          _ ≤ kE (t - u) * ENNReal.ofReal (Real.exp (κ * t)) := by
              gcongr
              linarith
          _ = _ := mul_comm _ _)
    (by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_sub_left_eq_self kE t,
        lintegral_kE, mul_one]
      exact ENNReal.ofReal_ne_top)
    (Eventually.of_forall fun u => by
      have := ENNReal.Tendsto.const_mul (rho_tendsto η κ l F hF1 hFa hF0 hl hlk hκ1 hr u)
        (Or.inr (kE_ne_top (t - u))) (a := kE (t - u))
      simpa using this)
  simpa [Sm] using h

end RhoN

/-- **C8**: the smoothed solution of the renewal equation `ρ + G₋ = G₊ + ρ ⊛ η`. -/
lemma renewal_solution (κ l : ℝ) (F Gp Gm : ℝ → ℝ≥0∞) (hκ : 0 < κ) (hF1 : ∀ s, F s ≤ 1)
    (hFa : Antitone F) (hF0 : Tendsto F atTop (𝓝 0)) (hFm : Measurable F)
    (hGp : Measurable Gp) (hGm : Measurable Gm)
    (hl : 0 < l) (hlk : l ≤ κ) (hκ1 : expMom κ η ≤ 1) (hr : expMom l η < 1)
    (hE : ∀ s, ENNReal.ofReal (Real.exp (κ * s)) * F s + Gm s =
      Gp s + cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) η s) (t : ℝ) :
    Sm (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) t + ∫⁻ w, Gm w * Hk η (t - w) =
      ∫⁻ w, Gp w * Hk η (t - w) := by
  set ρ : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s with hρ
  have hρm : Measurable ρ := (meas_expden κ).mul hFm
  -- one step
  have hE1 : ∀ k s, cv ρ (convPow η k) s + cv Gm (convPow η k) s =
      cv Gp (convPow η k) s + cv ρ (convPow η (k + 1)) s := by
    intro k s
    have := convPow_sf η k
    have hc : cv ρ (convPow η (k + 1)) = cv (cv ρ η) (convPow η k) := by
      simp only [convPow]
      rw [Measure.conv_comm, cv_conv ρ hρm]
    rw [hc]
    unfold cv
    have h1m : Measurable (fun y => ρ (s - y)) := hρm.comp (measurable_const.sub measurable_id)
    have h2m : Measurable (fun y => Gp (s - y)) := hGp.comp (measurable_const.sub measurable_id)
    rw [← lintegral_add_left h1m, ← lintegral_add_left h2m]
    exact lintegral_congr fun y => hE (s - y)
  -- iterate
  have hS : ∀ n s, ρ s + ∑ k ∈ Finset.range n, cv Gm (convPow η k) s =
      ∑ k ∈ Finset.range n, cv Gp (convPow η k) s + cv ρ (convPow η n) s := by
    intro n s
    induction n with
    | zero => simp [convPow, cv_dirac]
    | succ n ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ← add_assoc, ih, add_assoc, hE1 n s,
        ← add_assoc]
  have hmeasC : ∀ (G : ℝ → ℝ≥0∞), Measurable G → ∀ k, Measurable (cv G (convPow η k)) :=
    fun G hG k => by have := convPow_sf η k; exact cv_meas G hG _
  -- smooth
  have hSm : ∀ n, Sm ρ t + ∑ k ∈ Finset.range n, Sm (cv Gm (convPow η k)) t =
      ∑ k ∈ Finset.range n, Sm (cv Gp (convPow η k)) t + Sm (cv ρ (convPow η n)) t := by
    intro n
    have h1 : Sm (fun s => ρ s + ∑ k ∈ Finset.range n, cv Gm (convPow η k) s) t =
        Sm (fun s => ∑ k ∈ Finset.range n, cv Gp (convPow η k) s + cv ρ (convPow η n) s) t :=
      congrArg (fun G => Sm G t) (funext (hS n))
    rw [Sm_add _ _ hρm, Sm_sum _ (hmeasC Gm hGm),
      Sm_add _ _ (Finset.measurable_sum _ fun k _ => hmeasC Gp hGp k),
      Sm_sum _ (hmeasC Gp hGp)] at h1
    exact h1
  have hL : Tendsto (fun n => Sm ρ t + ∑ k ∈ Finset.range n, Sm (cv Gm (convPow η k)) t) atTop
      (𝓝 (Sm ρ t + ∫⁻ w, Gm w * Hk η (t - w))) := by
    rw [← tsum_Sm_cv η Gm hGm t]
    exact tendsto_const_nhds.add (ENNReal.tendsto_nat_tsum _)
  have hR : Tendsto (fun n => ∑ k ∈ Finset.range n, Sm (cv Gp (convPow η k)) t +
      Sm (cv ρ (convPow η n)) t) atTop (𝓝 ((∫⁻ w, Gp w * Hk η (t - w)) + 0)) := by
    rw [← tsum_Sm_cv η Gp hGp t]
    exact (ENNReal.tendsto_nat_tsum _).add
      (Sm_rho_tendsto η κ l F hκ hF1 hFa hF0 hFm hl hlk hκ1 hr t)
  have := tendsto_nhds_unique (hL.congr' (Eventually.of_forall hSm)) hR
  rwa [add_zero] at this

end GoldieRenewal.Implicit.KRT

/-! ## Parent: Goldie (1991) Thm 2.3, Case 1: `ř(t) → (1/m) ∫ ğ₁` -/

namespace GoldieRenewal.Implicit.KRT

open GoldieRenewal.Implicit ProbabilityTheory
open scoped ENNReal

/-- the smoothing kernel `k(s) = 1_{s ≥ 0} e^{-s}` (real version) -/
noncomputable def kern (s : ℝ) : ℝ := Set.indicator (Set.Ici 0) (fun s => Real.exp (-s)) s

lemma kern_integrable : Integrable kern := by
  unfold kern
  rw [integrable_indicator_iff measurableSet_Ici]
  rw [integrableOn_Ici_iff_integrableOn_Ioi]
  simpa using integrableOn_exp_neg_Ioi 0

lemma kern_integral : ∫ s, kern s = 1 := by
  unfold kern
  rw [integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi]
  exact integral_exp_neg_Ioi_zero

lemma smooth_eq_conv (g : ℝ → ℝ) (t : ℝ) :
    smooth g t = (convolution g kern (ContinuousLinearMap.lsmul ℝ ℝ) volume) t := by
  rw [convolution_lsmul, smooth, ← integral_indicator measurableSet_Iic]
  congr 1
  funext u
  by_cases hu : u ≤ t
  · have h0 : (0:ℝ) ≤ t - u := by linarith
    simp [Set.indicator, kern, hu, h0, mul_comm]
  · have h0 : ¬ (0:ℝ) ≤ t - u := by linarith
    simp [Set.indicator, kern, hu, h0]

/-- `∫ ğ = ∫ g` for `g ∈ L¹`. -/
lemma integral_smooth (g : ℝ → ℝ) (hg : Integrable g) : ∫ t, smooth g t = ∫ t, g t := by
  have : (fun t => smooth g t) = (convolution g kern (ContinuousLinearMap.lsmul ℝ ℝ) volume) :=
    funext (smooth_eq_conv g)
  rw [this, integral_convolution _ hg kern_integrable, kern_integral]
  simp

lemma integrableOn_Ioi_iff_exp (h : ℝ → ℝ) :
    IntegrableOn h (Set.Ioi 0) ↔ Integrable (fun u => Real.exp u * h (Real.exp u)) := by
  have himg : Real.exp '' Set.univ = Set.Ioi 0 := by rw [Set.image_univ, Real.range_exp]
  rw [← himg, integrableOn_image_iff_integrableOn_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn,
    integrableOn_univ]
  simp only [smul_eq_mul, abs_of_pos (Real.exp_pos _)]

lemma exp_mul_tailDiffPlus {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ)
    (κ : ℝ) (u : ℝ) :
    Real.exp u * tailDiffPlus P M R κ (Real.exp u) = gOne P M R κ u := by
  unfold tailDiffPlus gOne
  rw [← Real.exp_mul]
  have : Real.exp u * Real.exp (u * (κ - 1)) = Real.exp (κ * u) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [← this]; ring

lemma gOne_integrable {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (M R : Ω → ℝ) (κ : ℝ)
    (h28 : TailCondPlus P M R κ) : Integrable (gOne P M R κ) := by
  have := (integrableOn_Ioi_iff_exp (tailDiffPlus P M R κ)).mp h28
  simpa only [exp_mul_tailDiffPlus] using this

lemma ofReal_split (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ENNReal.ofReal a + ENNReal.ofReal (-(a - b)) = ENNReal.ofReal (a - b) + ENNReal.ofReal b := by
  rcases le_total b a with h | h
  · rw [ENNReal.ofReal_of_nonpos (show -(a - b) ≤ 0 by linarith), add_zero,
      ← ENNReal.ofReal_add (by linarith) hb]
    congr 1; ring
  · rw [ENNReal.ofReal_of_nonpos (show a - b ≤ 0 by linarith), zero_add,
      ← ENNReal.ofReal_add ha (by linarith)]
    congr 1; ring

section Main

variable (η : Measure ℝ) [IsProbabilityMeasure η]

lemma Ap_le (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (G : ℝ → ℝ≥0∞) (hG : Measurable G) (t : ℝ) :
    ∫⁻ w, G w * Hk η (t - w) ≤ (∫⁻ w, G w) * C0 η := by
  rw [← lintegral_mul_const _ hG]
  exact lintegral_mono fun w => by gcongr; exact Hk_le η h1 hμ hpos _

lemma Ap_tendsto (h1 : Integrable (fun x => x) η) (hμ : 0 < ∫ x, x ∂η)
    (hpos : ∀ θ, 0 < θ → 0 < aF η θ) (l : ℝ) (hl : 0 < l) (hr : expMom l η < 1)
    (G : ℝ → ℝ≥0∞) (hG : Measurable G) (hGi : ∫⁻ w, G w ≠ ∞) :
    Tendsto (fun t => ∫⁻ w, G w * Hk η (t - w)) atTop
      (𝓝 ((∫⁻ w, G w) * ENNReal.ofReal (1 / ∫ x, x ∂η))) := by
  rw [← lintegral_mul_const _ hG]
  refine tendsto_lintegral_filter_of_dominated_convergence (fun u => G u * C0 η) ?_ ?_ ?_ ?_
  · exact Eventually.of_forall fun t =>
      hG.mul ((measurable_Hk η).comp (measurable_const.sub measurable_id))
  · exact Eventually.of_forall fun t => Eventually.of_forall fun u => by
      gcongr; exact Hk_le η h1 hμ hpos _
  · rw [lintegral_mul_const _ hG]; exact ENNReal.mul_ne_top hGi (C0_ne_top η)
  · refine Eventually.of_forall fun u => ?_
    have hu : Tendsto (fun t : ℝ => t - u) atTop atTop := by
      simpa [sub_eq_add_neg] using tendsto_atTop_add_const_right atTop (-u) tendsto_id
    exact ENNReal.Tendsto.const_mul ((Hk_tendsto η h1 hμ hpos l hl hr).comp hu)
      (Or.inl (ENNReal.ofReal_pos.2 (by positivity)).ne')

end Main

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measReal_anti (P : Measure Ω) [IsFiniteMeasure P] (X : Ω → ℝ) :
    Antitone (fun s => P.real {ω | Real.exp s < X ω}) := by
  intro a b hab
  exact measureReal_mono (fun ω hω => lt_of_le_of_lt (Real.exp_le_exp.mpr hab) hω)

lemma smooth_rFun_eq (P : Measure Ω) [IsFiniteMeasure P] (R : Ω → ℝ) (κ t : ℝ) :
    smooth (rFun P R κ) t =
      (Sm (fun s => ENNReal.ofReal (Real.exp (κ * s)) * P {ω | Real.exp s < R ω}) t).toReal := by
  have hmeas : Measurable (fun u => Real.exp (-(t - u)) * rFun P R κ u) := by
    unfold rFun
    exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (-(t - u)))).mul
      ((by fun_prop : Measurable (fun u : ℝ => Real.exp (κ * u))).mul (measReal_anti P R).measurable)
  have hnn : ∀ u, 0 ≤ Real.exp (-(t - u)) * rFun P R κ u := fun u => by
    unfold rFun; exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
  rw [smooth, integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hnn)
    hmeas.aestronglyMeasurable]
  congr 1
  rw [← lintegral_indicator measurableSet_Iic]
  unfold Sm
  refine lintegral_congr fun u => ?_
  by_cases hu : u ≤ t
  · rw [Set.indicator_of_mem (show u ∈ Set.Iic t from hu), kE_of_nonneg (sub_nonneg.2 hu)]
    unfold rFun
    rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ENNReal.ofReal_mul (Real.exp_pos _).le,
      ofReal_measureReal]
  · rw [Set.indicator_of_notMem (show u ∉ Set.Iic t from hu), kE_of_neg (by
      push_neg at hu; linarith), zero_mul]

/-- **Key renewal limit, Case 1** (Goldie 1991, §9). -/
theorem key_renewal_main (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h28 : TailCondPlus P M R κ) :
    Tendsto (smooth (rFun P R κ)) atTop
      (𝓝 ((cramerMean κ (P.map M))⁻¹ * ∫ t, smooth (gOne P M R κ) t)) := by
  set ν := P.map M with hνdef
  haveI : IsProbabilityMeasure ν := Measure.isProbabilityMeasure_map hM.aemeasurable
  have hν0 : ν (Set.Iio 0) = 0 := by
    rw [hνdef, Measure.map_apply hM measurableSet_Iio]
    rw [ae_iff] at hM_nonneg
    refine measure_mono_null (fun ω hω => ?_) hM_nonneg
    exact not_le.2 hω
  have hκ := hC.pos
  set η := tiltOn κ ν (Set.Ioi 0) with hηdef
  haveI hηp : IsProbabilityMeasure η := eta_prob κ ν hν0 hC
  have h1 := eta_integrable κ ν hν0 hC
  have hmean : ∫ y, y ∂η = cramerMean κ ν := eta_mean κ ν hν0 hC
  have hμ : 0 < ∫ y, y ∂η := by rw [hmean]; exact cramerMean_pos κ ν hC
  have hpos := eta_aF_pos κ ν hν0 hC
  have hr := eta_expMom κ ν hν0 hC
  have hκ1 : expMom κ η ≤ 1 := by
    unfold expMom
    rw [lintegral_eta κ hκ ν hν0 _ (measurable_expden κ)]
    calc ∫⁻ x, ENNReal.ofReal (|x| ^ κ) * ENNReal.ofReal (Real.exp (-(κ * Real.log |x|))) ∂ν
        ≤ ∫⁻ _x, 1 ∂ν := lintegral_mono fun x => by
          rcases eq_or_ne x 0 with rfl | hx
          · simp [Real.zero_rpow hκ.ne']
          · rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (abs_nonneg x) κ),
              ← exp_kappa_log_abs κ x hx, ← Real.exp_add]
            simp
      _ = 1 := by simp
  -- the tail function `F(s) = P(R > e^s)`
  set F : ℝ → ℝ≥0∞ := fun s => P {ω | Real.exp s < R ω} with hFdef
  have hF1 : ∀ s, F s ≤ 1 := fun s => prob_le_one
  have hFa : Antitone F := tail_anti P R
  have hFm : Measurable F := hFa.measurable
  have hF0 : Tendsto F atTop (𝓝 0) := by
    have hanti : Antitone (fun s : ℝ => {ω | Real.exp s < R ω}) := fun a b hab ω hω =>
      lt_of_le_of_lt (Real.exp_le_exp.mpr hab) hω
    have := tendsto_measure_iInter_atTop (μ := P)
      (fun i => (measurableSet_lt measurable_const hR).nullMeasurableSet) hanti
      ⟨0, measure_ne_top _ _⟩
    have hempty : (⋂ s : ℝ, {ω | Real.exp s < R ω}) = ∅ := by
      rw [Set.iInter_eq_empty_iff]
      intro ω
      refine ⟨R ω, fun h => ?_⟩
      have h2 : R ω + 1 ≤ Real.exp (R ω) := Real.add_one_le_exp _
      have h3 : Real.exp (R ω) < R ω := h
      linarith
    rw [hempty, measure_empty] at this
    exact this
  -- the signed function `g₁` and its parts
  set g := gOne P M R κ with hgdef
  have hgi : Integrable g := gOne_integrable P M R κ h28
  have hgm : Measurable g := by
    rw [hgdef]; unfold gOne
    exact (by fun_prop : Measurable (fun u : ℝ => Real.exp (κ * u))).mul
      ((measReal_anti P R).measurable.sub (measReal_anti P (fun ω => M ω * R ω)).measurable)
  set Gp : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (g t) with hGp
  set Gm : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (-g t) with hGm
  have hGpm : Measurable Gp := ENNReal.measurable_ofReal.comp hgm
  have hGmm : Measurable Gm := ENNReal.measurable_ofReal.comp hgm.neg
  have hfin : ∫⁻ t, ‖g t‖ₑ < ∞ := hgi.2
  have hGpi : ∫⁻ t, Gp t ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin.ne (lintegral_mono fun t => ?_)
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (le_abs_self _)
  have hGmi : ∫⁻ t, Gm t ≠ ∞ := by
    refine ne_top_of_le_ne_top hfin.ne (lintegral_mono fun t => ?_)
    rw [Real.enorm_eq_ofReal_abs]; exact ENNReal.ofReal_le_ofReal (neg_le_abs _)
  -- the renewal equation `ρ + G₋ = G₊ + ρ ⊛ η`
  have hE : ∀ s, ENNReal.ofReal (Real.exp (κ * s)) * F s + Gm s =
      Gp s + cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) η s := by
    intro s
    have hB := tail_eq P M R hM hR κ hind hν0 s
    have hcv : cv (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) η s =
        cv (Fp P R κ) η s := rfl
    have ha : ENNReal.ofReal (Real.exp (κ * s)) * F s =
        ENNReal.ofReal (Real.exp (κ * s) * P.real {ω | Real.exp s < R ω}) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal]
    have hb : ENNReal.ofReal (Real.exp (κ * s)) * P {ω | Real.exp s < M ω * R ω} =
        ENNReal.ofReal (Real.exp (κ * s) * P.real {ω | Real.exp s < M ω * R ω}) := by
      rw [ENNReal.ofReal_mul (Real.exp_pos _).le, ofReal_measureReal]
    rw [hcv, ← hB, ha, hb]
    have hg : g s = Real.exp (κ * s) * P.real {ω | Real.exp s < R ω} -
        Real.exp (κ * s) * P.real {ω | Real.exp s < M ω * R ω} := by
      rw [hgdef]; unfold gOne; ring
    simp only [hGp, hGm, hg]
    exact ofReal_split _ _ (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
      (mul_nonneg (Real.exp_pos _).le measureReal_nonneg)
  have hid := renewal_solution η κ (κ / 2) F Gp Gm hκ hF1 hFa hF0 hFm hGpm hGmm
    (by positivity) (by linarith) hκ1 hr hE
  -- pass to reals
  have key : ∀ t, smooth (rFun P R κ) t =
      (∫⁻ w, Gp w * Hk η (t - w)).toReal - (∫⁻ w, Gm w * Hk η (t - w)).toReal := by
    intro t
    rw [smooth_rFun_eq P R κ t]
    have hAp : ∫⁻ w, Gp w * Hk η (t - w) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hGpi (C0_ne_top η)) (Ap_le η h1 hμ hpos Gp hGpm t)
    have hAm : ∫⁻ w, Gm w * Hk η (t - w) ≠ ∞ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top hGmi (C0_ne_top η)) (Ap_le η h1 hμ hpos Gm hGmm t)
    have hS : Sm (fun s => ENNReal.ofReal (Real.exp (κ * s)) * F s) t ≠ ∞ :=
      ne_top_of_le_ne_top hAp ((hid t) ▸ le_self_add)
    rw [← hid t, ENNReal.toReal_add hS hAm]
    ring
  have hT := ((ENNReal.tendsto_toReal (ENNReal.mul_ne_top hGpi ENNReal.ofReal_ne_top)).comp
      (Ap_tendsto η h1 hμ hpos (κ / 2) (by positivity) hr Gp hGpm hGpi)).sub
    ((ENNReal.tendsto_toReal (ENNReal.mul_ne_top hGmi ENNReal.ofReal_ne_top)).comp
      (Ap_tendsto η h1 hμ hpos (κ / 2) (by positivity) hr Gm hGmm hGmi))
  have hval : ((∫⁻ w, Gp w) * ENNReal.ofReal (1 / ∫ x, x ∂η)).toReal -
      ((∫⁻ w, Gm w) * ENNReal.ofReal (1 / ∫ x, x ∂η)).toReal =
      (cramerMean κ (P.map M))⁻¹ * ∫ t, smooth (gOne P M R κ) t := by
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity),
      integral_smooth _ hgi, integral_eq_lintegral_pos_part_sub_lintegral_neg_part hgi, ← hmean]
    ring
  rw [hval] at hT
  exact hT.congr fun t => (key t).symm

end GoldieRenewal.Implicit.KRT

open MeasureTheory ProbabilityTheory Filter Topology GoldieRenewal.Implicit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (M R : Ω → ℝ) (hM : Measurable M) (hR : Measurable R) (κ : ℝ)
    (hC : CramerConditions κ (P.map M)) (hind : IndepFun R M P)
    (hM_nonneg : ∀ᵐ ω ∂P, 0 ≤ M ω) (h28 : TailCondPlus P M R κ) :
    Tendsto (smooth (rFun P R κ)) atTop
      (𝓝 ((cramerMean κ (P.map M))⁻¹ * ∫ t, smooth (gOne P M R κ) t)) := by
  exact GoldieRenewal.Implicit.KRT.key_renewal_main P M R hM hR κ hC hind hM_nonneg h28
