-- Prove2me | solution 1 for MasulloGRH.realLocalZeta_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T17:11:48.125131+00:00
-- url     : https://prove2.me/submissions/699914aa-34a6-473c-ba43-f325bc7dabc9

import Mathlib

open MeasureTheory
open scoped FourierTransform

set_option autoImplicit false

namespace Sol_MasulloGRH_realLocalZeta_functional_equation

open Complex Set Real

/-- Gaussian transform `t ↦ ∫ h(y) e^{-π t y²} dy`. -/
noncomputable def gaussInt (h : ℝ → ℂ) (t : ℝ) : ℂ :=
  ∫ y : ℝ, h y * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)

theorem cpow_ofReal_pos {x : ℝ} (hx : 0 < x) (z : ℂ) :
    (x : ℂ) ^ z = cexp ((Real.log x : ℂ) * z) := by
  rw [Complex.cpow_def_of_ne_zero (ofReal_ne_zero.2 hx.ne'), ← ofReal_log hx.le]

/-- Mellin transform of the Gaussian kernel. -/
theorem integral_kernel (w : ℂ) (hw : 0 < w.re) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ (w / 2 - 1) * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2) =
      Gammaℝ w * ((|y| : ℝ) : ℂ) ^ (-w) := by
  have hr : 0 < π * y ^ 2 := by positivity
  have hw2 : 0 < (w / 2).re := by simpa using hw
  have key := integral_cpow_mul_exp_neg_mul_Ioi hw2 hr
  have e1 : (fun t : ℝ => (t : ℂ) ^ (w / 2 - 1) * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)) =
      fun t : ℝ => (t : ℂ) ^ (w / 2 - 1) * cexp (-(((π * y ^ 2 : ℝ) : ℂ) * (t : ℂ))) := by
    funext t; congr 2; push_cast; ring
  rw [e1, key, Gammaℝ_def]
  have hy' : 0 < |y| := abs_pos.2 hy
  have e2 : (1 / ((π * y ^ 2 : ℝ) : ℂ)) = (((π * y ^ 2)⁻¹ : ℝ) : ℂ) := by
    push_cast; ring
  rw [e2, cpow_ofReal_pos (inv_pos.2 hr), cpow_ofReal_pos Real.pi_pos, cpow_ofReal_pos hy']
  have hl : Real.log (π * y ^ 2)⁻¹ = -(Real.log π + 2 * Real.log |y|) := by
    rw [Real.log_inv, Real.log_mul Real.pi_ne_zero (by positivity), ← sq_abs, Real.log_pow]
    push_cast; ring
  rw [hl]
  have e3 : cexp (↑(Real.log π) * (-w / 2)) * Complex.Gamma (w / 2) * cexp (↑(Real.log |y|) * -w)
      = Complex.Gamma (w / 2) * cexp (↑(Real.log π) * (-w / 2) + ↑(Real.log |y|) * -w) := by
    rw [Complex.exp_add]; ring
  rw [e3, mul_comm]
  congr 2
  push_cast; ring


theorem norm_kernel (w : ℂ) {t : ℝ} (ht : 0 < t) (y : ℝ) :
    ‖(t : ℂ) ^ (w / 2 - 1) * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)‖ =
      t ^ (w.re / 2 - 1) * Real.exp (-(π * y ^ 2 * t)) := by
  have e : (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2) = ((-(π * y ^ 2 * t) : ℝ) : ℂ) := by
    push_cast; ring
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ht, e, Complex.norm_exp_ofReal]
  congr 2
  simp

theorem integral_norm_kernel (σ : ℝ) (hσ : 0 < σ) {y : ℝ} (hy : y ≠ 0) :
    ∫ t in Ioi (0:ℝ), t ^ (σ / 2 - 1) * Real.exp (-(π * y ^ 2 * t)) =
      π ^ (-σ / 2) * Real.Gamma (σ / 2) * |y| ^ (-σ) := by
  have hr : 0 < π * y ^ 2 := by positivity
  rw [Real.integral_rpow_mul_exp_neg_mul_Ioi (by linarith) hr]
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos Real.pi_pos,
    Real.rpow_def_of_pos (abs_pos.2 hy)]
  have hl : Real.log (1 / (π * y ^ 2)) = -(Real.log π + 2 * Real.log |y|) := by
    rw [one_div, Real.log_inv, Real.log_mul Real.pi_ne_zero (by positivity), ← sq_abs,
      Real.log_pow]
    push_cast; ring
  rw [hl]
  have e3 : Real.exp (Real.log π * (-σ / 2)) * Real.Gamma (σ / 2) * Real.exp (Real.log |y| * -σ)
      = Real.Gamma (σ / 2) * Real.exp (Real.log π * (-σ / 2) + Real.log |y| * -σ) := by
    rw [Real.exp_add]; ring
  rw [e3, mul_comm]
  congr 2
  ring

theorem measurable_cpow_ofReal (z : ℂ) : Measurable (fun t : ℝ => (t : ℂ) ^ z) :=
  Complex.measurable_ofReal.pow_const z

theorem integrableOn_kernel (w : ℂ) (hw : 0 < w.re) {y : ℝ} (hy : y ≠ 0) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (w / 2 - 1) * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2))
      (Ioi 0) := by
  have hb : 0 < π * y ^ 2 := by positivity
  have hg := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := w.re / 2 - 1)
    (b := π * y ^ 2) (by linarith) one_pos hb
  refine Integrable.mono' hg ?_ ?_
  · refine ((measurable_cpow_ofReal _).mul ?_).aestronglyMeasurable
    exact (by fun_prop : Continuous fun t : ℝ => cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)).measurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    rw [norm_kernel w ht, Real.rpow_one]
    apply le_of_eq
    congr 2
    ring


theorem ae_ne_zero : ∀ᵐ y : ℝ, y ≠ 0 := by
  rw [ae_iff]; simp

/-- Mellin transform of the Gaussian transform: `|y|^{-w}` as a superposition of Gaussians. -/
theorem mellin_gaussInt (h : ℝ → ℂ) (hh : Continuous h) (w : ℂ) (hw : 0 < w.re)
    (hint : Integrable (fun y : ℝ => h y * ((|y| : ℝ) : ℂ) ^ (-w))) :
    mellin (gaussInt h) (w / 2) = Gammaℝ w * ∫ y : ℝ, h y * ((|y| : ℝ) : ℂ) ^ (-w) := by
  set K : ℝ → ℝ → ℂ := fun t y =>
    (t : ℂ) ^ (w / 2 - 1) * (h y * cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)) with hK
  have hmeas : AEStronglyMeasurable (Function.uncurry K)
      ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    refine Measurable.aestronglyMeasurable ?_
    refine ((measurable_cpow_ofReal _).comp measurable_fst).mul
      ((hh.measurable.comp measurable_snd).mul ?_)
    exact (by fun_prop : Continuous fun p : ℝ × ℝ =>
      cexp (-(π : ℂ) * (p.1 : ℂ) * (p.2 : ℂ) ^ 2)).measurable
  have hnormint : ∀ y : ℝ, y ≠ 0 → ∫ t in Ioi (0:ℝ), ‖K t y‖ =
      (π ^ (-w.re / 2) * Real.Gamma (w.re / 2)) * ‖h y * ((|y| : ℝ) : ℂ) ^ (-w)‖ := by
    intro y hy
    have e : ∀ t ∈ Ioi (0:ℝ), ‖K t y‖ =
        ‖h y‖ * (t ^ (w.re / 2 - 1) * Real.exp (-(π * y ^ 2 * t))) := by
      intro t ht
      simp only [hK]
      rw [mul_left_comm, norm_mul, norm_kernel w ht]
    rw [setIntegral_congr_fun measurableSet_Ioi e, integral_const_mul,
      integral_norm_kernel _ hw hy, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
    simp only [neg_re]
    ring
  have hprod : Integrable (Function.uncurry K) ((volume.restrict (Ioi (0:ℝ))).prod volume) := by
    rw [integrable_prod_iff' hmeas]
    constructor
    · filter_upwards [ae_ne_zero] with y hy
      refine ((integrableOn_kernel w hw hy).const_mul (h y)).congr ?_
      filter_upwards with t
      simp only [Function.uncurry_apply_pair, hK]
      ring
    · refine (hint.norm.const_mul (π ^ (-w.re / 2) * Real.Gamma (w.re / 2))).congr ?_
      filter_upwards [ae_ne_zero] with y hy
      simp only [Function.uncurry_apply_pair]
      rw [hnormint y hy]
  have step1 : mellin (gaussInt h) (w / 2) = ∫ t in Ioi (0:ℝ), ∫ y, K t y := by
    unfold mellin gaussInt
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [smul_eq_mul, hK]
    rw [integral_const_mul]
  have step3 : ∀ y : ℝ, y ≠ 0 → ∫ t in Ioi (0:ℝ), K t y =
      Gammaℝ w * (h y * ((|y| : ℝ) : ℂ) ^ (-w)) := by
    intro y hy
    have e : ∀ t, K t y = h y * ((t : ℂ) ^ (w / 2 - 1) *
        cexp (-(π : ℂ) * (t : ℂ) * (y : ℂ) ^ 2)) := by
      intro t; simp only [hK]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_kernel w hw hy]
    ring
  rw [step1, integral_integral_swap hprod, integral_congr_ae (ae_ne_zero.mono step3),
    integral_const_mul]


theorem measurable_abs_cpow (z : ℂ) : Measurable (fun y : ℝ => ((|y| : ℝ) : ℂ) ^ z) :=
  (Complex.measurable_ofReal.comp continuous_abs.measurable).pow_const z

theorem integrable_mul_abs_cpow (h : ℝ → ℂ) (hc : Continuous h) (hi : Integrable h)
    (hb : ∃ C, ∀ y, ‖h y‖ ≤ C) (w : ℂ) (hw0 : 0 < w.re) (hw1 : w.re < 1) :
    Integrable (fun y : ℝ => h y * ((|y| : ℝ) : ℂ) ^ (-w)) := by
  obtain ⟨C, hC⟩ := hb
  have hmeas : AEStronglyMeasurable (fun y : ℝ => h y * ((|y| : ℝ) : ℂ) ^ (-w)) volume :=
    (hc.measurable.mul (measurable_abs_cpow _)).aestronglyMeasurable
  have hw : -w ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp at this
    linarith
  have hnorm : ∀ y : ℝ, ‖h y * ((|y| : ℝ) : ℂ) ^ (-w)‖ = ‖h y‖ * |y| ^ (-w.re) := by
    intro y
    rcases eq_or_ne y 0 with rfl | hy
    · simp [Complex.zero_cpow hw, Real.zero_rpow (by linarith : -w.re ≠ 0)]
    · rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (abs_pos.2 hy)]
      simp
  rw [← integrableOn_univ, ← Set.union_compl_self (Metric.ball (0:ℝ) 1)]
  refine IntegrableOn.union ?_ ?_
  · refine integrableOn_ball_of_norm_le_rpow (μ := volume) (C := C) (α := w.re) (by simp)
      (by simpa using hw1) ?_ hmeas
    filter_upwards with y
    rw [hnorm, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hC y) (Real.rpow_nonneg (abs_nonneg y) _)
  · refine Integrable.mono' hi.norm.integrableOn hmeas.restrict ?_
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.measurableSet.compl)] with y hy
    rw [hnorm]
    have h1 : 1 ≤ |y| := by simpa [Metric.mem_ball, Real.dist_eq] using hy
    calc ‖h y‖ * |y| ^ (-w.re) ≤ ‖h y‖ * 1 :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_one_of_one_le_of_nonpos h1 (by linarith))
            (norm_nonneg _)
      _ = ‖h y‖ := mul_one _

theorem mulFormula (f : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (hg : Integrable g) :
    ∫ x : ℝ, (𝓕 f) x * g x = ∫ y : ℝ, f y * 𝓕 g y := by
  rw [SchwartzMap.fourier_coe]
  simpa using! (VectorFourier.integral_fourierIntegral_smul_eq_flip (L := innerₗ ℝ)
      Real.continuous_fourierChar continuous_inner f.integrable hg)

theorem integrable_gauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) := by
  have e : (fun x : ℝ => cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) =
      fun x : ℝ => cexp (-((π : ℂ) * t) * (x : ℂ) ^ 2) := by
    funext x; ring_nf
  rw [e]
  exact integrable_cexp_neg_mul_sq (by rw [← ofReal_mul, ofReal_re]; positivity)

theorem integrable_xgauss {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : ℝ => (x : ℂ) * cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) := by
  have e : (fun x : ℝ => (x : ℂ) * cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) =
      fun x : ℝ => (x : ℂ) * cexp (-((π : ℂ) * t) * (x : ℂ) ^ 2) := by
    funext x; ring_nf
  rw [e]
  exact integrable_mul_cexp_neg_mul_sq (by rw [← ofReal_mul, ofReal_re]; positivity)

theorem fourier_gauss {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) ξ =
      ((t⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * cexp (-(π : ℂ) * ((t⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2) := by
  rw [fourier_gaussian_pi (b := (t : ℂ)) (by simpa using ht)]
  have harg : (t : ℂ).arg ≠ π := by
    rw [arg_ofReal_of_nonneg ht.le]; exact Real.pi_ne_zero.symm
  beta_reduce
  rw [ofReal_inv, Complex.inv_cpow _ _ harg]
  simp only [one_div]
  rw [div_eq_mul_inv]


theorem fourier_xgauss {t : ℝ} (ht : 0 < t) (ξ : ℝ) :
    𝓕 (fun x : ℝ => (x : ℂ) * cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) ξ =
      -I * ((t⁻¹ : ℝ) : ℂ) ^ (3 / 2 : ℂ) *
        ((ξ : ℂ) * cexp (-(π : ℂ) * ((t⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) := by
  set g : ℝ → ℂ := fun x => cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2) with hg
  have hgi : Integrable g := integrable_gauss ht
  have hxgi : Integrable (fun x : ℝ => x • g x) := by
    simpa only [Complex.real_smul] using integrable_xgauss ht
  have hd := congrFun (Real.deriv_fourier hgi hxgi) ξ
  set c : ℂ := ((t⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) with hc
  set a : ℂ := -(π : ℂ) * ((t⁻¹ : ℝ) : ℂ) with ha
  have hE : HasDerivAt (fun z : ℂ => c * cexp (a * z ^ 2))
      (c * (cexp (a * (ξ : ℂ) ^ 2) * (a * (2 * (ξ : ℂ))))) (ξ : ℂ) := by
    have := (((hasDerivAt_pow 2 (ξ : ℂ)).const_mul a).cexp).const_mul c
    exact this.congr_deriv (by norm_num)
  have hD := hE.comp_ofReal
  have hfun : (fun y : ℝ => c * cexp (a * (y : ℂ) ^ 2)) = 𝓕 g := by
    funext y
    rw [hg, fourier_gauss ht]
  rw [hfun] at hD
  rw [hD.deriv] at hd
  have hlin : 𝓕 (fun x : ℝ => (-2 * (π : ℂ) * I * x) • g x) ξ =
      (-2 * (π : ℂ) * I) * 𝓕 (fun x : ℝ => (x : ℂ) * g x) ξ := by
    rw [Real.fourier_real_eq_integral_exp_smul, Real.fourier_real_eq_integral_exp_smul,
      ← integral_const_mul]
    congr 1
    funext v
    simp only [smul_eq_mul]
    ring
  rw [hlin] at hd
  have hk : (-2 * (π : ℂ) * I) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_ne_zero
    simp [this, I_ne_zero]
  have hc' : ((t⁻¹ : ℝ) : ℂ) ^ (3 / 2 : ℂ) = c * ((t⁻¹ : ℝ) : ℂ) := by
    rw [hc, show (3 / 2 : ℂ) = 1 / 2 + 1 by norm_num,
      Complex.cpow_add _ _ (ofReal_ne_zero.2 (inv_ne_zero ht.ne')), Complex.cpow_one]
  apply mul_left_cancel₀ hk
  rw [← hd, hc', ha]
  linear_combination (-2 * (π : ℂ) * c * ((t⁻¹ : ℝ) : ℂ) * (ξ : ℂ) *
    cexp (-(π : ℂ) * ((t⁻¹ : ℝ) : ℂ) * (ξ : ℂ) ^ 2)) * I_sq


theorem gaussInt_fourier (f : SchwartzMap ℝ ℂ) {t : ℝ} (ht : 0 < t) :
    gaussInt (fun x : ℝ => (𝓕 f) x) t = ((t⁻¹ : ℝ) : ℂ) ^ (1 / 2 : ℂ) * gaussInt f t⁻¹ := by
  simp only [gaussInt]
  rw [mulFormula f _ (integrable_gauss ht), ← integral_const_mul]
  congr 1
  funext y
  rw [fourier_gauss ht]
  ring

theorem gaussInt_fourier_x (f : SchwartzMap ℝ ℂ) {t : ℝ} (ht : 0 < t) :
    gaussInt (fun x : ℝ => (𝓕 f) x * x) t =
      -I * ((t⁻¹ : ℝ) : ℂ) ^ (3 / 2 : ℂ) * gaussInt (fun y => f y * y) t⁻¹ := by
  simp only [gaussInt]
  have e : (fun x : ℝ => (𝓕 f) x * x * cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) =
      fun x : ℝ => (𝓕 f) x * ((x : ℂ) * cexp (-(π : ℂ) * (t : ℂ) * (x : ℂ) ^ 2)) := by
    funext x; ring
  rw [e, mulFormula f _ (integrable_xgauss ht), ← integral_const_mul]
  congr 1
  funext y
  rw [fourier_xgauss ht]
  ring

theorem real_sign_mul_abs (x : ℝ) : Real.sign x * |x| = x := by
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · rw [Real.sign_of_neg hx, abs_of_neg hx]; ring
  · simp
  · rw [Real.sign_of_pos hx, abs_of_pos hx]; ring

theorem sign_mul_abs_cpow (x : ℝ) (z : ℂ) :
    ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ z = (x : ℂ) * ((|x| : ℝ) : ℂ) ^ (z - 1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have hx' : ((|x| : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (abs_ne_zero.2 hx)
    rw [Complex.cpow_sub _ _ hx', Complex.cpow_one]
    have e : (x : ℂ) = ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) := by
      rw [← ofReal_mul, real_sign_mul_abs]
    rw [e]
    field_simp

theorem mellin_comp_inv_cpow (G : ℝ → ℂ) (c a s : ℂ) (F : ℝ → ℂ)
    (hF : ∀ t : ℝ, 0 < t → F t = c * ((t⁻¹ : ℝ) : ℂ) ^ a * G t⁻¹) :
    mellin F s = c * mellin G (-s + a) := by
  have e : mellin F s = mellin (fun t => c • (fun u : ℝ => (u : ℂ) ^ a • G u) t⁻¹) s := by
    unfold mellin
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [smul_eq_mul]
    rw [hF t ht]
    ring
  rw [e, mellin_const_smul, mellin_comp_inv (fun u : ℝ => (u : ℂ) ^ a • G u), mellin_cpow_smul,
    smul_eq_mul]

theorem schwartz_bdd (f : SchwartzMap ℝ ℂ) : ∃ C, ∀ y, ‖f y‖ ≤ C := by
  obtain ⟨C, -, hC⟩ := f.decay 0 0
  exact ⟨C, fun y => by simpa [norm_iteratedFDeriv_zero] using hC y⟩

end Sol_MasulloGRH_realLocalZeta_functional_equation

open Sol_MasulloGRH_realLocalZeta_functional_equation in
theorem solution
    (f : SchwartzMap ℝ ℂ) (s : ℂ) (h0 : 0 < s.re) (h1 : s.re < 1) :
    (∫ x : ℝ, f x * ((|x| : ℝ) : ℂ) ^ (s - 1)) * Complex.Gammaℝ (1 - s) =
      Complex.Gammaℝ s * ∫ x : ℝ, (𝓕 f) x * ((|x| : ℝ) : ℂ) ^ (-s) ∧
    (∫ x : ℝ, f x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) * Complex.Gammaℝ (2 - s) =
      Complex.I * Complex.Gammaℝ (s + 1) *
        ∫ x : ℝ, (𝓕 f) x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (-s) := by
  have hFc : Continuous (fun x : ℝ => (𝓕 f) x) := (𝓕 f).continuous
  have hFi : Integrable (fun x : ℝ => (𝓕 f) x) := (𝓕 f).integrable
  have hs1 : 0 < (1 - s).re := by simp; linarith
  have hs1' : (1 - s).re < 1 := by simp; linarith
  have iF : Integrable (fun y : ℝ => (𝓕 f) y * ((|y| : ℝ) : ℂ) ^ (-s)) :=
    integrable_mul_abs_cpow _ hFc hFi (schwartz_bdd (𝓕 f)) s h0 h1
  have if1 : Integrable (fun y : ℝ => f y * ((|y| : ℝ) : ℂ) ^ (-(1 - s))) :=
    integrable_mul_abs_cpow _ f.continuous f.integrable (schwartz_bdd f) (1 - s) hs1 hs1'
  constructor
  · have A := mellin_gaussInt f f.continuous (1 - s) hs1 if1
    have B := mellin_gaussInt (fun x : ℝ => (𝓕 f) x) hFc s h0 iF
    have C : mellin (gaussInt (fun x : ℝ => (𝓕 f) x)) (s / 2) =
        mellin (gaussInt f) ((1 - s) / 2) := by
      rw [mellin_comp_inv_cpow (gaussInt f) 1 (1 / 2) (s / 2) _
        (fun t ht => by rw [gaussInt_fourier f ht, one_mul]), one_mul]
      congr 1
      ring
    rw [← B, C, A, neg_sub, mul_comm]
  · have e1 : (fun x : ℝ => f x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (s - 1)) =
        fun x : ℝ => (f x * x) * ((|x| : ℝ) : ℂ) ^ (-(2 - s)) := by
      funext x
      rw [mul_assoc, sign_mul_abs_cpow, show -(2 - s) = s - 1 - 1 by ring]
      ring
    have e2 : (fun x : ℝ => (𝓕 f) x * ((Real.sign x : ℝ) : ℂ) * ((|x| : ℝ) : ℂ) ^ (-s)) =
        fun x : ℝ => ((𝓕 f) x * x) * ((|x| : ℝ) : ℂ) ^ (-(s + 1)) := by
      funext x
      rw [mul_assoc, sign_mul_abs_cpow, show -(s + 1) = -s - 1 by ring]
      ring
    have hsign : ∀ x : ℝ, ‖((Real.sign x : ℝ) : ℂ)‖ ≤ 1 := by
      intro x
      rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
    have if2 : Integrable (fun x : ℝ => (f x * x) * ((|x| : ℝ) : ℂ) ^ (-(2 - s))) := by
      refine if1.mono ((f.continuous.mul Complex.continuous_ofReal).measurable.mul
        (measurable_abs_cpow _)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [← congrFun e1 x, norm_mul, norm_mul, norm_mul, show s - 1 = -(1 - s) by ring]
      calc ‖f x‖ * ‖((Real.sign x : ℝ) : ℂ)‖ * ‖((|x| : ℝ) : ℂ) ^ (-(1 - s))‖
          ≤ ‖f x‖ * 1 * ‖((|x| : ℝ) : ℂ) ^ (-(1 - s))‖ := by gcongr; exact hsign x
        _ = ‖f x‖ * ‖((|x| : ℝ) : ℂ) ^ (-(1 - s))‖ := by ring
    have iF2 : Integrable (fun x : ℝ => ((𝓕 f) x * x) * ((|x| : ℝ) : ℂ) ^ (-(s + 1))) := by
      refine iF.mono ((hFc.mul Complex.continuous_ofReal).measurable.mul
        (measurable_abs_cpow _)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
      rw [← congrFun e2 x, norm_mul, norm_mul, norm_mul]
      calc ‖(𝓕 f) x‖ * ‖((Real.sign x : ℝ) : ℂ)‖ * ‖((|x| : ℝ) : ℂ) ^ (-s)‖
          ≤ ‖(𝓕 f) x‖ * 1 * ‖((|x| : ℝ) : ℂ) ^ (-s)‖ := by gcongr; exact hsign x
        _ = ‖(𝓕 f) x‖ * ‖((|x| : ℝ) : ℂ) ^ (-s)‖ := by ring
    have A := mellin_gaussInt (fun x : ℝ => f x * x) (f.continuous.mul Complex.continuous_ofReal)
      (2 - s) (by simp; linarith) if2
    have hFc2 : Continuous (fun x : ℝ => (𝓕 f) x * (x : ℂ)) :=
      hFc.mul Complex.continuous_ofReal
    have hs2 : 0 < (s + 1).re := by simp; linarith
    have B := mellin_gaussInt (fun x : ℝ => (𝓕 f) x * (x : ℂ)) hFc2 (s + 1) hs2
      (by beta_reduce; exact iF2)
    have C : mellin (gaussInt (fun x : ℝ => (𝓕 f) x * x)) ((s + 1) / 2) =
        -Complex.I * mellin (gaussInt (fun y : ℝ => f y * y)) ((2 - s) / 2) := by
      rw [mellin_comp_inv_cpow (gaussInt (fun y : ℝ => f y * y)) (-Complex.I) (3 / 2) ((s + 1) / 2) _
        (fun t ht => gaussInt_fourier_x f ht)]
      congr 2
      ring
    have hI : ∀ a : ℂ, Complex.I * (-Complex.I * a) = a := fun a => by
      linear_combination (-a) * Complex.I_sq
    rw [e1, e2, mul_assoc Complex.I, ← B, C, A, hI, mul_comm]
