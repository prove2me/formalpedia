-- Prove2me | solution 1 for MasulloAudit.real_log_fourier_eq_neg_half_integral_of_zero_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T03:01:29.241468+00:00
-- url     : https://prove2.me/submissions/6b41c280-5f23-43d9-96a6-66ceaf031812

import Mathlib

open Filter MeasureTheory Set FourierTransform
open scoped SchwartzMap FourierTransform Topology Interval

namespace MasulloAudit

/-- The distribution obtained by Fourier transforming the real logarithm
under the usual Lebesgue self-dual normalization. -/
noncomputable def realLogFourier (f : ℝ → ℂ) : ℂ :=
  ∫ ξ : ℝ, (Real.log |ξ| : ℂ) * 𝓕 f ξ

private lemma integrable_log_mul_schwartz (g : 𝓢(ℝ, ℂ)) :
    Integrable (fun x : ℝ ↦ (Real.log |x| : ℂ) * g x) := by
  let K := Icc (-1 : ℝ) 1
  let f (x : ℝ) := (Real.log |x| : ℂ) * g x
  have hf : Measurable f := by
    unfold f
    exact (Complex.continuous_ofReal.measurable.comp (Real.measurable_log.comp measurable_abs)).mul
      g.continuous.measurable
  have hLog : IntegrableOn (fun x : ℝ ↦ Real.log |x|) K := by
    simp only [Real.log_abs, K]
    have h : IntegrableOn (fun x : ℝ ↦ Real.log x) (Ioc (-1 : ℝ) 1) :=
      (intervalIntegral.intervalIntegrable_log' (a := (-1 : ℝ)) (b := 1)).1
    simpa only [IntegrableOn, Measure.restrict_congr_set Ioc_ae_eq_Icc] using h
  let C := SchwartzMap.seminorm ℝ 0 0 g
  have hNear : IntegrableOn f K := by
    refine (hLog.norm.const_mul C).mono' hf.aestronglyMeasurable ?_
    filter_upwards [] with x
    dsimp only [f]
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [mul_comm C]
    exact mul_le_mul_of_nonneg_left (SchwartzMap.norm_le_seminorm ℝ g x) (abs_nonneg _)
  have hFar : IntegrableOn f Kᶜ := by
    have hI := (g.integrable_pow_mul volume 1).integrableOn (s := Kᶜ)
    refine hI.mono' hf.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    have hx'' : 0 < |x| := zero_lt_one.trans hx'
    dsimp only [f]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg hx'.le), pow_one]
    exact mul_le_mul_of_nonneg_right
      ((Real.log_le_sub_one_of_pos hx'').trans (sub_le_self _ zero_le_one)) (norm_nonneg _)
  have h := hNear.union hFar
  simpa only [union_compl_self, integrableOn_univ, f] using h

private lemma integral_fourier_schwartz_eq_value_zero (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ) = f 0 := by
  have hf : Integrable (𝓕 (f : ℝ → ℂ)) := by
    simpa only [SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have h := f.integrable.fourierInv_fourier_eq hf (v := (0:ℝ)) f.continuous.continuousAt
  rw [Real.fourierInv_eq] at h
  simpa only [inner_zero_right, AddChar.map_zero_eq_one, one_smul] using h

private noncomputable def logHeat (b t : ℝ) : ℝ :=
  t⁻¹ * (Real.exp (-t) - Real.exp (-(b*t)))

private lemma abs_exp_sub_exp_le {a b : ℝ} (ha : a ≤ 0) (hb : b ≤ 0) :
    |Real.exp a - Real.exp b| ≤ |a-b| := by
  wlog hab : b ≤ a
  · rw [abs_sub_comm (Real.exp a), abs_sub_comm a]
    exact this hb ha (le_of_not_ge hab)
  have he : Real.exp a - Real.exp b = Real.exp a * (1 - Real.exp (b-a)) := by
    rw [mul_sub, mul_one, ← Real.exp_add, show a+(b-a)=b by ring]
  rw [abs_of_nonneg (sub_nonneg.mpr (Real.exp_le_exp.mpr hab)),
    abs_of_nonneg (sub_nonneg.mpr hab), he]
  have hne : 0 ≤ 1 - Real.exp (b-a) := by
    rw [← Real.exp_zero, sub_nonneg, Real.exp_le_exp]
    linarith
  have hexp : Real.exp a ≤ 1 := Real.exp_le_one_iff.mpr ha
  exact (mul_le_of_le_one_left hne hexp).trans (by linarith [Real.add_one_le_exp (b-a)])

private lemma integrableOn_logHeat {b : ℝ} (hb : 0 < b) :
    IntegrableOn (logHeat b) (Ioi 0) := by
  have hMeas : Measurable (logHeat b) := by
    unfold logHeat
    fun_prop
  have hNear : IntegrableOn (logHeat b) (Ioc 0 1) := by
    refine (integrableOn_const (C := |b-1|) (by simp)).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    have ht' : 0 < t := ht.1
    rw [logHeat, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht'.le)]
    calc t⁻¹ * |Real.exp (-t) - Real.exp (-(b*t))|
      _ ≤ t⁻¹ * |(b-1)*t| := by
        apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr ht'.le)
        have he : -t - -(b*t) = (b-1)*t := by ring
        rw [← he]
        exact abs_exp_sub_exp_le (by linarith) (neg_nonpos.mpr (mul_nonneg hb.le ht'.le))
      _ = |b-1| := by rw [abs_mul, abs_of_pos ht']; field_simp
  have hExp : IntegrableOn (fun t : ℝ ↦ Real.exp (-(b*t))) (Ioi 1) := by
    refine (integrableOn_Ioi_comp_mul_left_iff (fun t : ℝ ↦ Real.exp (-t)) 1 hb).mpr ?_
    apply integrableOn_exp_neg_Ioi
  have hFar : IntegrableOn (logHeat b) (Ioi 1) := by
    refine ((integrableOn_exp_neg_Ioi 1).add hExp).mono'
      hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t := zero_lt_one.trans ht
    rw [logHeat, Real.norm_eq_abs, abs_mul, abs_of_nonneg (inv_nonneg.mpr ht'.le)]
    have ha := Real.exp_pos (-t)
    have hb' := Real.exp_pos (-(b*t))
    calc t⁻¹ * |Real.exp (-t) - Real.exp (-(b*t))|
      _ ≤ |Real.exp (-t) - Real.exp (-(b*t))| :=
        mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ ht.le)
      _ ≤ Real.exp (-t) + Real.exp (-(b*t)) := by rw [abs_le]; constructor <;> linarith
  simpa only [Ioc_union_Ioi_eq_Ioi zero_le_one] using hNear.union hFar

private lemma integral_logHeat {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), logHeat b t) = Real.log b := by
  let g (t : ℝ) := Real.exp (-t)
  have hg : Continuous g := by fun_prop
  have h0 : Tendsto g (𝓝[>] 0) (𝓝 1) := by
    have h := hg.continuousWithinAt (s := Ioi (0:ℝ)) (x := 0)
    change Tendsto g (𝓝[>] 0) (𝓝 (g 0)) at h
    simpa [g] using h
  have hinf : Tendsto g atTop (𝓝 0) := Real.tendsto_exp_neg_atTop_nhds_zero
  simpa [logHeat, g, smul_eq_mul] using
    Frullani.integral_Ioi_eq (f := g) (hg.locallyIntegrable.locallyIntegrableOn (Ioi 0))
      zero_lt_one hb h0 hinf (by
        simp only [g, smul_eq_mul, one_mul]
        exact integrableOn_logHeat hb)

private lemma integral_abs_logHeat {b : ℝ} (hb : 0 < b) :
    (∫ t in Ioi (0 : ℝ), |logHeat b t|) = |Real.log b| := by
  rcases le_or_gt 1 b with h | h
  · rw [abs_of_nonneg (Real.log_nonneg h), ← integral_logHeat hb]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ abs_of_nonneg ?_
    have ht' : 0 < t := ht
    unfold logHeat
    exact mul_nonneg (inv_nonneg.mpr ht'.le) (sub_nonneg.mpr (Real.exp_le_exp.mpr (by nlinarith)))
  · rw [abs_of_neg (Real.log_neg hb h), ← integral_logHeat hb, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ abs_of_nonpos ?_
    have ht' : 0 < t := ht
    unfold logHeat
    exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht'.le)
      (sub_nonpos.mpr (Real.exp_le_exp.mpr (by nlinarith)))


private noncomputable def realGaussian (t x : ℝ) : ℝ :=
  Real.exp (-t*x^2)

private noncomputable def realGaussFourier (t x : ℝ) : ℝ :=
  Real.sqrt (Real.pi/t) * Real.exp (-Real.pi^2*x^2/t)

private lemma fourier_realGaussian {t : ℝ} (ht : 0 < t) (x : ℝ) :
    𝓕 (fun ξ : ℝ ↦ (realGaussian t ξ : ℂ)) x = (realGaussFourier t x : ℂ) := by
  have hb : 0 < t/Real.pi := div_pos ht Real.pi_pos
  have h := congrFun (fourier_gaussian_pi (b := ((t/Real.pi : ℝ) : ℂ))
    (by simpa using hb)) x
  have hLeft : (fun ξ : ℝ ↦ Complex.exp (-↑Real.pi * ↑(t/Real.pi) * (ξ : ℂ)^2)) =
      fun ξ : ℝ ↦ (realGaussian t ξ : ℂ) := by
    funext ξ
    rw [realGaussian, Complex.ofReal_exp]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [hLeft] at h
  rw [h]
  have hCast : (1/2 : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
  rw [hCast, ← Complex.ofReal_cpow hb.le, ← Real.sqrt_eq_rpow, ← Complex.ofReal_one, ← Complex.ofReal_div]
  unfold realGaussFourier
  rw [Complex.ofReal_mul, Complex.ofReal_exp]
  congr 1
  · exact congrArg Complex.ofReal (by rw [one_div, ← Real.sqrt_inv, inv_div])
  · congr 1
    push_cast
    field_simp [Real.pi_ne_zero, ht.ne']

private lemma integral_gaussFourier_mul_eq {t : ℝ} (ht : 0 < t) (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ * (realGaussian t ξ : ℂ)) =
      ∫ x : ℝ, f x * (realGaussFourier t x : ℂ) := by
  have hG : Integrable (fun ξ : ℝ ↦ (realGaussian t ξ : ℂ)) :=
    by simpa only [realGaussian] using! ((integrable_exp_neg_mul_sq ht).ofReal (𝕜 := ℂ))
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner (f.integrable (μ := volume)) hG
  rw [show (innerₗ ℝ).flip = innerₗ ℝ from by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    exact real_inner_comm (x := x) (y := y)] at h
  change (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ • (realGaussian t ξ : ℂ)) =
    ∫ x : ℝ, f x • 𝓕 (fun ξ : ℝ ↦ (realGaussian t ξ : ℂ)) x at h
  simpa only [smul_eq_mul, fourier_realGaussian ht] using h

private noncomputable def heatKernel (x t : ℝ) : ℝ :=
  t⁻¹ * realGaussFourier t x

private lemma heatKernel_nonneg (x t : ℝ) (ht : 0 < t) : 0 ≤ heatKernel x t := by
  unfold heatKernel realGaussFourier
  positivity

private lemma heatKernel_rpow (x t : ℝ) (ht : 0 < t) :
    heatKernel x t = (|(-1/2:ℝ)| * t ^ ((-1/2:ℝ) - 1)) *
      (2 * Real.sqrt Real.pi * Real.exp (-(Real.pi^2*x^2)*(t^(-1/2:ℝ))^2)) := by
  have hPow : (t^(-1/2:ℝ))^2 = t⁻¹ := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul ht.le, show (-1/2:ℝ)*↑(2:ℕ) = -1 by norm_num,
      Real.rpow_neg_one]
  have hPow' : t ^ ((-1/2:ℝ)-1) = (Real.sqrt t)⁻¹ * t⁻¹ := by
    rw [Real.rpow_sub ht, Real.rpow_one]
    rw [show (-1/2:ℝ) = -(1/2) by ring, Real.rpow_neg ht.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
  unfold heatKernel realGaussFourier
  rw [hPow, hPow', Real.sqrt_div Real.pi_pos.le, abs_of_nonpos (by norm_num : (-1/2:ℝ) ≤ 0)]
  rw [show -(Real.pi^2*x^2)*t⁻¹ = -Real.pi^2*x^2/t by ring]
  ring

private lemma integrableOn_heatKernel {x : ℝ} (hx : x ≠ 0) :
    IntegrableOn (heatKernel x) (Ioi 0) := by
  let g (y : ℝ) := 2 * Real.sqrt Real.pi * Real.exp (-(Real.pi^2*x^2)*y^2)
  have hc : 0 < Real.pi^2*x^2 := mul_pos (sq_pos_of_pos Real.pi_pos) (sq_pos_of_ne_zero hx)
  have hg : IntegrableOn g (Ioi 0) :=
    ((integrable_exp_neg_mul_sq hc).const_mul _).integrableOn
  refine ((integrableOn_Ioi_comp_rpow_iff g (p := -1/2) (by norm_num)).mpr hg).congr_fun
    (fun t ht ↦ ?_) measurableSet_Ioi
  exact (heatKernel_rpow x t ht).symm

private lemma integral_heatKernel {x : ℝ} (hx : x ≠ 0) :
    (∫ t in Ioi (0 : ℝ), heatKernel x t) = |x|⁻¹ := by
  let g (y : ℝ) := 2 * Real.sqrt Real.pi * Real.exp (-(Real.pi^2*x^2)*y^2)
  calc
    _ = ∫ t in Ioi (0:ℝ), (|(-1/2:ℝ)| * t^((-1/2:ℝ)-1)) • g (t^(-1/2:ℝ)) := by
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ heatKernel_rpow x t ht
    _ = ∫ y in Ioi (0:ℝ), g y := integral_comp_rpow_Ioi g (by norm_num)
    _ = _ := by
      unfold g
      rw [integral_const_mul, integral_gaussian_Ioi, Real.sqrt_div Real.pi_pos.le,
        Real.sqrt_mul (sq_nonneg Real.pi), Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
        abs_of_pos Real.pi_pos]
      have hp := Real.sq_sqrt Real.pi_pos.le
      field_simp [Real.pi_ne_zero, abs_ne_zero.mpr hx]
      nlinarith


private lemma ae_ne_zero_real : ∀ᵐ x : ℝ ∂volume, x ≠ 0 := by simp [ae_iff]

private lemma integrable_div_abs_of_zero_at_zero (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    Integrable (fun x : ℝ ↦ f x / (|x| : ℝ)) := by
  let E := Icc (-1 : ℝ) 1
  let g (x : ℝ) : ℂ := f x / (|x| : ℝ)
  have hMeas : Measurable g := by
    unfold g
    exact f.continuous.measurable.div (Complex.continuous_ofReal.measurable.comp measurable_abs)
  let C := SchwartzMap.seminorm ℝ 0 1 f
  have hBound (x : ℝ) : ‖f x‖ ≤ C * |x| := by
    have hLe := Convex.norm_image_sub_le_of_norm_deriv_le
      (f := (f : ℝ → ℂ)) (s := univ) (C := C) (x := 0) (y := x)
      (fun y _ ↦ f.differentiable y) (fun y _ ↦ ?_) (convex_univ) (mem_univ _) (mem_univ _)
    · simpa only [hf, sub_zero, Real.norm_eq_abs] using hLe
    · rw [norm_deriv_eq_norm_fderiv, ← norm_iteratedFDeriv_one]
      exact SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ f 1 y
  have hNear : IntegrableOn g E := by
    refine (integrableOn_const (C := C) (by simp [E])).mono' hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_of_ae ae_ne_zero_real] with x hx
    rw [show ‖g x‖ = ‖f x‖ / |x| by simp only [g, norm_div, Complex.norm_real,
      Real.norm_eq_abs, abs_abs ] ]
    exact (div_le_iff₀ (abs_pos.mpr hx)).mpr (hBound x)
  have hFar : IntegrableOn g Eᶜ := by
    have hfFar : IntegrableOn (f : ℝ → ℂ) Eᶜ := f.integrable.integrableOn
    change Integrable g (volume.restrict Eᶜ)
    refine Integrable.mono' (f := g) hfFar.norm hMeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Icc.compl] with x hx
    dsimp [g]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have hx' : 1 < |x| := lt_of_not_ge fun he ↦ hx (abs_le.mp he)
    exact div_le_self (norm_nonneg _) hx'.le
  simpa only [union_compl_self, integrableOn_univ, g] using hNear.union hFar

private lemma logHeat_square_integral {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ t in Ioi (0 : ℝ), logHeat (ξ^2) t) = 2 * Real.log |ξ| := by
  rw [integral_logHeat (sq_pos_of_ne_zero hξ), Real.log_pow, Real.log_abs]
  norm_num

private lemma logHeat_square_abs_integral {ξ : ℝ} (hξ : ξ ≠ 0) :
    (∫ t in Ioi (0 : ℝ), |logHeat (ξ^2) t|) = 2 * |Real.log ξ| := by
  rw [integral_abs_logHeat (sq_pos_of_ne_zero hξ), ← integral_logHeat (sq_pos_of_ne_zero hξ),
    logHeat_square_integral hξ, Real.log_abs, abs_mul, abs_of_nonneg (by norm_num : 0 ≤ (2:ℝ))]

private lemma integrable_logHeat_fourier (f : 𝓢(ℝ, ℂ)) :
    Integrable (fun p : ℝ × ℝ ↦ 𝓕 (f : ℝ → ℂ) p.1 * (logHeat (p.1^2) p.2 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  let η : Measure ℝ := volume.restrict (Ioi 0)
  let F (p : ℝ × ℝ) : ℂ := (𝓕 f) p.1 * (logHeat (p.1^2) p.2 : ℂ)
  have hMeas : Measurable F := by
    unfold F logHeat
    apply ((𝓕 f).continuous.measurable.comp measurable_fst).mul
    apply Complex.continuous_ofReal.measurable.comp
    fun_prop
  have hI : Integrable F (volume.prod η) := by
    apply (integrable_prod_iff hMeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_ne_zero_real] with ξ hξ
      simpa only [F, η] using!
        ((integrableOn_logHeat (sq_pos_of_ne_zero hξ)).ofReal (𝕜 := ℂ)).const_mul ((𝓕 f) ξ)
    · refine (((integrable_log_mul_schwartz (𝓕 f)).norm.const_mul (2:ℝ))).congr ?_
      filter_upwards [ae_ne_zero_real] with ξ hξ
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, η,
        integral_const_mul, logHeat_square_abs_integral hξ, Real.log_abs]
      ring
  simpa only [F, η, SchwartzMap.fourier_coe] using hI

private lemma integral_logHeat_fourier (f : 𝓢(ℝ, ℂ)) :
    (∫ ξ : ℝ, ∫ t in Ioi (0 : ℝ), 𝓕 (f : ℝ → ℂ) ξ * (logHeat (ξ^2) t : ℂ)) =
      2 * realLogFourier f := by
  rw [realLogFourier, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_ne_zero_real] with ξ hξ
  rw [integral_const_mul]
  have hc : (∫ t in Ioi (0 : ℝ), (logHeat (ξ^2) t : ℂ)) = (↑(∫ t in Ioi (0 : ℝ), logHeat (ξ^2) t) : ℂ) := by
    exact integral_ofReal (𝕜 := ℂ)
  rw [hc, logHeat_square_integral hξ]
  push_cast
  ring


private lemma integrable_heatKernel_mul (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    Integrable (fun p : ℝ × ℝ ↦ f p.1 * (heatKernel p.1 p.2 : ℂ))
      (volume.prod (volume.restrict (Ioi 0))) := by
  let η : Measure ℝ := volume.restrict (Ioi 0)
  let F (p : ℝ × ℝ) : ℂ := f p.1 * (heatKernel p.1 p.2 : ℂ)
  have hMeas : Measurable F := by
    unfold F heatKernel realGaussFourier
    apply (f.continuous.measurable.comp measurable_fst).mul
    apply Complex.continuous_ofReal.measurable.comp
    fun_prop
  apply (integrable_prod_iff (f := F) (ν := η) hMeas.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [ae_ne_zero_real] with x hx
    simpa only [F, η] using!
      ((integrableOn_heatKernel hx).ofReal (𝕜 := ℂ)).const_mul (f x)
  · refine (integrable_div_abs_of_zero_at_zero f hf).norm.congr ?_
    filter_upwards [ae_ne_zero_real] with x hx
    dsimp only [F, η]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    have he : (∫ t in Ioi (0 : ℝ), ‖f x * (heatKernel x t : ℂ)‖) =
        ∫ t in Ioi (0 : ℝ), ‖f x‖ * heatKernel x t := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [norm_mul, Complex.norm_of_nonneg (heatKernel_nonneg x t ht)]
    rw [he, integral_const_mul, integral_heatKernel hx, div_eq_mul_inv]

private lemma integral_heatKernel_mul (f : 𝓢(ℝ, ℂ)) :
    (∫ x : ℝ, ∫ t in Ioi (0 : ℝ), f x * (heatKernel x t : ℂ)) =
      ∫ x : ℝ, f x / (|x| : ℝ) := by
  apply integral_congr_ae
  filter_upwards [ae_ne_zero_real] with x hx
  rw [integral_const_mul]
  have hc : (∫ t in Ioi (0 : ℝ), (heatKernel x t : ℂ)) =
      (↑(∫ t in Ioi (0 : ℝ), heatKernel x t) : ℂ) := by
    exact integral_ofReal (𝕜 := ℂ)
  rw [hc, integral_heatKernel hx, Complex.ofReal_inv, div_eq_mul_inv]

private lemma integral_logHeat_fourier_eq_neg_heatKernel_mul
    (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) {t : ℝ} (ht : 0 < t) :
    (∫ ξ : ℝ, 𝓕 (f : ℝ → ℂ) ξ * (logHeat (ξ^2) t : ℂ)) =
      -(∫ x : ℝ, f x * (heatKernel x t : ℂ)) := by
  let F := 𝓕 (f : ℝ → ℂ)
  let c : ℂ := Real.exp (-t)
  let G (ξ : ℝ) : ℂ := realGaussian t ξ
  have hF : Integrable F := by simpa only [F, SchwartzMap.fourier_coe] using (𝓕 f).integrable
  have hG : Integrable (fun ξ ↦ F ξ * G ξ) := by
    refine hF.mul_bdd (c := 1) ?_ ?_
    · have hMeas : Measurable G := by
        unfold G realGaussian
        exact Complex.continuous_ofReal.measurable.comp (by fun_prop)
      exact hMeas.aestronglyMeasurable
    · filter_upwards [] with ξ
      unfold G realGaussian
      rw [Complex.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht.le) (sq_nonneg _)
  have he : (fun ξ : ℝ ↦ F ξ * (logHeat (ξ^2) t : ℂ)) =
      fun ξ ↦ ((t : ℂ)⁻¹) * (F ξ * c - F ξ * G ξ) := by
    funext ξ
    unfold logHeat c G realGaussian
    push_cast
    have h : -((ξ : ℂ)^2*(t : ℂ)) = -(t : ℂ)*(ξ : ℂ)^2 := by ring
    rw [h]
    ring
  change (∫ ξ : ℝ, F ξ * (logHeat (ξ^2) t : ℂ)) =
    -(∫ x : ℝ, f x * (heatKernel x t : ℂ))
  rw [he, integral_const_mul, integral_sub (hF.mul_const c) hG, integral_mul_const]
  rw [show (∫ ξ : ℝ, F ξ) = 0 from (integral_fourier_schwartz_eq_value_zero f).trans hf]
  simp only [zero_mul, zero_sub, mul_neg]
  rw [show (∫ ξ : ℝ, F ξ * G ξ) = ∫ x : ℝ, f x * (realGaussFourier t x : ℂ)
    from integral_gaussFourier_mul_eq ht f, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  unfold heatKernel
  push_cast
  ring

/-- For a Schwartz test vanishing at zero, the self-dual real logarithmic Fourier
distribution equals minus one half of its integral against the absolute pole kernel. -/
theorem zero_value_pairing (f : 𝓢(ℝ, ℂ)) (hf : f 0 = 0) :
    realLogFourier f = -(2 : ℂ)⁻¹ * ∫ x : ℝ, f x / (|x| : ℝ) := by
  have h :
      2 * realLogFourier f = -(∫ x : ℝ, f x / (|x| : ℝ)) := by
    rw [← integral_logHeat_fourier f, integral_integral_swap (integrable_logHeat_fourier f)]
    have hI : (∫ t in Ioi (0:ℝ), ∫ ξ : ℝ,
        𝓕 (f : ℝ → ℂ) ξ * (logHeat (ξ^2) t : ℂ)) =
        -(∫ t in Ioi (0:ℝ), ∫ x : ℝ, f x * (heatKernel x t : ℂ)) := by
      rw [← integral_neg]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht ↦
        integral_logHeat_fourier_eq_neg_heatKernel_mul f hf ht
    rw [hI, ← integral_integral_swap (integrable_heatKernel_mul f hf), integral_heatKernel_mul]
  linear_combination (1 / 2 : ℂ) * h

end MasulloAudit

open MeasureTheory

theorem solution (f : SchwartzMap ℝ ℂ) (hf : f 0 = 0) :
    (∫ ξ : ℝ, (Real.log |ξ| : ℂ) * FourierTransform.fourier (f : ℝ → ℂ) ξ) =
      -(2 : ℂ)⁻¹ * ∫ x : ℝ, f x / (|x| : ℝ) := by
  exact MasulloAudit.zero_value_pairing f hf
