-- Prove2me | solution 1 for MomentSearch.rakhmanov_equilibrium_potential
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T23:59:11.696951+00:00
-- url     : https://prove2.me/submissions/4d99c2eb-9de5-4095-8fd3-610f7259eb12

import Mathlib
open Real Set MeasureTheory intervalIntegral Polynomial Metric
open scoped Real
private noncomputable def rootOffset (c : ℝ) : ℂ :=
  ⟨Real.sqrt (c ^ 2 - 1), Real.sqrt (1 - c ^ 2)⟩

private theorem rootOffset_sq (c : ℝ) : rootOffset c ^ 2 = ((c : ℂ) ^ 2 - 1) := by
  rcases le_or_gt (c ^ 2) 1 with h | h
  · have ha : Real.sqrt (c ^ 2 - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have hb := Real.sq_sqrt (show 0 ≤ 1 - c ^ 2 by linarith)
    simp only [pow_two] at ha hb
    apply Complex.ext
    · simp [rootOffset, pow_two, Complex.mul_re, ha]
      nlinarith only [hb]
    · simp [rootOffset, pow_two, Complex.mul_im, ha]
  · have hb : Real.sqrt (1 - c ^ 2) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
    have ha := Real.sq_sqrt (show 0 ≤ c ^ 2 - 1 by linarith)
    simp only [pow_two] at ha hb
    apply Complex.ext
    · simp [rootOffset, pow_two, Complex.mul_re, hb]
      nlinarith only [ha]
    · simp [rootOffset, pow_two, Complex.mul_im, hb]

private theorem arcsine_circle (b x : ℝ) (hb : 0 < b) :
    circleAverage (fun z : ℂ => Real.log |x - b * z.re|) 0 1 =
      Real.log (b / 2) +
        (log⁺ ‖(↑(x / b) : ℂ) + rootOffset (x / b)‖ +
          log⁺ ‖(↑(x / b) : ℂ) - rootOffset (x / b)‖) := by
  let c := x / b
  let u : ℂ := ↑c + rootOffset c
  let v : ℂ := ↑c - rootOffset c
  let B : ℂ := -(b : ℂ) / 2
  let P := C B * ((X - C u) * (X - C v))
  have hB : B ≠ 0 := by simp [B, hb.ne']
  have huv : u * v = 1 := by
    dsimp [u, v]
    calc
      _ = (c : ℂ) ^ 2 - rootOffset c ^ 2 := by ring
      _ = 1 := by rw [rootOffset_sq]; ring
  have huv' : u + v = 2 * (c : ℂ) := by dsimp [u,v]; ring
  have hc : (b : ℂ) * (c : ℂ) = x := by
    norm_cast
    dsimp [c]
    field_simp
  have havg : circleAverage (fun z : ℂ => Real.log |x - b * z.re|) 0 1 =
      P.logMahlerMeasure := by
    rw [logMahlerMeasure_def]
    apply circleAverage_congr_sphere
    intro z hz
    have hnorm : ‖z‖ = 1 := by simpa using hz
    have hzconj : z * (starRingEnd ℂ) z = 1 := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hnorm]
      norm_num
    have hp : P.eval z = z * (↑(x - b * z.re) : ℂ) := by
      simp only [P, eval_mul, eval_C, eval_sub, eval_X, Complex.ofReal_sub, Complex.ofReal_mul]
      have hprod : (z - u) * (z - v) = z ^ 2 - z * (u + v) + u * v := by ring
      rw [hprod, huv, huv', Complex.re_eq_add_conj]
      calc
        _ = z * (↑x - (b : ℂ) * ((z + (starRingEnd ℂ) z) / 2)) +
            ((b : ℂ) / 2) * (z * (starRingEnd ℂ) z - 1) := by
              dsimp [B]
              linear_combination (z * (hc))
        _ = _ := by rw [hzconj, sub_self, mul_zero, add_zero]
    change Real.log |x - b * z.re| = Real.log ‖P.eval z‖
    rw [hp, norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  rw [havg]
  dsimp [P]
  rw [logMahlerMeasure_C_mul hB (by simp [X_sub_C_ne_zero]),
    logMahlerMeasure_mul_eq_add_logMahlerMeasure (by simp [X_sub_C_ne_zero]),
    logMahlerMeasure_X_sub_C, logMahlerMeasure_X_sub_C]
  have hnorm : ‖B‖ = b / 2 := by
    simp [B, abs_of_pos hb]
  rw [hnorm]

private theorem arcsine_circle_eq (b x : ℝ) (hb : 0 < b) (hx : |x| ≤ b) :
    circleAverage (fun z : ℂ => Real.log |x - b * z.re|) 0 1 = Real.log (b / 2) := by
  rw [arcsine_circle b x hb]
  have hbound : |x / b| ≤ 1 := by
    rw [abs_div, abs_of_pos hb]
    exact (div_le_iff₀ hb).mpr (by simpa)
  have hsq : (x / b) ^ 2 ≤ 1 := by
    rw [← sq_abs]
    nlinarith [mul_nonneg (sub_nonneg.mpr hbound) (show 0 ≤ 1 + |x / b| by positivity)]
  have hoffset : Real.sqrt ((x / b) ^ 2 - 1) = 0 := Real.sqrt_eq_zero_of_nonpos (by linarith)
  have hrem := Real.sq_sqrt (show 0 ≤ 1 - (x / b) ^ 2 by linarith)
  have hplus : ‖(↑(x / b) : ℂ) + rootOffset (x / b)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [rootOffset, hoffset]
    nlinarith only [hrem]
  have hminus : ‖(↑(x / b) : ℂ) - rootOffset (x / b)‖ = 1 := by
    apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [rootOffset, hoffset]
    nlinarith only [hrem]
  rw [hplus, hminus]
  simp

private theorem arcsine_circle_le (b x : ℝ) (hb : 0 < b) :
    Real.log (b / 2) ≤ circleAverage (fun z : ℂ => Real.log |x - b * z.re|) 0 1 := by
  rw [arcsine_circle b x hb]
  linarith only [Real.posLog_nonneg (x := ‖(↑(x / b) : ℂ) + rootOffset (x / b)‖),
    Real.posLog_nonneg (x := ‖(↑(x / b) : ℂ) - rootOffset (x / b)‖)]

private theorem circle_to_half (b x : ℝ) :
    (∫ θ in (0 : ℝ)..Real.pi, Real.log |x - b * Real.cos θ|) =
      Real.pi * circleAverage (fun z : ℂ => Real.log |x - b * z.re|) 0 1 := by
  let g : ℝ → ℝ := fun t => Real.log (x - b * Real.cos t)
  have hg (l u : ℝ) : IntervalIntegrable g volume l u := by
    have h : AnalyticOnNhd ℝ (fun t => x - b * Real.cos t) (Set.uIcc l u) :=
      analyticOnNhd_const.sub (analyticOnNhd_const.mul Real.analyticOnNhd_cos)
    exact h.meromorphicOn.intervalIntegrable_log
  have hshift : (∫ θ in Real.pi..2 * Real.pi, g θ) = ∫ θ in 0..Real.pi, g θ := by
    have h := intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := Real.pi) g
      (2 * Real.pi)
    rw [show 2 * Real.pi - Real.pi = Real.pi by ring, sub_zero] at h
    simpa only [g, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, one_mul, zero_mul, add_zero]
      using h.symm
  rw [circleAverage_def]
  simp only [smul_eq_mul, Real.log_abs]
  have hcircle (θ : ℝ) : (circleMap (0 : ℂ) 1 θ).re = Real.cos θ := by
    simp [circleMap, Complex.exp_re]
  simp only [hcircle]
  change (∫ θ in 0..Real.pi, g θ) = Real.pi * ((2 * Real.pi)⁻¹ * ∫ θ in 0..2 * Real.pi, g θ)
  rw [← intervalIntegral.integral_add_adjacent_intervals (hg 0 Real.pi) (hg Real.pi (2*Real.pi)), hshift]
  field_simp [Real.pi_ne_zero]
  ring
private noncomputable def arcKernel (t s : ℝ) := (Real.sqrt (1 - t ^ 2 - s ^ 2))⁻¹

private theorem arcPrimitive (b c : ℝ) (hb : 0 < b) (hc : 0 ≤ c) (hcb : c ≤ b) :
    IntervalIntegrable (fun s => (Real.sqrt (b ^ 2 - s ^ 2))⁻¹) volume 0 c ∧
    (∫ s in (0 : ℝ)..c, (Real.sqrt (b ^ 2 - s ^ 2))⁻¹) = Real.arcsin (c / b) := by
  have hcont : Continuous (fun s : ℝ => Real.arcsin (s / b)) := by fun_prop
  have hderiv (s : ℝ) (hs : s ∈ Ioo 0 c) :
      HasDerivAt (fun s : ℝ => Real.arcsin (s / b)) (Real.sqrt (b ^ 2 - s ^ 2))⁻¹ s := by
    have hlt : s < b := hs.2.trans_le hcb
    have hs0 : 0 ≤ s := hs.1.le
    have hargs₁ : -1 < s / b := by linarith [div_nonneg hs0 hb.le]
    have hargs₂ : s / b < 1 := (div_lt_one hb).mpr hlt
    have h := (Real.hasDerivAt_arcsin hargs₁.ne' hargs₂.ne).comp s ((hasDerivAt_id' s).div_const b)
    have hrad : (1 : ℝ) - (s / b) ^ 2 = (b ^ 2 - s ^ 2) / b ^ 2 := by
      field_simp
    have hrad_pos : 0 < b ^ 2 - s ^ 2 := by
      nlinarith only [mul_pos (sub_pos.mpr hlt) (show 0 < b + s by positivity)]
    have he : 1 / Real.sqrt (1 - (s / b) ^ 2) * (1 / b) =
        (Real.sqrt (b ^ 2 - s ^ 2))⁻¹ := by
      rw [hrad, Real.sqrt_div hrad_pos.le, Real.sqrt_sq hb.le]
      field_simp [Real.sqrt_ne_zero'.mpr hrad_pos]
    change HasDerivAt (fun u : ℝ => Real.arcsin (u / b))
      (1 / Real.sqrt (1 - (s / b) ^ 2) * (1 / b)) s at h
    rwa [he] at h
  have hi : IntervalIntegrable (fun s => (Real.sqrt (b ^ 2 - s ^ 2))⁻¹) volume 0 c := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hc]
    exact integrableOn_deriv_of_nonneg hcont.continuousOn hderiv (fun _ _ => by positivity)
  refine ⟨hi, ?_⟩
  rw [integral_eq_sub_of_hasDerivAt_of_le hc hcont.continuousOn hderiv hi,
    zero_div, Real.arcsin_zero, sub_zero]

private theorem arcKernel_integral {t a : ℝ} (ht : t ∈ Ioo (-1 : ℝ) 1) (ha : 0 < a) :
    IntervalIntegrable (arcKernel t) volume 0 a ∧
    (∫ s in (0 : ℝ)..a, arcKernel t s) =
      Real.pi / 2 - Real.arctan (Real.sqrt (1 - a ^ 2 - t ^ 2) / a) := by
  let b := Real.sqrt (1 - t ^ 2)
  have hpos : 0 < 1 - t ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr ht.2) (show 0 < 1 + t by linarith [ht.1])]
  have hb : 0 < b := Real.sqrt_pos.mpr hpos
  have hb2 : b ^ 2 = 1 - t ^ 2 := Real.sq_sqrt hpos.le
  have hkernel : arcKernel t = (fun s => (Real.sqrt (b ^ 2 - s ^ 2))⁻¹) := by
    funext s
    simp [arcKernel, hb2]
  rcases lt_or_ge a b with hab | hab
  · obtain ⟨hi, he⟩ := arcPrimitive b a hb ha.le hab.le
    refine ⟨hkernel ▸ hi, ?_⟩
    rw [hkernel, he, Real.arcsin_eq_arctan (show a / b ∈ Ioo (-1 : ℝ) 1
      from ⟨by linarith [div_nonneg ha.le hb.le], (div_lt_one hb).mpr hab⟩)]
    have hrad : b ^ 2 - a ^ 2 = 1 - a ^ 2 - t ^ 2 := by rw [hb2]; ring
    have hrad_pos : 0 < b ^ 2 - a ^ 2 := by
      nlinarith only [mul_pos (sub_pos.mpr hab) (show 0 < b + a by positivity)]
    rw [show (1 : ℝ) - (a / b) ^ 2 = (b ^ 2 - a ^ 2) / b ^ 2 by field_simp,
      Real.sqrt_div hrad_pos.le, Real.sqrt_sq hb.le]
    rw [show a / b / (Real.sqrt (b ^ 2 - a ^ 2) / b) =
        (Real.sqrt (b ^ 2 - a ^ 2) / a)⁻¹ by field_simp [Real.sqrt_ne_zero'.mpr hrad_pos]]
    rw [Real.arctan_inv_of_pos (div_pos (Real.sqrt_pos.mpr hrad_pos) ha), hrad]
  · obtain ⟨hi, he⟩ := arcPrimitive b b hb hb.le le_rfl
    have hzero (s : ℝ) (hs : s ∈ Ioc b a) : arcKernel t s = 0 := by
      rw [hkernel]
      have hrad : b ^ 2 - s ^ 2 ≤ 0 := by
        nlinarith only [mul_nonneg (sub_nonneg.mpr hs.1.le) (show 0 ≤ s + b by linarith [hs.1])]
      change (Real.sqrt (b ^ 2 - s ^ 2))⁻¹ = 0
      rw [Real.sqrt_eq_zero_of_nonpos hrad, inv_zero]
    have hi' : IntervalIntegrable (arcKernel t) volume b a := by
      have hc : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume b a :=
        intervalIntegrable_const
      exact hc.congr (fun s hs => (hzero s (by simpa [uIoc_of_le hab] using hs)).symm)
    have hib : IntervalIntegrable (arcKernel t) volume 0 b := hkernel ▸ hi
    refine ⟨hib.trans hi', ?_⟩
    rw [← integral_add_adjacent_intervals hib hi']
    have hz : (∫ s in b..a, arcKernel t s) = 0 := by
      rw [integral_of_le hab]
      calc
        _ = ∫ _s in Ioc b a, (0 : ℝ) :=
          setIntegral_congr_fun measurableSet_Ioc hzero
        _ = 0 := by simp
    have hrad : 1 - a ^ 2 - t ^ 2 ≤ 0 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hab) (show 0 ≤ a + b by positivity), hb2]
    rw [hz, add_zero, hkernel, he, div_self hb.ne', Real.arcsin_one,
      Real.sqrt_eq_zero_of_nonpos hrad, zero_div, Real.arctan_zero, sub_zero]

private theorem arcKernel_cos (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) 1) (hs' : s < 1)
    (g : ℝ → ℝ) :
    (∫ t in (-1 : ℝ)..1, g t * arcKernel t s) =
      ∫ θ in (0 : ℝ)..Real.pi, g (Real.sqrt (1 - s ^ 2) * Real.cos θ) := by
  let b := Real.sqrt (1 - s ^ 2)
  have hpos : 0 < 1 - s ^ 2 := by
    nlinarith only [mul_pos (sub_pos.mpr hs') (show 0 < 1 + s by linarith [hs.1])]
  have hb : 0 < b := Real.sqrt_pos.mpr hpos
  have hb2 : b ^ 2 = 1 - s ^ 2 := Real.sq_sqrt hpos.le
  have hb1 : b ≤ 1 := by
    apply (sq_le_sq₀ hb.le zero_le_one).mp
    rw [hb2]
    nlinarith
  have hrestrict : (∫ t in (-1 : ℝ)..1, g t * arcKernel t s) =
      ∫ t in -b..b, g t * arcKernel t s := by
    rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      intervalIntegral.integral_of_le (by linarith : -b ≤ b)]
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioc
      (Set.Ioc_subset_Ioc (by linarith) hb1)
    intro t ht
    have ht' : ¬ t ∈ Set.Ioc (-b) b := ht.2
    have hbabs : b ≤ |t| := by
      rw [Set.mem_Ioc, not_and_or] at ht'
      rcases ht' with h | h
      · linarith [neg_le_abs t]
      · linarith [le_abs_self t]
    have hzero : 1 - t ^ 2 - s ^ 2 ≤ 0 := by
      have hsq := (sq_le_sq₀ hb.le (abs_nonneg t)).mpr hbabs
      rw [sq_abs] at hsq
      linarith
    simp [arcKernel, Real.sqrt_eq_zero_of_nonpos hzero]
  have hscale : (∫ t in -b..b, g t * arcKernel t s) =
      b * ∫ u in (-1 : ℝ)..1, g (b * u) * arcKernel (b * u) s := by
    simpa only [mul_neg, mul_one, smul_eq_mul] using
      (intervalIntegral.smul_integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
        (fun t => g t * arcKernel t s) b).symm
  have hcos := Polynomial.Chebyshev.integral_measureT_eq_integral_cos (f := fun u => g (b * u))
  rw [Polynomial.Chebyshev.integral_measureT] at hcos
  rw [hrestrict, hscale, ← intervalIntegral.integral_const_mul, ← hcos]
  apply intervalIntegral.integral_congr
  intro u hu
  have hroot : 1 - (b * u) ^ 2 - s ^ 2 = b ^ 2 * (1 - u ^ 2) := by
    rw [mul_sub, mul_one, mul_pow]
    linarith
  simp only [arcKernel, Real.sqrt_inv]
  rw [hroot, Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le, mul_inv_rev]
  calc
    _ = (b * b⁻¹) * (g (b * u) * (Real.sqrt (1 - u ^ 2))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hb.ne', one_mul]

private theorem uniform_log_integral (z : ℝ) :
    (∫ t in (-1 : ℝ)..1, Real.log |z - t|) =
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z)) - 2 := by
  simp_rw [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left Real.log z, integral_log,
    show z - -1 = 1 + z by ring, show z - 1 = -(1 - z) by ring, Real.log_neg_eq_log]
  ring

private theorem arc_mix (a z : ℝ) (ha : 0 < a) (ha' : a < 1) :
    let g : ℝ → ℝ := fun t => Real.log |z - t|
    let D : ℝ → ℝ := fun t => Real.pi / 2 -
      Real.arctan (Real.sqrt (1 - a ^ 2 - t ^ 2) / a)
    let J : ℝ → ℝ := fun s =>
      circleAverage (fun u : ℂ => Real.log |z - Real.sqrt (1 - s ^ 2) * u.re|) 0 1
    IntervalIntegrable J volume 0 a ∧
      (∫ t in (-1 : ℝ)..1, g t * D t) = Real.pi * ∫ s in (0 : ℝ)..a, J s := by
  intro g D J
  let μ : Measure ℝ := volume.restrict (Set.Ioc (-1) 1)
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 a)
  let F : ℝ × ℝ → ℝ := fun p => g p.1 * arcKernel p.1 p.2
  have hmeas : Measurable F := by unfold F g arcKernel; fun_prop
  have haet : ∀ᵐ t ∂μ, t ∈ Set.Ioo (-1 : ℝ) 1 := by
    dsimp [μ]
    rw [← restrict_Ioo_eq_restrict_Ioc]
    exact ae_restrict_mem measurableSet_Ioo
  have haes : ∀ᵐ s ∂ν, s ∈ Set.Ioc (0 : ℝ) a := ae_restrict_mem measurableSet_Ioc
  have hg : IntervalIntegrable g volume (-1) 1 := by
    have h : AnalyticOnNhd ℝ (fun t : ℝ => z - t) (Set.uIcc (-1) 1) :=
      analyticOnNhd_const.sub analyticOnNhd_id
    simpa only [g, Real.log_abs] using (show IntervalIntegrable (fun t : ℝ => Real.log (z - t)) volume (-1) 1 from
        h.meromorphicOn.intervalIntegrable_log)
  have hD : Continuous D := by unfold D; fun_prop
  have hgD : IntervalIntegrable (fun t => g t * D t) volume (-1) 1 :=
    hg.mul_continuousOn hD.continuousOn
  have hgDnorm : IntervalIntegrable (fun t => |g t| * D t) volume (-1) 1 :=
    hg.abs.mul_continuousOn hD.continuousOn
  have hF : Integrable F (μ.prod ν) := by
    apply (integrable_prod_iff hmeas.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [haet] with t ht
      exact ((intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mp
        (arcKernel_integral ht ha).1).const_mul (g t)
    · apply ((intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num : (-1 : ℝ) ≤ 1)).mp
          hgDnorm).congr
      filter_upwards [haet] with t ht
      have he := (arcKernel_integral ht ha).2
      rw [intervalIntegral.integral_of_le ha.le] at he
      symm
      calc
        _ = ∫ s, |g t| * arcKernel t s ∂ν := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards with s
          simp [F, Real.norm_eq_abs,
            abs_of_nonneg (show 0 ≤ arcKernel t s by unfold arcKernel; positivity)]
        _ = |g t| * D t := by rw [MeasureTheory.integral_const_mul]; rw [he]
  have hin (s : ℝ) (hs : s ∈ Set.Ioc (0 : ℝ) a) :
      (∫ t, F (t,s) ∂μ) = Real.pi * J s := by
    have hs' := hs.2.trans_lt ha'
    change (∫ t in Set.Ioc (-1 : ℝ) 1, g t * arcKernel t s) = _
    rw [← intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
      arcKernel_cos s ⟨hs.1, hs'.le⟩ hs']
    exact circle_to_half _ _
  have hJ : Integrable J ν := by
    have hi := (hF.swap.integral_prod_left).const_mul Real.pi⁻¹
    apply hi.congr
    filter_upwards [haes] with s hs
    change Real.pi⁻¹ * (∫ t, F (t,s) ∂μ) = _
    rw [hin s hs, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  refine ⟨(intervalIntegrable_iff_integrableOn_Ioc_of_le ha.le).mpr hJ, ?_⟩
  have hout (t : ℝ) (ht : t ∈ Set.Ioo (-1 : ℝ) 1) :
      (∫ s, F (t,s) ∂ν) = g t * D t := by
    change (∫ s in Set.Ioc (0 : ℝ) a, g t * arcKernel t s) = _
    rw [← intervalIntegral.integral_of_le ha.le, intervalIntegral.integral_const_mul,
      (arcKernel_integral ht ha).2]
  rw [intervalIntegral.integral_of_le (by norm_num : (-1 : ℝ) ≤ 1),
    intervalIntegral.integral_of_le ha.le]
  change (∫ t, g t * D t ∂μ) = Real.pi * ∫ s, J s ∂ν
  calc
    _ = ∫ t, ∫ s, F (t,s) ∂ν ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact haet.mono fun t ht => (hout t ht).symm
    _ = ∫ s, ∫ t, F (t,s) ∂μ ∂ν := integral_integral_swap hF
    _ = ∫ s, Real.pi * J s ∂ν := MeasureTheory.integral_congr_ae (haes.mono hin)
    _ = _ := MeasureTheory.integral_const_mul _ _

theorem solution (N k : ℕ) (hk : 1 ≤ k) (hkN : k < N) :
    let r := Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2)
    let ρ : ℝ → ℝ := fun t => (N : ℝ) / Real.pi * Real.arctan
      ((N : ℝ) / (k : ℝ) * Real.sqrt (r ^ 2 - t ^ 2))
    let L : ℝ → ℝ := fun z => ∫ t in (-1 : ℝ)..1, ρ t * Real.log |z - t|
    let V : ℝ → ℝ := fun z => (N : ℝ) / 2 *
      ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z))
    ∃ K : ℝ,
      (∀ x ∈ Set.Icc (-r) r, L x - V x = K) ∧
      (∀ z ∈ Set.Icc (-1 : ℝ) 1, L z - V z ≤ K) := by
  intro r ρ L V
  let a : ℝ := (k : ℝ) / (N : ℝ)
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have ha : 0 < a := div_pos hkpos hN
  have ha' : a < 1 := (div_lt_one hN).mpr (by exact_mod_cast hkN)
  have ha_sq : a ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha'.le) (show 0 ≤ 1 + a by positivity)]
  have hr2 : r ^ 2 = 1 - a ^ 2 := by
    change Real.sqrt (1 - (k : ℝ) ^ 2 / (N : ℝ) ^ 2) ^ 2 = _
    rw [← div_pow, Real.sq_sqrt (sub_nonneg.mpr ha_sq)]
  have hρ : Continuous ρ := by unfold ρ; fun_prop
  let B : ℝ → ℝ := fun s => Real.sqrt (1 - s ^ 2)
  let base : ℝ → ℝ := fun s => Real.log (B s / 2)
  let J (z : ℝ) : ℝ → ℝ := fun s =>
    circleAverage (fun u : ℂ => Real.log |z - B s * u.re|) 0 1
  have hB (s : ℝ) (hs : s ∈ Icc (0 : ℝ) a) : 0 < B s := by
    have hsa := hs.2.trans_lt ha'
    apply Real.sqrt_pos.mpr
    nlinarith only [mul_pos (sub_pos.mpr hsa) (show 0 < 1 + s by linarith [hs.1])]
  have hBase : IntervalIntegrable base volume 0 a := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le ha.le]
    have hcont : Continuous (fun s => B s / 2) := by unfold B; fun_prop
    exact Real.continuousOn_log.comp hcont.continuousOn
      (fun s hs => (div_pos (hB s hs) (by norm_num)).ne')
  have hmixed (z : ℝ) :
      IntervalIntegrable (J z) volume 0 a ∧
        L z - V z = -(N : ℝ) - (N : ℝ) * ∫ s in (0 : ℝ)..a, J z s := by
    let g : ℝ → ℝ := fun t => Real.log |z - t|
    let D : ℝ → ℝ := fun t => Real.pi / 2 -
      Real.arctan (Real.sqrt (1 - a ^ 2 - t ^ 2) / a)
    obtain ⟨hJ, hIdentity⟩ := arc_mix a z ha ha'
    change (∫ t in (-1 : ℝ)..1, g t * D t) = Real.pi * ∫ s in (0 : ℝ)..a, J z s at hIdentity
    refine ⟨hJ, ?_⟩
    have hcoef (t : ℝ) : (N : ℝ) / 2 - ρ t = (N : ℝ) / Real.pi * D t := by
      have hratio : (N : ℝ) / (k : ℝ) = a⁻¹ := by simp [a]
      dsimp only [D, ρ]
      rw [hr2, hratio, ← div_eq_inv_mul]
      field_simp [Real.pi_ne_zero]
    have hweighted :
        (∫ t in (-1 : ℝ)..1, ((N : ℝ) / 2 - ρ t) * g t) =
          (N : ℝ) * ∫ s in (0 : ℝ)..a, J z s := by
      calc
        _ = ((N : ℝ) / Real.pi) * ∫ t in (-1 : ℝ)..1, g t * D t := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro t _
          change ((N : ℝ) / 2 - ρ t) * g t = ((N : ℝ) / Real.pi) * (g t * D t)
          rw [hcoef t]
          ring
        _ = _ := by rw [hIdentity]; field_simp [Real.pi_ne_zero]
    have hg : IntervalIntegrable g volume (-1) 1 := by
      have h : AnalyticOnNhd ℝ (fun t : ℝ => z - t) (Set.uIcc (-1) 1) :=
        analyticOnNhd_const.sub analyticOnNhd_id
      simpa only [g, Real.log_abs] using (show IntervalIntegrable
        (fun t : ℝ => Real.log (z - t)) volume (-1) 1 from h.meromorphicOn.intervalIntegrable_log)
    have hρg : IntervalIntegrable (fun t => ρ t * g t) volume (-1) 1 :=
      hg.continuousOn_mul hρ.continuousOn
    simp only [sub_mul] at hweighted
    rw [intervalIntegral.integral_sub (hg.const_mul _) hρg,
      intervalIntegral.integral_const_mul, uniform_log_integral z] at hweighted
    change (N : ℝ) / 2 * ((1 + z) * Real.log (1 + z) + (1 - z) * Real.log (1 - z) - 2) -
      L z = _ at hweighted
    dsimp only [V]
    nlinarith only [hweighted]
  refine ⟨-(N : ℝ) - (N : ℝ) * ∫ s in (0 : ℝ)..a, base s, ?_, ?_⟩
  · intro x hx
    rw [(hmixed x).2]
    congr 1
    congr 1
    apply intervalIntegral.integral_congr
    intro s hs
    rw [uIcc_of_le ha.le] at hs
    have hxs : |x| ≤ B s := by
      apply (abs_le.mpr hx).trans
      have hsr : s ^ 2 ≤ a ^ 2 := (sq_le_sq₀ hs.1 ha.le).mpr hs.2
      change Real.sqrt _ ≤ Real.sqrt _
      apply Real.sqrt_le_sqrt
      rw [← div_pow]
      linarith
    exact arcsine_circle_eq _ _ (hB s hs) hxs
  · intro z _
    rw [(hmixed z).2]
    have hJ : (∫ s in (0 : ℝ)..a, base s) ≤ ∫ s in (0 : ℝ)..a, J z s :=
      intervalIntegral.integral_mono_on ha.le hBase (hmixed z).1
        (fun s hs => arcsine_circle_le _ _ (hB s hs))
    exact sub_le_sub_left (mul_le_mul_of_nonneg_left hJ hN.le) _
