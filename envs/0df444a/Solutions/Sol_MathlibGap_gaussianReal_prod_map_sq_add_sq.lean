-- Prove2me | solution 1 for MathlibGap.gaussianReal_prod_map_sq_add_sq
-- status  : ACCEPTED   (prove)
-- author  : @domodus
-- created : 2026-11-26T15:15:17.745625+00:00
-- url     : https://prove2.me/submissions/fda6b67f-e67c-45e0-9fb8-b0929749dc52

import Mathlib

open MeasureTheory ProbabilityTheory Real Set

theorem solution (v : NNReal) (hv : v ≠ 0) :
    ((gaussianReal 0 v).prod (gaussianReal 0 v)).map (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) =
      (volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal
        (if 0 < x then (2 * (v : ℝ))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x) else 0)) := by
  have hv0 : (0 : ℝ) < v := by positivity
  set c : ℝ := (2 * (v : ℝ))⁻¹ with hc
  -- the joint density, written as a function of x² + y²
  set k : ℝ → ℝ := fun t => (2 * π * v)⁻¹ * Real.exp (-c * t) with hk
  have hmeas : Measurable (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2) := by fun_prop
  have hpdf : ∀ x y : ℝ, gaussianPDF 0 v x * gaussianPDF 0 v y =
      ENNReal.ofReal (k (x ^ 2 + y ^ 2)) := by
    intro x y
    rw [gaussianPDF, gaussianPDF, ← ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    congr 1
    simp only [gaussianPDFReal, hk, hc, sub_zero]
    have hs := Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ 2 * π * v)
    calc _ = ((√(2 * π * v)) * √(2 * π * v))⁻¹ *
          (rexp (-x ^ 2 / (2 * v)) * rexp (-y ^ 2 / (2 * v))) := by ring
      _ = _ := by rw [hs, ← Real.exp_add]; congr 2; ring
  refine Measure.ext_of_lintegral _ fun φ hφ => ?_
  set H : ℝ → ENNReal := fun t => ENNReal.ofReal (k t) * φ t with hH
  have hHm : Measurable H := (ENNReal.measurable_ofReal.comp (by rw [hk]; fun_prop)).mul hφ
  -- left side as an integral over the plane
  have hL : ∫⁻ t, φ t ∂(((gaussianReal 0 v).prod (gaussianReal 0 v)).map
      (fun p : ℝ × ℝ => p.1 ^ 2 + p.2 ^ 2)) = ∫⁻ p : ℝ × ℝ, H (p.1 ^ 2 + p.2 ^ 2) := by
    rw [lintegral_map hφ hmeas, gaussianReal_of_var_ne_zero _ hv,
      prod_withDensity (measurable_gaussianPDF _ _) (measurable_gaussianPDF _ _),
      ← Measure.volume_eq_prod]
    refine (lintegral_withDensity_eq_lintegral_mul _
        (((measurable_gaussianPDF _ _).comp measurable_fst).mul
          ((measurable_gaussianPDF _ _).comp measurable_snd)) (hφ.comp hmeas)).trans ?_
    refine lintegral_congr fun p => ?_
    simp only [Pi.mul_apply, Function.comp_apply, hH, hpdf]
  -- polar coordinates
  have hP : ∫⁻ p : ℝ × ℝ, H (p.1 ^ 2 + p.2 ^ 2) =
      ENNReal.ofReal (2 * π) * ∫⁻ r in Ioi 0, ENNReal.ofReal r * H (r ^ 2) := by
    rw [← lintegral_comp_polarCoord_symm, polarCoord_target, Measure.volume_eq_prod,
      ← Measure.prod_restrict]
    have hpt : ∀ p : ℝ × ℝ, ENNReal.ofReal p.1 •
        H ((polarCoord.symm p).1 ^ 2 + (polarCoord.symm p).2 ^ 2) =
        ENNReal.ofReal p.1 * H (p.1 ^ 2) * (fun _ : ℝ => (1 : ENNReal)) p.2 := by
      intro p
      simp only [polarCoord_symm_apply, smul_eq_mul, mul_one]
      rw [mul_pow, mul_pow, ← mul_add, cos_sq_add_sin_sq, mul_one]
    simp_rw [hpt]
    rw [lintegral_prod_mul (f := fun r : ℝ => ENNReal.ofReal r * H (r ^ 2))
        (g := fun _ : ℝ => (1 : ENNReal)) ((ENNReal.measurable_ofReal.comp measurable_id).mul
        (hHm.comp (measurable_id.pow_const 2))).aemeasurable aemeasurable_const,
      lintegral_one, Measure.restrict_apply_univ, Real.volume_Ioo, mul_comm]
    congr 2; ring
  -- substitution t = r²
  have hS : ∫⁻ r in Ioi 0, ENNReal.ofReal (2 * r) * H (r ^ 2) = ∫⁻ t in Ioi 0, H t := by
    have himg : (fun r : ℝ => r ^ 2) '' Ioi 0 = Ioi 0 := by
      ext t
      constructor
      · rintro ⟨r, hr, rfl⟩; exact pow_pos (show (0 : ℝ) < r from hr) 2
      · intro ht; exact ⟨√t, Real.sqrt_pos.2 ht, Real.sq_sqrt (le_of_lt ht)⟩
    rw [show (∫⁻ t in Ioi 0, H t) = ∫⁻ t in (fun r : ℝ => r ^ 2) '' Ioi 0, H t by rw [himg],
      lintegral_image_eq_lintegral_abs_deriv_mul measurableSet_Ioi
      (f' := fun r => 2 * r) (fun x _ => (by simpa using hasDerivAt_pow 2 x :
        HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x).hasDerivWithinAt)
      (fun a ha b hb h => (pow_left_inj₀ (le_of_lt ha) (le_of_lt hb) two_ne_zero).1 h)]
    refine setLIntegral_congr_fun measurableSet_Ioi (fun r hr => ?_)
    have hr' : (0 : ℝ) < r := hr
    rw [abs_of_pos (by positivity)]
  -- right side
  have hR : ∫⁻ t, φ t ∂((volume : Measure ℝ).withDensity (fun x => ENNReal.ofReal
        (if 0 < x then (2 * (v : ℝ))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x) else 0))) =
      ∫⁻ t in Ioi 0, ENNReal.ofReal π * H t := by
    have hfm : Measurable (fun x : ℝ => ENNReal.ofReal
        (if 0 < x then (2 * (v : ℝ))⁻¹ * Real.exp (-(2 * (v : ℝ))⁻¹ * x) else 0)) := by
      refine ENNReal.measurable_ofReal.comp (Measurable.ite (p := fun x : ℝ => 0 < x)
        measurableSet_Ioi ?_ measurable_const)
      fun_prop
    rw [lintegral_withDensity_eq_lintegral_mul _ hfm hφ, ← lintegral_indicator measurableSet_Ioi]
    refine lintegral_congr fun t => ?_
    by_cases ht : 0 < t
    · simp only [Pi.mul_apply, if_pos ht, indicator_of_mem (show t ∈ Ioi 0 from ht), hH,
        ← mul_assoc]
      rw [← ENNReal.ofReal_mul pi_pos.le]
      congr 2
      simp only [hk, hc]
      field_simp
    · simp [Pi.mul_apply, if_neg ht, indicator_of_notMem (show t ∉ Ioi 0 from ht)]
  rw [hL, hP, hR, lintegral_const_mul _ hHm, ← hS]
  simp_rw [ENNReal.ofReal_mul zero_le_two, mul_assoc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ring
