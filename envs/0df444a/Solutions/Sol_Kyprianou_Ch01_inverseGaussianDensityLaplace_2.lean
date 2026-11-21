-- Prove2me | solution 2 for Kyprianou.Ch01.inverseGaussianDensityLaplace
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T02:12:45.448186+00:00
-- url     : https://prove2.me/submissions/e3c970b9-0253-42f3-9f95-d8781c82d8cc

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

/-- The Glasser-type Gaussian integral
`∫_0^∞ exp(-a y² - c/y²) dy = (√π / (2√a)) exp(-2√(ac))` for `a, c > 0`. -/
lemma gaussian_core (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ y in Set.Ioi (0 : ℝ),
      Real.exp (-a * y ^ 2 - c / y ^ 2) ∂volume) =
    (Real.sqrt Real.pi / (2 * Real.sqrt a)) *
      Real.exp (-2 * Real.sqrt (a * c)) := by
  set k : ℝ := Real.sqrt (c / a) with hkdef
  set α : ℝ := Real.sqrt (a * c) with hαdef
  have hk : 0 < k := by
    rw [hkdef]
    exact Real.sqrt_pos_of_pos (div_pos hc ha)
  have hαpos : 0 < α := by
    rw [hαdef]
    exact Real.sqrt_pos_of_pos (mul_pos ha hc)
  have hk2 : k ^ 2 = c / a := by
    rw [hkdef]
    exact Real.sq_sqrt (div_nonneg hc.le ha.le)
  have hak2 : a * k ^ 2 = c := by
    rw [hk2]
    field_simp
  have hak : a * k = α := by
    have hsq : (a * k) ^ 2 = α ^ 2 := by
      rw [mul_pow, hk2, hαdef, Real.sq_sqrt (mul_nonneg ha.le hc.le)]
      field_simp
    have hnn : 0 ≤ a * k := mul_nonneg ha.le hk.le
    calc a * k = Real.sqrt ((a * k) ^ 2) := (Real.sqrt_sq hnn).symm
      _ = Real.sqrt (α ^ 2) := by rw [hsq]
      _ = α := Real.sqrt_sq hαpos.le
  have hexp : ∀ y ∈ Ioi (0 : ℝ),
      -a * y ^ 2 - c / y ^ 2 = -2 * α + -a * (y - k / y) ^ 2 := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    field_simp
    nlinarith [hak2, hak]
  have hstep1 : (∫ y in Ioi (0 : ℝ), Real.exp (-a * y ^ 2 - c / y ^ 2)) =
      Real.exp (-2 * α) * ∫ y in Ioi (0 : ℝ), Real.exp (-a * (y - k / y) ^ 2) := by
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    try dsimp only
    rw [← Real.exp_add]
    congr 1
    exact hexp y hy
  have hderiv1_at : ∀ y : ℝ, 0 < y →
      HasDerivAt (fun y : ℝ => k / y) (-k / y ^ 2) y := by
    intro y hy
    have hy0 : y ≠ 0 := ne_of_gt hy
    have h0 := (hasDerivAt_const (x := y) (c := k)).div (hasDerivAt_id y) hy0
    have heq : (0 * y - k * 1) / y ^ 2 = -k / y ^ 2 := by
      field_simp
      ring
    have h1 : HasDerivAt ((fun x : ℝ => k) / id) (-k / y ^ 2) y := by
      simpa only [id_eq, Pi.div_apply, heq] using h0
    exact h1
  have hderiv1 : ∀ y ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => k / y) (-k / y ^ 2) (Ioi (0 : ℝ)) y :=
    fun y hy => (hderiv1_at y hy).hasDerivWithinAt
  have hderiv_f : ∀ y ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun y : ℝ => y - k / y) (1 + k / y ^ 2) (Ioi (0 : ℝ)) y := by
    intro y hy
    have h2 : HasDerivAt (fun y : ℝ => y - k / y) (1 - (-k / y ^ 2)) y :=
      (hasDerivAt_id y).sub (hderiv1_at y hy)
    have heq : 1 - (-k / y ^ 2) = 1 + k / y ^ 2 := by
      field_simp
      ring
    rw [heq] at h2
    exact h2.hasDerivWithinAt
  have hinj_f : InjOn (fun y : ℝ => y - k / y) (Ioi (0 : ℝ)) := by
    intro y1 hy1 y2 hy2 h
    have hy1' : 0 < y1 := hy1
    have hy2' : 0 < y2 := hy2
    have h1 : 0 < 1 + k / (y1 * y2) := by positivity
    have hkey : y1 - y2 = -(k * (y1 - y2) / (y1 * y2)) := by
      have h' : y1 - k / y1 = y2 - k / y2 := h
      have hsub : k / y1 - k / y2 = -(k * (y1 - y2) / (y1 * y2)) := by
        field_simp
        ring
      linarith
    have hd : k * (y1 - y2) / (y1 * y2) = -(y1 - y2) := by
      linarith
    have h2 : (y1 - y2) * (1 + k / (y1 * y2)) = 0 := by
      have hsplit : (y1 - y2) * (1 + k / (y1 * y2)) =
          (y1 - y2) + k * (y1 - y2) / (y1 * y2) := by
        field_simp
      rw [hsplit, hd]
      ring
    have h3 : y1 - y2 = 0 := by
      rcases mul_eq_zero.mp h2 with h4 | h4
      · exact h4
      · exact absurd h4 (ne_of_gt h1)
    linarith
  have himage_f : (fun y : ℝ => y - k / y) '' Ioi (0 : ℝ) = univ := by
    ext t
    simp only [mem_image, mem_Ioi, mem_univ, iff_true]
    have hs2 : Real.sqrt (t ^ 2 + 4 * k) ^ 2 = t ^ 2 + 4 * k :=
      Real.sq_sqrt (by positivity)
    have hlt : |t| < Real.sqrt (t ^ 2 + 4 * k) := by
      rw [Real.lt_sqrt (abs_nonneg t), sq_abs]
      linarith
    have hpos : 0 < (t + Real.sqrt (t ^ 2 + 4 * k)) / 2 := by
      have := neg_abs_le t
      linarith
    set y : ℝ := (t + Real.sqrt (t ^ 2 + 4 * k)) / 2 with hydef
    have hypos : 0 < y := by rw [hydef]; exact hpos
    refine ⟨y, hypos, ?_⟩
    have hyne : y ≠ 0 := ne_of_gt hypos
    have hsq : y ^ 2 = t * y + k := by
      rw [hydef]
      field_simp
      nlinarith [hs2]
    field_simp
    nlinarith [hsq]
  have hsub : (∫ y in Ioi (0 : ℝ), (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2)) =
      ∫ t, Real.exp (-a * t ^ 2) := by
    have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun y : ℝ => y - k / y) (f' := fun y : ℝ => 1 + k / y ^ 2)
      (g := fun t : ℝ => Real.exp (-a * t ^ 2)) measurableSet_Ioi hderiv_f hinj_f
    rw [himage_f, setIntegral_univ] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    try dsimp only
    have hy' : 0 < y := hy
    have hpos : (0 : ℝ) < 1 + k / y ^ 2 := by positivity
    rw [abs_of_pos hpos]
    simp only [smul_eq_mul]
  have hIntW : IntegrableOn (fun y : ℝ => (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2))
      (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn (fun t : ℝ => Real.exp (-a * t ^ 2)) univ := by
      simpa using (integrable_exp_neg_mul_sq ha)
    have hiff := (integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun y : ℝ => y - k / y) (f' := fun y : ℝ => 1 + k / y ^ 2)
      (g := fun t : ℝ => Real.exp (-a * t ^ 2)) measurableSet_Ioi hderiv_f hinj_f).mp
      (by rwa [himage_f])
    convert hiff using 1
    ext y
    try dsimp only
    have hpos : (0 : ℝ) < 1 + k / y ^ 2 := by positivity
    rw [abs_of_pos hpos]
    simp only [smul_eq_mul]
  have hIntA : IntegrableOn (fun y : ℝ => Real.exp (-a * (y - k / y) ^ 2)) (Ioi (0 : ℝ)) := by
    rw [IntegrableOn] at hIntW ⊢
    refine hIntW.mono' ?_ ?_
    · exact Measurable.aestronglyMeasurable (by measurability)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      have hy' : 0 < y := hy
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hk2y : 0 ≤ k / y ^ 2 := by positivity
      have hle : Real.exp (-a * (y - k / y) ^ 2) ≤
          (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2) := by
        have hone : (1 : ℝ) ≤ 1 + k / y ^ 2 := by linarith
        calc Real.exp (-a * (y - k / y) ^ 2)
            = 1 * Real.exp (-a * (y - k / y) ^ 2) := (one_mul _).symm
          _ ≤ (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2) := by
              exact mul_le_mul_of_nonneg_right hone (Real.exp_pos _).le
      exact hle
  have hIntB : IntegrableOn (fun y : ℝ => (k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2))
      (Ioi (0 : ℝ)) := by
    rw [IntegrableOn] at hIntW ⊢
    refine hIntW.mono' ?_ ?_
    · exact Measurable.aestronglyMeasurable (by measurability)
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with y hy
      have hy' : 0 < y := hy
      have hk2y : 0 ≤ k / y ^ 2 := by positivity
      have hexp : 0 ≤ Real.exp (-a * (y - k / y) ^ 2) := (Real.exp_pos _).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hk2y hexp)]
      have hone : (k / y ^ 2) ≤ 1 + k / y ^ 2 := by linarith
      exact mul_le_mul_of_nonneg_right hone hexp
  have hinv : (∫ y in Ioi (0 : ℝ), Real.exp (-a * (y - k / y) ^ 2)) =
      ∫ y in Ioi (0 : ℝ), (k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2) := by
    have hinj_g : InjOn (fun y : ℝ => k / y) (Ioi (0 : ℝ)) := by
      intro y1 hy1 y2 hy2 h
      have hk0 : k ≠ 0 := ne_of_gt hk
      have hy1' : 0 < y1 := hy1
      have hy2' : 0 < y2 := hy2
      have h2 : k * y2 = k * y1 := by
        have h3 : k / y1 = k / y2 := h
        rwa [div_eq_div_iff (ne_of_gt hy1') (ne_of_gt hy2')] at h3
      exact (mul_left_cancel₀ hk0 h2).symm
    have himage_g : (fun y : ℝ => k / y) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
      ext u
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact div_pos hk hy
      · intro hu
        refine ⟨k / u, div_pos hk hu, ?_⟩
        have hk0 : k ≠ 0 := ne_of_gt hk
        have hu0 : u ≠ 0 := ne_of_gt hu
        field_simp
    have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
      (f := fun y : ℝ => k / y) (f' := fun y : ℝ => -k / y ^ 2)
      (g := fun u : ℝ => Real.exp (-a * (u - k / u) ^ 2)) measurableSet_Ioi hderiv1 hinj_g
    rw [himage_g] at h
    rw [h]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    try dsimp only
    have hy' : 0 < y := hy
    have hneg : -k / y ^ 2 < 0 := by
      have hpos : (0 : ℝ) < k / y ^ 2 := by positivity
      rw [neg_div]
      linarith
    rw [abs_of_neg hneg]
    have hkk : k / (k / y) = y := by
      have hk0 : k ≠ 0 := ne_of_gt hk
      have hy0 : y ≠ 0 := ne_of_gt hy'
      field_simp
    rw [hkk]
    simp only [smul_eq_mul]
    have hs : -(-k / y ^ 2) = k / y ^ 2 := by ring
    rw [hs]
    congr 1
    congr 1
    ring
  have h2J : 2 * (∫ y in Ioi (0 : ℝ), Real.exp (-a * (y - k / y) ^ 2)) =
      ∫ y in Ioi (0 : ℝ), (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2) := by
    have happ : (∫ y in Ioi (0 : ℝ), (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2)) =
        (∫ y in Ioi (0 : ℝ), Real.exp (-a * (y - k / y) ^ 2)) +
        (∫ y in Ioi (0 : ℝ), (k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2)) := by
      rw [← integral_add hIntA hIntB]
      apply setIntegral_congr_fun measurableSet_Ioi
      intro y hy
      ring
    rw [happ, ← hinv]
    ring
  have hWval : (∫ y in Ioi (0 : ℝ), (1 + k / y ^ 2) * Real.exp (-a * (y - k / y) ^ 2)) =
      Real.sqrt (Real.pi / a) := by
    rw [hsub]
    exact integral_gaussian a
  have hJ : (∫ y in Ioi (0 : ℝ), Real.exp (-a * (y - k / y) ^ 2)) =
      Real.sqrt (Real.pi / a) / 2 := by
    have h := h2J
    rw [hWval] at h
    linarith
  have hmain : (∫ y in Ioi (0 : ℝ), Real.exp (-a * y ^ 2 - c / y ^ 2)) =
      Real.exp (-2 * α) * (Real.sqrt (Real.pi / a) / 2) := by
    rw [hstep1, hJ]
  have hsqrt : Real.sqrt (Real.pi / a) = Real.sqrt Real.pi / Real.sqrt a :=
    Real.sqrt_div' Real.pi ha.le
  rw [hmain, hαdef, hsqrt]
  ring

/-! ## The reciprocal (Bessel-type) integral -/

lemma sqrt_three_halves (x : ℝ) (hx : 0 < x) :
    Real.sqrt (x ^ 3) = x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast (x := x) (n := 3), ← Real.rpow_mul hx.le]
  congr 1
  norm_num

lemma reciprocal_smul_eq (a c u : ℝ) (hu : 0 < u) :
    |(-2 : ℝ) / u ^ 3| •
        (((u ^ 2)⁻¹) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(a / ((u ^ 2)⁻¹)) - c * ((u ^ 2)⁻¹))) =
      2 * Real.exp (-a * u ^ 2 - c / u ^ 2) := by
  have hu0 : u ≠ 0 := ne_of_gt hu
  have hpow : (((u ^ 2)⁻¹) ^ (-(3 / 2 : ℝ))) = u ^ 3 := by
    have h1 : (u ^ 2)⁻¹ = u ^ (-(2 : ℝ)) := by
      rw [← Real.rpow_natCast (x := u) (n := 2), ← Real.rpow_neg hu.le]
      congr 1
    rw [h1, ← Real.rpow_mul hu.le]
    rw [show (-(2 : ℝ)) * (-(3 / 2 : ℝ)) = 3 by norm_num]
    exact Real.rpow_natCast u 3
  have hdiv : a / ((u ^ 2)⁻¹) = a * u ^ 2 := by
    field_simp
  have hneg : (-2 : ℝ) / u ^ 3 < 0 := by
    have h : (0 : ℝ) < 2 / u ^ 3 := by positivity
    have he : (-2 : ℝ) / u ^ 3 = -(2 / u ^ 3) := by ring
    rw [he]
    linarith
  have habs : |(-2 : ℝ) / u ^ 3| = 2 / u ^ 3 := by
    rw [abs_of_neg hneg]
    ring
  rw [habs, hpow, hdiv, smul_eq_mul]
  have hdiv2 : c * ((u ^ 2)⁻¹) = c / u ^ 2 := by
    rw [div_eq_mul_inv]
  rw [hdiv2]
  field_simp

lemma reciprocal_core (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    (∫ x in Set.Ioi (0 : ℝ), (x ^ (-(3 / 2 : ℝ))) * Real.exp (-(a / x) - c * x) ∂volume) =
    (Real.sqrt Real.pi / Real.sqrt a) * Real.exp (-2 * Real.sqrt (a * c)) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => (u ^ 2)⁻¹) (-2 / u ^ 3) (Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h2 := h1.inv (pow_ne_zero 2 hu0)
    have heq : -(2 * u) / (u ^ 2) ^ 2 = -2 / u ^ 3 := by
      field_simp
    rw [heq] at h2
    exact h2.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
    intro u1 hu1 u2 hu2 h
    have hu1' : 0 < u1 := hu1
    have hu2' : 0 < u2 := hu2
    have hsq : u1 ^ 2 = u2 ^ 2 := inv_inj.mp h
    have hfac : (u1 - u2) * (u1 + u2) = 0 := by nlinarith [hsq]
    have hpos : 0 < u1 + u2 := by linarith
    have hzero : u1 - u2 = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact h'
      · linarith
    linarith
  have himage : (fun u : ℝ => (u ^ 2)⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact inv_pos.mpr (pow_pos (show (0 : ℝ) < u from hu) 2)
    · intro hx
      refine ⟨(Real.sqrt x)⁻¹, ?_, ?_⟩
      · exact inv_pos.mpr (Real.sqrt_pos_of_pos hx)
      · dsimp only
        rw [inv_pow, Real.sq_sqrt hx.le, inv_inv]
  have h := integral_image_eq_integral_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun u : ℝ => (u ^ 2)⁻¹) (f' := fun u : ℝ => -2 / u ^ 3)
    (g := fun x : ℝ => x ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / x) - c * x))
    measurableSet_Ioi hderiv hinj
  rw [himage] at h
  rw [h]
  rw [show (∫ u in Ioi (0 : ℝ), |(-2 : ℝ) / u ^ 3| •
        (((u ^ 2)⁻¹) ^ (-(3 / 2 : ℝ)) *
          Real.exp (-(a / ((u ^ 2)⁻¹)) - c * ((u ^ 2)⁻¹))))
      = ∫ u in Ioi (0 : ℝ), 2 * Real.exp (-a * u ^ 2 - c / u ^ 2) from by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro u hu
        exact reciprocal_smul_eq a c u hu]
  rw [integral_const_mul]
  rw [gaussian_core a c ha hc]
  ring

lemma sqrt_two_pi_mul (x : ℝ) (hx : 0 < x) :
    Real.sqrt (2 * Real.pi * x ^ 3) = Real.sqrt (2 * Real.pi) * x ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_mul (by positivity), sqrt_three_halves x hx]

lemma reciprocal_integrable (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / x) - c * x))
      (Ioi (0 : ℝ)) := by
  have hderiv : ∀ u ∈ Ioi (0 : ℝ),
      HasDerivWithinAt (fun u : ℝ => (u ^ 2)⁻¹) (-2 / u ^ 3) (Ioi (0 : ℝ)) u := by
    intro u hu
    have hu0 : u ≠ 0 := ne_of_gt hu
    have h1 : HasDerivAt (fun u : ℝ => u ^ 2) (2 * u) u := by
      simpa using hasDerivAt_pow 2 u
    have h2 := h1.inv (pow_ne_zero 2 hu0)
    have heq : -(2 * u) / (u ^ 2) ^ 2 = -2 / u ^ 3 := by
      field_simp
    rw [heq] at h2
    exact h2.hasDerivWithinAt
  have hinj : InjOn (fun u : ℝ => (u ^ 2)⁻¹) (Ioi (0 : ℝ)) := by
    intro u1 hu1 u2 hu2 h
    have hu1' : 0 < u1 := hu1
    have hu2' : 0 < u2 := hu2
    have hsq : u1 ^ 2 = u2 ^ 2 := inv_inj.mp h
    have hfac : (u1 - u2) * (u1 + u2) = 0 := by nlinarith [hsq]
    have hpos : 0 < u1 + u2 := by linarith
    have hzero : u1 - u2 = 0 := by
      rcases mul_eq_zero.mp hfac with h' | h'
      · exact h'
      · linarith
    linarith
  have himage : (fun u : ℝ => (u ^ 2)⁻¹) '' Ioi (0 : ℝ) = Ioi (0 : ℝ) := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact inv_pos.mpr (pow_pos (show (0 : ℝ) < u from hu) 2)
    · intro hx
      refine ⟨(Real.sqrt x)⁻¹, ?_, ?_⟩
      · exact inv_pos.mpr (Real.sqrt_pos_of_pos hx)
      · dsimp only
        rw [inv_pow, Real.sq_sqrt hx.le, inv_inv]
  have hbase : IntegrableOn (fun u : ℝ => 2 * Real.exp (-a * u ^ 2 - c / u ^ 2))
      (Ioi (0 : ℝ)) := by
    have hg : IntegrableOn (fun u : ℝ => Real.exp (-a * u ^ 2)) (Ioi (0 : ℝ)) :=
      (integrable_exp_neg_mul_sq ha).integrableOn
    have hc' : IntegrableOn (fun u : ℝ => Real.exp (-a * u ^ 2 - c / u ^ 2))
        (Ioi (0 : ℝ)) := by
      rw [IntegrableOn] at hg ⊢
      refine hg.mono' ?_ ?_
      · exact Measurable.aestronglyMeasurable (by measurability)
      · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        apply Real.exp_le_exp.mpr
        have hcu : 0 ≤ c / u ^ 2 := by positivity
        linarith
    exact hc'.const_mul 2
  have hiff := integrableOn_image_iff_integrableOn_abs_deriv_smul (s := Ioi (0 : ℝ))
    (f := fun u : ℝ => (u ^ 2)⁻¹) (f' := fun u : ℝ => -2 / u ^ 3)
    (g := fun x : ℝ => x ^ (-(3 / 2 : ℝ)) * Real.exp (-(a / x) - c * x))
    measurableSet_Ioi hderiv hinj
  rw [himage] at hiff
  rw [hiff]
  refine hbase.congr_fun ?_ measurableSet_Ioi
  intro u hu
  exact (reciprocal_smul_eq a c u hu).symm

/-! ## Density helpers -/

lemma density_factor (s b x : ℝ) (hx : 0 < x) :
    (s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x))) =
      (s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) *
        (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x)) := by
  have hsqrt := sqrt_two_pi_mul x hx
  have hexp : Real.exp (-((s - b * x) ^ 2 / (2 * x))) =
      Real.exp (s * b) * Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [hsqrt, hexp, Real.rpow_neg hx.le]
  have h1 : (0 : ℝ) < Real.sqrt (2 * Real.pi) := Real.sqrt_pos_of_pos (by positivity)
  have h2 : (0 : ℝ) < x ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  field_simp

lemma density_nonneg (s b x : ℝ) (hs : 0 < s) (hx : 0 < x) :
    0 ≤ (s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x))) := by
  have h1 : (0 : ℝ) < Real.sqrt (2 * Real.pi * x ^ 3) := Real.sqrt_pos_of_pos (by positivity)
  positivity

lemma density_laplace_factor (s b q x : ℝ) (hx : 0 < x) :
    Real.exp (-q * x) *
        ((s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x)))) =
      ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b)) *
        (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x)) := by
  rw [density_factor s b x hx]
  have hexp2 : Real.exp (-q * x) * Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x) =
      Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x) := by
    rw [← Real.exp_add]
    congr 1
    field_simp
    ring
  calc Real.exp (-q * x) *
        ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) *
          (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x)))
      = ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b)) *
          (x ^ (-(3 / 2 : ℝ)) *
            (Real.exp (-q * x) * Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x))) := by ring
    _ = ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b)) *
          (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x)) := by
        rw [hexp2]

/-! ## Mass one -/

theorem thm_mass (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 := by
  dsimp only
  set w : ℝ → ℝ := fun x : ℝ =>
    (s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x))) with hwdef
  set c0 : ℝ := (s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) with hc0def
  have hIntOn : IntegrableOn w (Ioi (0 : ℝ)) := by
    have hR : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x)) (Ioi (0 : ℝ)) :=
      reciprocal_integrable (s ^ 2 / 2) (b ^ 2 / 2) (by positivity) (by positivity)
    have h := hR.const_mul c0
    refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
    intro x hx
    rw [show w x = c0 * (x ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x)) from density_factor s b x hx]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] w := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    exact density_nonneg s b x hs hx
  have hIntegral : (∫ x in Ioi (0 : ℝ), w x) = 1 := by
    have hfac : (∫ x in Ioi (0 : ℝ), w x) =
        ∫ x in Ioi (0 : ℝ), c0 * (x ^ (-(3 / 2 : ℝ)) *
          Real.exp (-((s ^ 2 / 2) / x) - (b ^ 2 / 2) * x)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact density_factor s b x hx
    rw [hfac, integral_const_mul]
    rw [reciprocal_core (s ^ 2 / 2) (b ^ 2 / 2) (by positivity) (by positivity)]
    rw [show Real.sqrt (s ^ 2 / 2) = s / Real.sqrt 2 from by
      have harg : s ^ 2 / 2 = (s / Real.sqrt 2) ^ 2 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [harg, Real.sqrt_sq (by positivity)]]
    rw [show Real.sqrt ((s ^ 2 / 2) * (b ^ 2 / 2)) = s * b / 2 from by
      have harg : (s ^ 2 / 2) * (b ^ 2 / 2) = (s * b / 2) ^ 2 := by ring
      rw [harg, Real.sqrt_sq (by positivity)]]
    have hexp2 : Real.exp (-2 * (s * b / 2)) = Real.exp (-(s * b)) := by
      congr 1
      ring
    rw [hexp2]
    rw [hc0def]
    have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
      Real.sqrt_mul (by norm_num) Real.pi
    have hsne : s ≠ 0 := ne_of_gt hs
    have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
    have hpne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos Real.pi_pos)
    have hexp3 : Real.exp (s * b) * Real.exp (-(s * b)) = 1 := by
      rw [← Real.exp_add, show s * b + -(s * b) = 0 by ring, Real.exp_zero]
    calc (s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) *
          (Real.sqrt Real.pi / (s / Real.sqrt 2) * Real.exp (-(s * b)))
        = ((s / Real.sqrt (2 * Real.pi)) * (Real.sqrt Real.pi / (s / Real.sqrt 2))) *
            (Real.exp (s * b) * Real.exp (-(s * b))) := by ring
      _ = ((s / Real.sqrt (2 * Real.pi)) * (Real.sqrt Real.pi / (s / Real.sqrt 2))) * 1 := by
            rw [hexp3]
      _ = 1 := by
            rw [mul_one, h2pi]
            field_simp
  rw [withDensity_apply _ MeasurableSet.univ]
  simp only [setLIntegral_univ, Measure.restrict_univ]
  rw [← ofReal_integral_eq_lintegral_ofReal hIntOn hnn]
  rw [hIntegral]
  norm_num

/-! ## Laplace transform value -/

theorem thm_val (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    ∀ q : ℝ, 0 ≤ q →
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  dsimp only
  intro q hq
  set w : ℝ → ℝ := fun x : ℝ =>
    (s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x))) with hwdef
  have hw_meas : Measurable w := by
    rw [hwdef]
    measurability
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (w x)) := hw_meas.ennreal_ofReal
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (w x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul (f := fun x : ℝ => ENNReal.ofReal (w x))
    hmeas hflt]
  rw [show (∫ x, (ENNReal.ofReal (w x)).toReal • Real.exp (-q * x)
        ∂(volume.restrict (Ioi (0 : ℝ)))) = ∫ x in Ioi (0 : ℝ), Real.exp (-q * x) * w x from by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      dsimp only
      rw [ENNReal.toReal_ofReal (density_nonneg s b x hs hx), smul_eq_mul]
      exact mul_comm _ _]
  have hfac : ∀ x ∈ Ioi (0 : ℝ), Real.exp (-q * x) * w x =
      ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b)) *
        (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x)) :=
    fun x hx => density_laplace_factor s b q x hx
  rw [show (∫ x in Ioi (0 : ℝ), Real.exp (-q * x) * w x) =
      ∫ x in Ioi (0 : ℝ), ((s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b)) *
        (x ^ (-(3 / 2 : ℝ)) * Real.exp (-((s ^ 2 / 2) / x) -
          ((b ^ 2 + 2 * q) / 2) * x)) from by
      apply setIntegral_congr_fun measurableSet_Ioi
      exact hfac]
  rw [integral_const_mul]
  rw [reciprocal_core (s ^ 2 / 2) ((b ^ 2 + 2 * q) / 2) (by positivity) (by positivity)]
  rw [show Real.sqrt (s ^ 2 / 2) = s / Real.sqrt 2 from by
    have harg : s ^ 2 / 2 = (s / Real.sqrt 2) ^ 2 := by
      rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    rw [harg, Real.sqrt_sq (by positivity)]]
  rw [show Real.sqrt ((s ^ 2 / 2) * ((b ^ 2 + 2 * q) / 2)) =
      s * Real.sqrt (b ^ 2 + 2 * q) / 2 from by
    have harg : (s ^ 2 / 2) * ((b ^ 2 + 2 * q) / 2) =
        (s * Real.sqrt (b ^ 2 + 2 * q) / 2) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt (by positivity)]
      ring
    rw [harg, Real.sqrt_sq (by positivity)]]
  have hexp2 : Real.exp (-2 * (s * Real.sqrt (b ^ 2 + 2 * q) / 2)) =
      Real.exp (-(s * Real.sqrt (b ^ 2 + 2 * q))) := by
    congr 1
    ring
  rw [hexp2]
  have h2pi : Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi :=
    Real.sqrt_mul (by norm_num) Real.pi
  have hsne : s ≠ 0 := ne_of_gt hs
  have h2ne : Real.sqrt 2 ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by norm_num))
  have hpne : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos Real.pi_pos)
  have hscalar : (s / Real.sqrt (2 * Real.pi)) * (Real.sqrt Real.pi / (s / Real.sqrt 2)) = 1 := by
    rw [h2pi]
    field_simp
  calc (s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) *
        (Real.sqrt Real.pi / (s / Real.sqrt 2) * Real.exp (-(s * Real.sqrt (b ^ 2 + 2 * q))))
      = ((s / Real.sqrt (2 * Real.pi)) * (Real.sqrt Real.pi / (s / Real.sqrt 2))) *
          (Real.exp (s * b) * Real.exp (-(s * Real.sqrt (b ^ 2 + 2 * q)))) := by ring
    _ = 1 * (Real.exp (s * b) * Real.exp (-(s * Real.sqrt (b ^ 2 + 2 * q)))) := by
          rw [hscalar]
    _ = Real.exp (s * b + -(s * Real.sqrt (b ^ 2 + 2 * q))) := by
          rw [one_mul, Real.exp_add]
    _ = Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
          congr 1
          ring

/-! ## Discounted integrability -/

theorem thm_disc (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    ∀ q : ℝ, 0 ≤ q → Integrable (fun x : ℝ => Real.exp (-q * x)) IG := by
  dsimp only
  intro q hq
  set w : ℝ → ℝ := fun x : ℝ =>
    (s / Real.sqrt (2 * Real.pi * x ^ 3)) * Real.exp (-((s - b * x) ^ 2 / (2 * x))) with hwdef
  have hw_meas : Measurable w := by
    rw [hwdef]
    measurability
  have hmeas : Measurable (fun x : ℝ => ENNReal.ofReal (w x)) := hw_meas.ennreal_ofReal
  have hflt : ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ))), ENNReal.ofReal (w x) < ⊤ :=
    Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top
  rw [integrable_withDensity_iff_integrable_smul' (μ := volume.restrict (Ioi (0 : ℝ))) hmeas hflt]
  set c0 : ℝ := (s / Real.sqrt (2 * Real.pi)) * Real.exp (s * b) with hc0def
  have hR : IntegrableOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ)) *
      Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x)) (Ioi (0 : ℝ)) :=
    reciprocal_integrable (s ^ 2 / 2) ((b ^ 2 + 2 * q) / 2) (by positivity) (by positivity)
  have h := hR.const_mul c0
  refine IntegrableOn.congr_fun h ?_ measurableSet_Ioi
  intro x hx
  beta_reduce
  rw [ENNReal.toReal_ofReal (density_nonneg s b x hs hx), smul_eq_mul]
  calc c0 * (x ^ (-(3 / 2 : ℝ)) *
        Real.exp (-((s ^ 2 / 2) / x) - ((b ^ 2 + 2 * q) / 2) * x))
      = Real.exp (-q * x) * w x := (density_laplace_factor s b q x hx).symm
    _ = w x * Real.exp (-q * x) := by ring

/-! ## Packaged statement -/

theorem thm_pkg (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 ∧
    ∀ q : ℝ, 0 ≤ q →
      Integrable (fun x : ℝ => Real.exp (-q * x)) IG ∧
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) := by
  dsimp only
  constructor
  · exact thm_mass s b hs hb
  · intro q hq
    exact ⟨thm_disc s b hs hb q hq, thm_val s b hs hb q hq⟩

theorem solution (s b : ℝ) (hs : 0 < s) (hb : 0 < b) :
    let IG : Measure ℝ :=
      (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
        (fun x : ℝ =>
          ENNReal.ofReal
            ((s / Real.sqrt (2 * Real.pi * x ^ 3)) *
              Real.exp (-((s - b * x) ^ 2 / (2 * x)))))
    IG Set.univ = 1 ∧
    ∀ q : ℝ, 0 ≤ q →
      Integrable (fun x : ℝ => Real.exp (-q * x)) IG ∧
      (∫ x, Real.exp (-q * x) ∂IG) =
        Real.exp (-s * (Real.sqrt (b ^ 2 + 2 * q) - b)) :=
  thm_pkg s b hs hb
