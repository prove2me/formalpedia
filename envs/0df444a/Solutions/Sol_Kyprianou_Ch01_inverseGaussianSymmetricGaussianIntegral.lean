-- Prove2me | solution 1 for Kyprianou.Ch01.inverseGaussianSymmetricGaussianIntegral
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-21T01:59:23.264654+00:00
-- url     : https://prove2.me/submissions/5402831f-8fa9-47f5-a28a-1d0fccb05912

import Mathlib
open MeasureTheory Set Real
set_option autoImplicit false

/-- The Glasser-type Gaussian integral
`∫_0^∞ exp(-a y² - c/y²) dy = (√π / (2√a)) exp(-2√(ac))` for `a, c > 0`. -/
theorem solution (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
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
