-- Prove2me | solution 1 for MasulloRH.partialEulerProduct_tendsto_riemannZeta_one_line
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T01:29:33.004184+00:00
-- url     : https://prove2.me/submissions/5226aff2-1f2e-48b2-a2b3-e412b1eb1e98

import Theorems.Thm_ArtinPrimitiveRoots_psi_prime_number_theorem

set_option autoImplicit false

open Real Filter Topology MeasureTheory Set Asymptotics

namespace OneLineTheta

lemma log_two_gt_half : (1 : ℝ) / 2 < Real.log 2 := by
  have := Real.log_two_gt_d9; linarith

lemma log_ge_half {x : ℝ} (hx : 2 ≤ x) : (1 : ℝ) / 2 ≤ Real.log x :=
  le_trans log_two_gt_half.le (Real.log_le_log (by norm_num) hx)

lemma log_pos_of_two_le {x : ℝ} (hx : 2 ≤ x) : 0 < Real.log x := by
  have := log_ge_half hx; linarith

lemma log_sq_le_four_mul {x : ℝ} (hx1 : 1 ≤ x) : Real.log x ^ 2 ≤ 4 * x := by
  have hx : 0 < x := by linarith
  have h1 : Real.log (√x) ≤ √x - 1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  have h2 : Real.log (√x) = Real.log x / 2 := by
    rw [Real.log_sqrt hx.le]
  have hs : √x * √x = x := Real.mul_self_sqrt hx.le
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have : Real.log x ≤ 2 * √x := by linarith
  nlinarith

lemma log_cube_le {x : ℝ} (hx : 1 ≤ x) : Real.log x ^ 3 ≤ 216 * √x := by
  have h := Real.log_le_rpow_div (x := x) (by linarith) (by norm_num : (0 : ℝ) < 1 / 6)
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx
  have h6 : Real.log x ≤ 6 * x ^ (1 / 6 : ℝ) := by
    have : x ^ (1 / 6 : ℝ) / (1 / 6) = 6 * x ^ (1 / 6 : ℝ) := by ring
    linarith
  have hx0 : 0 ≤ x ^ (1 / 6 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hcube : (x ^ (1 / 6 : ℝ)) ^ 3 = √x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), Real.sqrt_eq_rpow]
    norm_num
  calc Real.log x ^ 3 ≤ (6 * x ^ (1 / 6 : ℝ)) ^ 3 := by gcongr
    _ = 216 * √x := by rw [mul_pow, hcube]; norm_num

/-- The prime number theorem for `θ` with error `x / log² x`. -/
lemma theta_pnt : ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x →
    |Chebyshev.theta x - x| ≤ C * (x / Real.log x ^ 2) := by
  obtain ⟨C0, hC0⟩ := ArtinPrimitiveRoots.psi_prime_number_theorem 2 two_pos
  refine ⟨4 * |C0| + 444, by positivity, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hlog := log_pos_of_two_le hx
  have hq : 0 < x / Real.log x ^ 2 := by positivity
  rcases lt_or_ge x 4 with hx4 | hx4
  · -- small range
    have hθ0 := Chebyshev.theta_nonneg x
    have hθ := Chebyshev.theta_le_log4_mul_x hx0.le
    have hl4 : Real.log 4 < 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    have hlx : Real.log x ^ 2 ≤ 2 := by
      have h1 : Real.log x < Real.log 4 := Real.log_lt_log hx0 hx4
      have h2 : Real.log 4 < 1.4 := by
        have : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_lt_d9; linarith
      nlinarith
    have hxq : x / 2 ≤ x / Real.log x ^ 2 := by
      apply div_le_div_of_nonneg_left hx0.le (by positivity) hlx
    have : |Chebyshev.theta x - x| ≤ 3 * x := by
      rw [abs_le]; constructor <;> nlinarith
    have hC : (6 : ℝ) ≤ 4 * |C0| + 444 := by have := abs_nonneg C0; linarith
    calc |Chebyshev.theta x - x| ≤ 3 * x := this
      _ = 6 * (x / 2) := by ring
      _ ≤ 6 * (x / Real.log x ^ 2) := by gcongr
      _ ≤ (4 * |C0| + 444) * (x / Real.log x ^ 2) := by gcongr
  · -- large range
    set X : ℕ := ⌊x⌋₊ with hX
    have hXle : (X : ℝ) ≤ x := Nat.floor_le hx0.le
    have hXgt : x < X + 1 := Nat.lt_floor_add_one x
    have hX4 : 4 ≤ X := Nat.le_floor (by exact_mod_cast hx4)
    have hX2 : 2 ≤ X := by omega
    have hXr : (4 : ℝ) ≤ X := by exact_mod_cast hX4
    have hpsi : Chebyshev.psi x = ∑ n ∈ Finset.Ioc 0 X, ArithmeticFunction.vonMangoldt n := rfl
    have h1 := hC0 X hX2
    rw [← hpsi] at h1
    have hlogX : Real.log x / 2 ≤ Real.log X := by
      have hhalf : x / 2 ≤ X := by linarith
      have h2 : Real.log (x / 2) ≤ Real.log X := Real.log_le_log (by linarith) hhalf
      rw [Real.log_div hx0.ne' (by norm_num)] at h2
      have : 2 * Real.log 2 ≤ Real.log x := by
        rw [← Real.log_rpow (by norm_num)]
        exact Real.log_le_log (by positivity) (by norm_num; linarith)
      linarith
    have hlogXpos : 0 < Real.log X := by linarith
    have hrp : Real.log X ^ (-2 : ℝ) = 1 / Real.log X ^ 2 := by
      rw [Real.rpow_neg hlogXpos.le, one_div]; norm_cast
    rw [hrp] at h1
    have hb1 : (X : ℝ) * (1 / Real.log X ^ 2) ≤ 4 * (x / Real.log x ^ 2) := by
      rw [mul_one_div, div_le_iff₀ (by positivity)]
      have : Real.log x ^ 2 ≤ 4 * Real.log X ^ 2 := by nlinarith
      have h3 : 4 * (x / Real.log x ^ 2) * Real.log X ^ 2 =
          x * (4 * Real.log X ^ 2) / Real.log x ^ 2 := by ring
      rw [h3, le_div_iff₀ (by positivity)]
      nlinarith
    have hpsi_err : |Chebyshev.psi x - x| ≤ 4 * |C0| * (x / Real.log x ^ 2) + 4 * (x / Real.log x ^ 2) := by
      have e1 : |Chebyshev.psi x - X| ≤ |C0| * (X * (1 / Real.log X ^ 2)) :=
        h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity))
      have e2 : |(X : ℝ) - x| ≤ 1 := by rw [abs_le]; constructor <;> linarith
      have e3 : (1 : ℝ) ≤ 4 * (x / Real.log x ^ 2) := by
        rw [mul_div_assoc', le_div_iff₀ (by positivity), one_mul]
        exact log_sq_le_four_mul (by linarith)
      calc |Chebyshev.psi x - x| = |(Chebyshev.psi x - X) + (X - x)| := by ring_nf
        _ ≤ |Chebyshev.psi x - X| + |(X : ℝ) - x| := abs_add_le _ _
        _ ≤ |C0| * (4 * (x / Real.log x ^ 2)) + 1 := by
            gcongr
            exact e1.trans (mul_le_mul_of_nonneg_left hb1 (abs_nonneg _))
        _ ≤ _ := by nlinarith [abs_nonneg C0]
    have hpt := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := x) (by linarith)
    have hpt' : 2 * √x * Real.log x ≤ 432 * (x / Real.log x ^ 2) := by
      have hc := log_cube_le (x := x) (by linarith)
      rw [mul_div_assoc', le_div_iff₀ (by positivity)]
      have hs : √x * √x = x := Real.mul_self_sqrt hx0.le
      have hsx : 0 ≤ √x := Real.sqrt_nonneg x
      calc 2 * √x * Real.log x * Real.log x ^ 2 = 2 * √x * Real.log x ^ 3 := by ring
        _ ≤ 2 * √x * (216 * √x) := by gcongr
        _ = 432 * (√x * √x) := by ring
        _ = 432 * x := by rw [hs]
    calc |Chebyshev.theta x - x| = |(Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x)| := by
          ring_nf
      _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := abs_sub _ _
      _ ≤ (4 * |C0| * (x / Real.log x ^ 2) + 4 * (x / Real.log x ^ 2)) + 432 * (x / Real.log x ^ 2) := by
          gcongr; exact hpt.trans hpt'
      _ ≤ (4 * |C0| + 444) * (x / Real.log x ^ 2) := by nlinarith

end OneLineTheta

namespace EulerOneLine

/-- `u ↦ u^{-w}` as a complex function of a real variable. -/
noncomputable def P (w : ℂ) (u : ℝ) : ℂ := (u : ℂ) ^ (-w)
/-- `f_w(u) = u^{-w} / log u`. -/
noncomputable def fw (w : ℂ) (u : ℝ) : ℂ := P w u / (Real.log u : ℂ)
/-- derivative of `f_w`. -/
noncomputable def dfw (w : ℂ) (u : ℝ) : ℂ :=
  -(P w u * (w * (Real.log u : ℂ) + 1)) / ((u : ℂ) * (Real.log u : ℂ) ^ 2)
/-- an antiderivative of `u^{-w}`. -/
noncomputable def gw (w : ℂ) (u : ℝ) : ℂ := (u : ℂ) * P w u / (1 - w)
/-- `H_w(u) = -w g_w(u) / log u`. -/
noncomputable def Hw (w : ℂ) (u : ℝ) : ℂ := -w * gw w u / (Real.log u : ℂ)
/-- derivative of `H_w`. -/
noncomputable def dHw (w : ℂ) (u : ℝ) : ℂ :=
  -w * P w u / (Real.log u : ℂ) + w * gw w u / ((u : ℂ) * (Real.log u : ℂ) ^ 2)

lemma hasDerivAt_P (w : ℂ) {u : ℝ} (hu : 0 < u) :
    HasDerivAt (P w) (-w * P w u / u) u := by
  have h0 : ((u : ℂ)) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.mpr hu
  have h := ((hasDerivAt_id ((u : ℂ))).cpow_const (c := -w) h0).comp_ofReal
  simp only [id, mul_one] at h
  refine h.congr_deriv ?_
  have hu0 : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  rw [P, Complex.cpow_sub _ _ hu0, Complex.cpow_one]
  ring

lemma hasDerivAt_logC {u : ℝ} (hu : 0 < u) :
    HasDerivAt (fun u : ℝ => (Real.log u : ℂ)) ((u : ℂ)⁻¹) u := by
  have := (Real.hasDerivAt_log hu.ne').ofReal_comp
  simpa using this

lemma hasDerivAt_fw (w : ℂ) {u : ℝ} (hu : 1 < u) : HasDerivAt (fw w) (dfw w u) u := by
  have hu0 : 0 < u := by linarith
  have hl : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have h := (hasDerivAt_P w hu0).div (hasDerivAt_logC hu0) hl
  refine h.congr_deriv ?_
  rw [dfw]
  field_simp
  ring

lemma hasDerivAt_gw {w : ℂ} (hw : w ≠ 1) {u : ℝ} (hu : 0 < u) : HasDerivAt (gw w) (P w u) u := by
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu.ne'
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  have h := (((hasDerivAt_id u).ofReal_comp).mul (hasDerivAt_P w hu)).div_const (1 - w)
  refine h.congr_deriv ?_
  simp only [id, Complex.ofReal_one]
  field_simp
  ring

lemma hasDerivAt_Hw {w : ℂ} (hw : w ≠ 1) {u : ℝ} (hu : 1 < u) : HasDerivAt (Hw w) (dHw w u) u := by
  have hu0 : 0 < u := by linarith
  have hl : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have h := ((hasDerivAt_gw hw hu0).const_mul (-w)).div (hasDerivAt_logC hu0) hl
  have e : Hw w = fun u => -w * gw w u / (Real.log u : ℂ) := rfl
  rw [e]
  refine h.congr_deriv ?_
  rw [dHw]
  field_simp
  ring

/-- The key algebraic identity `u f_w'(u) - H_w'(u) = -u^{-w} / ((1-w) log² u)`. -/
lemma mul_dfw_sub_dHw {w : ℂ} (hw : w ≠ 1) {u : ℝ} (hu : 1 < u) :
    (u : ℂ) * dfw w u - dHw w u = -P w u / ((1 - w) * (Real.log u : ℂ) ^ 2) := by
  have hu0 : 0 < u := by linarith
  have hl : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have h1w : (1 : ℂ) - w ≠ 0 := sub_ne_zero.mpr (Ne.symm hw)
  rw [dfw, dHw, gw]
  field_simp
  ring

lemma norm_P {w : ℂ} (hw : 1 ≤ w.re) {u : ℝ} (hu : 1 ≤ u) : ‖P w u‖ ≤ u⁻¹ := by
  have hu0 : 0 < u := by linarith
  rw [P, Complex.norm_cpow_eq_rpow_re_of_pos hu0, Complex.neg_re, ← Real.rpow_neg_one]
  exact Real.rpow_le_rpow_of_exponent_le hu (by linarith)

lemma log_ge_half {x : ℝ} (hx : 2 ≤ x) : (1 : ℝ) / 2 ≤ Real.log x := by
  have : (1 : ℝ) / 2 < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  exact le_trans this.le (Real.log_le_log (by norm_num) hx)

lemma norm_logC {u : ℝ} (hu : 1 ≤ u) : ‖(Real.log u : ℂ)‖ = Real.log u := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg hu)]

lemma norm_ofReal_pos {u : ℝ} (hu : 0 ≤ u) : ‖(u : ℂ)‖ = u := by
  rw [Complex.norm_real, Real.norm_of_nonneg hu]

lemma norm_one_sub_ge {w : ℂ} : |w.im| ≤ ‖1 - w‖ := by
  have := Complex.abs_im_le_norm (1 - w)
  simpa using this

/-- `‖u f'(u) - H'(u)‖ ≤ 1/(|τ| u log² u)`. -/
lemma norm_mul_dfw_sub_dHw {w : ℂ} (hw1 : 1 ≤ w.re) (him : w.im ≠ 0) {u : ℝ} (hu : 2 ≤ u) :
    ‖(u : ℂ) * dfw w u - dHw w u‖ ≤ |w.im|⁻¹ / (u * Real.log u ^ 2) := by
  have hw : w ≠ 1 := by intro h; rw [h] at him; simp at him
  have hu1 : 1 < u := by linarith
  have hl := Real.log_pos hu1
  rw [mul_dfw_sub_dHw hw hu1, norm_div, norm_neg, norm_mul, norm_pow, norm_logC hu1.le]
  have hP := norm_P hw1 hu1.le
  have h1w : |w.im| ≤ ‖1 - w‖ := norm_one_sub_ge
  have him' : 0 < |w.im| := abs_pos.mpr him
  have hn1 : 0 < ‖1 - w‖ := lt_of_lt_of_le him' h1w
  rw [div_le_div_iff₀ (mul_pos hn1 (by positivity)) (by positivity)]
  calc ‖P w u‖ * (u * Real.log u ^ 2) ≤ u⁻¹ * (u * Real.log u ^ 2) := by gcongr
    _ = Real.log u ^ 2 := by field_simp
    _ = |w.im|⁻¹ * (|w.im| * Real.log u ^ 2) := by field_simp
    _ ≤ |w.im|⁻¹ * (‖1 - w‖ * Real.log u ^ 2) := by gcongr

lemma norm_dfw {w : ℂ} (hw1 : 1 ≤ w.re) {u : ℝ} (hu : 2 ≤ u) :
    ‖dfw w u‖ ≤ (‖w‖ * Real.log u + 1) / (u ^ 2 * Real.log u ^ 2) := by
  have hu1 : 1 < u := by linarith
  have hl := Real.log_pos hu1
  have hu0 : 0 < u := by linarith
  rw [dfw, norm_div, norm_neg, norm_mul, norm_mul, norm_pow, norm_logC hu1.le, norm_ofReal_pos hu0.le]
  have hP := norm_P hw1 hu1.le
  have hn : ‖w * (Real.log u : ℂ) + 1‖ ≤ ‖w‖ * Real.log u + 1 := by
    calc ‖w * (Real.log u : ℂ) + 1‖ ≤ ‖w * (Real.log u : ℂ)‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
      _ = ‖w‖ * Real.log u + 1 := by rw [norm_mul, norm_logC hu1.le, norm_one]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  calc ‖P w u‖ * ‖w * (Real.log u : ℂ) + 1‖ * (u ^ 2 * Real.log u ^ 2)
      ≤ u⁻¹ * (‖w‖ * Real.log u + 1) * (u ^ 2 * Real.log u ^ 2) := by gcongr
    _ = (‖w‖ * Real.log u + 1) * (u * Real.log u ^ 2) := by field_simp

/-- the remainder integrand -/
noncomputable def Φ (w : ℂ) (u : ℝ) : ℂ := dfw w u * (Chebyshev.theta u : ℂ) - dHw w u

lemma norm_Φ {w : ℂ} (hw1 : 1 ≤ w.re) (him : w.im ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * (x / Real.log x ^ 2)) {u : ℝ} (hu : 2 ≤ u) :
    ‖Φ w u‖ ≤ (|w.im|⁻¹ + C * (2 * ‖w‖ + 4)) / (u * Real.log u ^ 2) := by
  have hu1 : 1 < u := by linarith
  have hl := Real.log_pos hu1
  have hl2 := log_ge_half hu
  have hu0 : 0 < u := by linarith
  have e : Φ w u = ((u : ℂ) * dfw w u - dHw w u) + dfw w u * ((Chebyshev.theta u - u : ℝ) : ℂ) := by
    rw [Φ]; push_cast; ring
  rw [e]
  have h1 := norm_mul_dfw_sub_dHw hw1 him hu
  have h2 := norm_dfw hw1 hu
  have h3 := hθ u hu
  have h4 : ‖dfw w u * ((Chebyshev.theta u - u : ℝ) : ℂ)‖ ≤ C * (2 * ‖w‖ + 4) / (u * Real.log u ^ 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
    have key : ‖w‖ * Real.log u + 1 ≤ (2 * ‖w‖ + 4) * Real.log u ^ 2 := by
      have a1 : 0 ≤ ‖w‖ * Real.log u * (2 * Real.log u - 1) :=
        mul_nonneg (mul_nonneg hw0 hl.le) (by linarith)
      have a2 : 1 ≤ 4 * Real.log u ^ 2 := by nlinarith
      nlinarith
    calc ‖dfw w u‖ * |Chebyshev.theta u - u|
        ≤ (‖w‖ * Real.log u + 1) / (u ^ 2 * Real.log u ^ 2) * (C * (u / Real.log u ^ 2)) := by
          gcongr
      _ = C * (‖w‖ * Real.log u + 1) / (u * Real.log u ^ 2 * Real.log u ^ 2) := by
          field_simp
      _ ≤ C * ((2 * ‖w‖ + 4) * Real.log u ^ 2) / (u * Real.log u ^ 2 * Real.log u ^ 2) := by
          gcongr
      _ = C * (2 * ‖w‖ + 4) / (u * Real.log u ^ 2) := by
          field_simp
  calc _ ≤ ‖(u : ℂ) * dfw w u - dHw w u‖ + ‖dfw w u * ((Chebyshev.theta u - u : ℝ) : ℂ)‖ :=
        norm_add_le _ _
    _ ≤ |w.im|⁻¹ / (u * Real.log u ^ 2) + C * (2 * ‖w‖ + 4) / (u * Real.log u ^ 2) := add_le_add h1 h4
    _ = _ := by ring

lemma hasDerivAt_neg_inv_log {u : ℝ} (hu : 1 < u) :
    HasDerivAt (fun u => -(Real.log u)⁻¹) (1 / (u * Real.log u ^ 2)) u := by
  have hl := Real.log_pos hu
  have h := ((Real.hasDerivAt_log (by linarith : u ≠ 0)).inv hl.ne').neg
  refine h.congr_deriv ?_
  field_simp

lemma tendsto_neg_inv_log : Tendsto (fun u : ℝ => -(Real.log u)⁻¹) atTop (𝓝 0) := by
  have := (Real.tendsto_log_atTop.inv_tendsto_atTop).neg
  simpa using this

lemma integrableOn_bound {b : ℝ} (hb : 2 ≤ b) :
    IntegrableOn (fun u : ℝ => 1 / (u * Real.log u ^ 2)) (Ioi b) := by
  refine integrableOn_Ioi_deriv_of_nonneg' (g := fun u => -(Real.log u)⁻¹) (l := 0)
    (fun x hx => hasDerivAt_neg_inv_log (by have := hx.out; linarith)) (fun x hx => ?_)
    tendsto_neg_inv_log
  have : 1 < x := by have := hx.out; linarith
  have := Real.log_pos this
  have : 0 < x := by linarith
  positivity

lemma integral_bound {b : ℝ} (hb : 2 ≤ b) :
    ∫ u in Ioi b, 1 / (u * Real.log u ^ 2) = 1 / Real.log b := by
  rw [integral_Ioi_of_hasDerivAt_of_nonneg' (g := fun u => -(Real.log u)⁻¹) (l := 0)
    (fun x hx => hasDerivAt_neg_inv_log (by have := hx.out; linarith)) (fun x hx => ?_)
    tendsto_neg_inv_log]
  · simp
  · have : 1 < x := by have := hx.out; linarith
    have := Real.log_pos this
    have : 0 < x := by linarith
    positivity

lemma measurable_P (w : ℂ) : Measurable (P w) := by
  unfold P
  exact Complex.measurable_ofReal.pow_const _

lemma measurable_Φ (w : ℂ) : Measurable (Φ w) := by
  have hP := measurable_P w
  have hθ : Measurable Chebyshev.theta := Chebyshev.theta_mono.measurable
  unfold Φ dfw dHw gw
  fun_prop

section bounds

variable {w : ℂ} (hw1 : 1 ≤ w.re) (him : w.im ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * (x / Real.log x ^ 2))
include hw1 him hC hθ

lemma integrableOn_Φ {b : ℝ} (hb : 2 ≤ b) : IntegrableOn (Φ w) (Ioi b) := by
  have hK := (integrableOn_bound hb).const_mul (|w.im|⁻¹ + C * (2 * ‖w‖ + 4))
  refine hK.mono' (measurable_Φ w).aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => ?_)
  have h2 : 2 ≤ u := by have := hu.out; linarith
  have := norm_Φ hw1 him hC hθ h2
  calc ‖Φ w u‖ ≤ _ := this
    _ = _ := by ring

lemma norm_integral_Φ_Ioi {b : ℝ} (hb : 2 ≤ b) :
    ‖∫ u in Ioi b, Φ w u‖ ≤ (|w.im|⁻¹ + C * (2 * ‖w‖ + 4)) / Real.log b := by
  have hK := (integrableOn_bound hb).const_mul (|w.im|⁻¹ + C * (2 * ‖w‖ + 4))
  have h := norm_integral_le_of_norm_le hK
    ((ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun u hu => by
      have h2 : 2 ≤ u := by have := hu.out; linarith
      have := norm_Φ hw1 him hC hθ h2
      calc ‖Φ w u‖ ≤ _ := this
        _ = (|w.im|⁻¹ + C * (2 * ‖w‖ + 4)) * (1 / (u * Real.log u ^ 2)) := by ring))
  rw [integral_const_mul, integral_bound hb] at h
  calc _ ≤ _ := h
    _ = _ := by ring

end bounds

lemma continuousAt_P (w : ℂ) {u : ℝ} (hu : 0 < u) : ContinuousAt (P w) u :=
  (hasDerivAt_P w hu).continuousAt

lemma continuousAt_logC {u : ℝ} (hu : 0 < u) : ContinuousAt (fun u : ℝ => (Real.log u : ℂ)) u :=
  (hasDerivAt_logC hu).continuousAt

lemma continuousAt_dfw (w : ℂ) {u : ℝ} (hu : 1 < u) : ContinuousAt (dfw w) u := by
  have hu0 : 0 < u := by linarith
  have hl : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have h1 := continuousAt_P w hu0
  have h2 := continuousAt_logC hu0
  have h3 : ContinuousAt (fun u : ℝ => (u : ℂ)) u := Complex.continuous_ofReal.continuousAt
  exact ((h1.mul ((continuousAt_const.mul h2).add continuousAt_const)).neg).div
    (h3.mul (h2.pow 2)) (mul_ne_zero hu0' (pow_ne_zero 2 hl))

lemma continuousAt_dHw (w : ℂ) {u : ℝ} (hu : 1 < u) : ContinuousAt (dHw w) u := by
  have hu0 : 0 < u := by linarith
  have hl : (Real.log u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.log_pos hu).ne'
  have hu0' : (u : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hu0.ne'
  have h1 := continuousAt_P w hu0
  have h2 := continuousAt_logC hu0
  have h3 : ContinuousAt (fun u : ℝ => (u : ℂ)) u := Complex.continuous_ofReal.continuousAt
  have hg : ContinuousAt (gw w) u := (h3.mul h1).div_const _
  exact ((continuousAt_const.mul h1).div h2 hl).add
    ((continuousAt_const.mul hg).div (h3.mul (h2.pow 2)) (mul_ne_zero hu0' (pow_ne_zero 2 hl)))

/-- prime indicator weights `log p`. -/
noncomputable def aw (k : ℕ) : ℂ := if k.Prime then (Real.log k : ℂ) else 0

lemma sum_aw (t : ℝ) : ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, aw k = (Chebyshev.theta t : ℂ) := by
  rw [Chebyshev.theta_eq_sum_Icc, Complex.ofReal_sum, Finset.sum_filter]
  rfl

lemma abel (w : ℂ) {b : ℝ} (hb : 2 ≤ b) :
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊, fw w k * aw k =
      fw w b * (Chebyshev.theta b : ℂ) - ∫ t in Ioc 2 b, dfw w t * (Chebyshev.theta t : ℂ) := by
  have hderiv : ∀ t ∈ Icc (2 : ℝ) b, deriv (fw w) t = dfw w t :=
    fun t ht => (hasDerivAt_fw w (by linarith [ht.1])).deriv
  have hint : IntegrableOn (dfw w) (Icc 2 b) :=
    ContinuousOn.integrableOn_Icc
      (fun t ht => (continuousAt_dfw w (by linarith [ht.1])).continuousWithinAt)
  rw [sum_mul_eq_sub_integral_mul₁ aw (by simp [aw]) (by simp [aw]) b
      (fun t ht => (hasDerivAt_fw w (by linarith [ht.1])).differentiableAt)
      (hint.congr_fun (fun t ht => (hderiv t ht).symm) measurableSet_Icc)]
  rw [sum_aw]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  rw [hderiv t (Ioc_subset_Icc_self ht), sum_aw]

lemma integral_dHw {w : ℂ} (hw : w ≠ 1) {b : ℝ} (hb : 2 ≤ b) :
    ∫ t in (2 : ℝ)..b, dHw w t = Hw w b - Hw w 2 := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => ?_) ?_
  · rw [uIcc_of_le hb] at ht
    exact hasDerivAt_Hw hw (by linarith [ht.1])
  · refine ContinuousOn.intervalIntegrable (fun t ht => ?_)
    rw [uIcc_of_le hb] at ht
    exact (continuousAt_dHw w (by linarith [ht.1])).continuousWithinAt

/-- the limit of the prime sums `∑_{p ≤ b} p^{-w}` -/
noncomputable def Lim (w : ℂ) : ℂ := Hw w 2 - ∫ t in Ioi (2 : ℝ), Φ w t

section rate

variable {w : ℂ} (hw1 : 1 ≤ w.re) (him : w.im ≠ 0) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * (x / Real.log x ^ 2))
include hw1 him hC hθ

lemma rate {b : ℝ} (hb : 2 ≤ b) :
    ‖∑ k ∈ Finset.Icc 0 ⌊b⌋₊, fw w k * aw k - Lim w‖ ≤
      (Real.log 4 + ‖w‖ * |w.im|⁻¹ + (|w.im|⁻¹ + C * (2 * ‖w‖ + 4))) / Real.log b := by
  have hw : w ≠ 1 := by intro h; rw [h] at him; simp at him
  have hb1 : 1 < b := by linarith
  have hb0 : 0 < b := by linarith
  have hl := Real.log_pos hb1
  have hΦ2 := integrableOn_Φ hw1 him hC hθ (le_refl 2)
  have hΦb := integrableOn_Φ hw1 him hC hθ hb
  have hsplit : ∫ t in Ioc 2 b, dfw w t * (Chebyshev.theta t : ℂ) =
      (Hw w b - Hw w 2) + ∫ t in Ioc 2 b, Φ w t := by
    have e : ∀ t, dfw w t * (Chebyshev.theta t : ℂ) = dHw w t + Φ w t := by
      intro t; rw [Φ]; ring
    simp_rw [e]
    have hdH : IntegrableOn (dHw w) (Ioc 2 b) := by
      refine (ContinuousOn.integrableOn_Icc (fun t ht => ?_)).mono_set Ioc_subset_Icc_self
      exact (continuousAt_dHw w (by linarith [ht.1])).continuousWithinAt
    rw [integral_add hdH (hΦ2.mono_set Ioc_subset_Ioi_self), ← intervalIntegral.integral_of_le hb,
      integral_dHw hw hb]
  have hI : ∫ t in Ioi 2, Φ w t = (∫ t in Ioc 2 b, Φ w t) + ∫ t in Ioi b, Φ w t := by
    rw [← intervalIntegral.integral_interval_add_Ioi hΦ2 hΦb, intervalIntegral.integral_of_le hb]
  rw [abel w hb, hsplit, Lim, hI]
  have e : fw w b * (Chebyshev.theta b : ℂ) - ((Hw w b - Hw w 2) + ∫ t in Ioc 2 b, Φ w t) -
      (Hw w 2 - ((∫ t in Ioc 2 b, Φ w t) + ∫ t in Ioi b, Φ w t)) =
      fw w b * (Chebyshev.theta b : ℂ) - Hw w b + ∫ t in Ioi b, Φ w t := by ring
  rw [e]
  have hP := norm_P hw1 hb1.le
  have h1 : ‖fw w b * (Chebyshev.theta b : ℂ)‖ ≤ Real.log 4 / Real.log b := by
    rw [fw, norm_mul, norm_div, norm_logC hb1.le, Complex.norm_real,
      Real.norm_of_nonneg (Chebyshev.theta_nonneg b)]
    have hθb := Chebyshev.theta_le_log4_mul_x hb0.le
    calc ‖P w b‖ / Real.log b * Chebyshev.theta b ≤ b⁻¹ / Real.log b * (Real.log 4 * b) := by
          gcongr
      _ = Real.log 4 / Real.log b := by field_simp
  have h2 : ‖Hw w b‖ ≤ ‖w‖ * |w.im|⁻¹ / Real.log b := by
    have him' : 0 < |w.im| := abs_pos.mpr him
    have h1w : |w.im| ≤ ‖1 - w‖ := norm_one_sub_ge
    have hn1 : 0 < ‖1 - w‖ := lt_of_lt_of_le him' h1w
    have hg : ‖gw w b‖ ≤ |w.im|⁻¹ := by
      rw [gw, norm_div, norm_mul, norm_ofReal_pos hb0.le, div_le_iff₀ hn1]
      calc b * ‖P w b‖ ≤ b * b⁻¹ := by gcongr
        _ = 1 := by field_simp
        _ = |w.im|⁻¹ * |w.im| := by field_simp
        _ ≤ |w.im|⁻¹ * ‖1 - w‖ := by gcongr
    rw [Hw, norm_div, norm_mul, norm_neg, norm_logC hb1.le]
    gcongr
  have h3 := norm_integral_Φ_Ioi hw1 him hC hθ hb
  calc _ ≤ ‖fw w b * (Chebyshev.theta b : ℂ) - Hw w b‖ + ‖∫ t in Ioi b, Φ w t‖ := norm_add_le _ _
    _ ≤ (‖fw w b * (Chebyshev.theta b : ℂ)‖ + ‖Hw w b‖) + ‖∫ t in Ioi b, Φ w t‖ := by
        gcongr; exact norm_sub_le _ _
    _ ≤ (Real.log 4 / Real.log b + ‖w‖ * |w.im|⁻¹ / Real.log b) +
        (|w.im|⁻¹ + C * (2 * ‖w‖ + 4)) / Real.log b := by gcongr
    _ = _ := by ring

end rate


open scoped BigOperators
noncomputable section

private def mainTerm (k : ℕ) (w : ℂ) := if k.Prime then (k:ℂ)^(-w) else 0
private def corrTerm (k : ℕ) (w : ℂ) := if k.Prime then
    -Complex.log (1-(k:ℂ)^(-w)) - (k:ℂ)^(-w) else 0
private def logLim (w : ℂ) := Lim w + ∑' k : ℕ, corrTerm k w

private theorem main_rate (w : ℂ) (hw : 1≤w.re) (him : w.im≠0) {C : ℝ} (hC : 0 ≤ C)
    (hθ : ∀ x : ℝ, 2 ≤ x → |Chebyshev.theta x - x| ≤ C * (x / Real.log x ^ 2)) (n : ℕ) (hn : 2≤n) :
    ‖∑ k ∈ Finset.range (n+1), mainTerm k w - Lim w‖ ≤
    (Real.log 4 + ‖w‖ * |w.im|⁻¹ + (|w.im|⁻¹ + C * (2 * ‖w‖ + 4))) / Real.log n := by
  have h := rate hw him hC hθ (by exact_mod_cast hn : 2≤(n:ℝ))
  rw [Nat.floor_natCast,←Nat.range_succ_eq_Icc_zero] at h
  have he (k : ℕ) : fw w k*aw k=mainTerm k w := by
    by_cases hk : k.Prime
    · have hl : (Real.log k:ℂ)≠0 := Complex.ofReal_ne_zero.mpr
          (Real.log_pos (by exact_mod_cast hk.one_lt)).ne'
      simp only [fw,aw,P,mainTerm,if_pos hk,div_mul_cancel₀ _ hl,Complex.ofReal_natCast]
    · simp [aw,mainTerm,hk]
  simpa only [he] using h

private theorem main_uniform (K : Set ℂ) (a b : ℝ) (ha : 0<a)
    (hK : ∀ w ∈ K,1≤w.re ∧ a≤|w.im| ∧ ‖w‖≤b) :
    TendstoUniformlyOn (fun n w => ∑ k ∈ Finset.range (n+1),mainTerm k w) Lim atTop K := by
  obtain ⟨C,hC,hθ⟩ := OneLineTheta.theta_pnt
  let B := Real.log 4 + b*a⁻¹ + (a⁻¹+C*(2*b+4))
  have hzero : Tendsto (fun n : ℕ => B / Real.log n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  filter_upwards [hzero.eventually_lt_const hε,eventually_ge_atTop 2] with n hn h2 w hw
  rw [dist_comm,dist_eq_norm]
  obtain ⟨hw1,hwa,hwb⟩ := hK w hw
  have hp : 0 < |w.im| := ha.trans_le hwa
  apply lt_of_le_of_lt (main_rate w hw1 (abs_pos.mp hp) hC hθ n h2) _
  apply lt_of_le_of_lt _ hn
  apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by exact_mod_cast (by omega : 1≤n)))
  have hi : |w.im|⁻¹ ≤ a⁻¹ := inv_anti₀ ha hwa
  have hb0 := (norm_nonneg w).trans hwb
  dsimp [B]
  gcongr

private theorem main_cont (k : ℕ) : Continuous (mainTerm k) := by
  by_cases hk : k.Prime
  · change Continuous (fun w => mainTerm k w)
    simp only [mainTerm,if_pos hk]
    exact continuous_id.neg.const_cpow (.inl (by exact_mod_cast hk.ne_zero))
  · change Continuous (fun w => mainTerm k w)
    simp [mainTerm,hk,continuous_const]

private theorem pow_bd (k : ℕ) (hk : k.Prime) (w : ℂ) (hw : 1≤w.re) :
    ‖(k:ℂ)^(-w)‖ ≤ (k:ℝ)⁻¹ ∧ (k:ℝ)⁻¹ ≤ 1/2 := by
  constructor
  · simpa [P] using norm_P hw (by exact_mod_cast hk.one_le : (1:ℝ)≤k)
  · rw [one_div];exact inv_anti₀ (by norm_num) (by exact_mod_cast hk.two_le)

private theorem corr_bd (k : ℕ) {w : ℂ} (hw : 1≤w.re) :
    ‖corrTerm k w‖ ≤ 1/(k:ℝ)^2 := by
  by_cases hk : k.Prime
  · let z := (k:ℂ)^(-w)
    obtain ⟨h1,h2⟩ := pow_bd k hk w hw
    change ‖z‖≤(k:ℝ)⁻¹ at h1
    have hh : ‖z‖≤1/2 := h1.trans h2
    have hn : ‖-z‖<1 := by rw [norm_neg];linarith
    have hl := Complex.norm_log_one_add_sub_self_le hn
    rw [norm_neg] at hl
    have he : -Complex.log (1-z)-z = -(Complex.log (1 + -z) - -z) := by rw [sub_eq_add_neg (1:ℂ)];ring
    simp only [corrTerm,if_pos hk]
    change ‖-Complex.log (1-z)-z‖≤_
    rw [he,norm_neg]
    apply hl.trans
    have hi : (1-‖z‖)⁻¹ ≤ 2 := by
      rw [inv_le_comm₀ (by linarith) (by norm_num)]
      norm_num
      linarith
    calc ‖z‖^2*(1-‖z‖)⁻¹/2 ≤ ‖z‖^2*2/2 := by gcongr
         _ ≤ ((k:ℝ)⁻¹)^2 := by rw [mul_div_cancel_right₀ _ (by norm_num)];gcongr
         _ = _ := by rw [inv_pow,one_div]
  · simp [corrTerm,hk]

private theorem corr_cont (k : ℕ) : ContinuousOn (corrTerm k) {w : ℂ | 1≤w.re} := by
  by_cases hk : k.Prime
  · have hp : Continuous (fun w : ℂ => (k:ℂ)^(-w)) :=
      continuous_id.neg.const_cpow (.inl (by exact_mod_cast hk.ne_zero))
    change ContinuousOn (fun w => corrTerm k w) _
    simp only [corrTerm,if_pos hk]
    apply ContinuousOn.sub _ hp.continuousOn
    apply ContinuousOn.neg
    intro w hw
    have hh := (pow_bd k hk w hw).1.trans (pow_bd k hk w hw).2
    have hsl : 1-(k:ℂ)^(-w) ∈ Complex.slitPlane := by
      apply Complex.mem_slitPlane_iff.mpr (.inl _)
      simp only [Complex.sub_re,Complex.one_re]
      linarith [Complex.re_le_norm ((k:ℂ)^(-w))]
    have hc : Continuous (fun v : ℂ => 1-(k:ℂ)^(-v)) := continuous_const.sub hp
    exact (continuousAt_clog hsl).comp_continuousWithinAt (f:=fun v : ℂ => 1-(k:ℂ)^(-v)) hc.continuousAt.continuousWithinAt
  · change ContinuousOn (fun w => corrTerm k w) _
    simpa only [corrTerm,if_neg hk] using (continuousOn_const : ContinuousOn (fun _ : ℂ=> (0:ℂ)) _)

private def sector (a b : ℝ) := {w : ℂ | 1≤w.re ∧ a≤|w.im| ∧ ‖w‖≤b}
private def logPart (n : ℕ) (w : ℂ) :=
  (∑ k ∈ Finset.range (n+1),mainTerm k w)+(∑ k ∈ Finset.range (n+1),corrTerm k w)
private def prodPart (n : ℕ) (w : ℂ) :=
    ∏ k ∈ (n+1).primesBelow,(1-(k:ℂ)^(-w))⁻¹
private theorem log_uniform (a b : ℝ) (ha : 0<a) :
    TendstoUniformlyOn logPart logLim atTop (sector a b) := by
  have hm := main_uniform (sector a b) a b ha fun _ h => h
  have ht := tendstoUniformlyOn_tsum_nat (f := corrTerm)
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
    (s := sector a b) (fun k w hw => corr_bd k hw.1)
  have ht' : TendstoUniformlyOn (fun n w => ∑ k ∈ Finset.range (n+1),corrTerm k w)
      (fun w => ∑' k : ℕ,corrTerm k w) atTop (sector a b) :=
    fun u hu => (tendsto_add_atTop_nat 1).eventually (ht u hu)
  exact hm.add ht'

private theorem log_cont (a b : ℝ) (ha : 0<a) : ContinuousOn logLim (sector a b) := by
  apply (log_uniform a b ha).continuousOn (Frequently.of_forall fun n => ?_)
  unfold logPart
  exact (continuousOn_finsetSum _ fun k _ => (main_cont k).continuousOn).add
    (continuousOn_finsetSum _ fun k _ => (corr_cont k).mono fun _ h => h.1)

private theorem exp_logPart (n : ℕ) {w : ℂ} (hw : 1≤w.re) :
    Complex.exp (logPart n w)=prodPart n w := by
  unfold logPart prodPart
  rw [←Finset.sum_add_distrib,Complex.exp_sum,Nat.primesBelow,Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro k hk
  by_cases h : k.Prime
  · have hbd := (pow_bd k h w hw).1.trans (pow_bd k h w hw).2
    have hn : 1-(k:ℂ)^(-w) ≠ 0 := by
      intro hn
      have he := (sub_eq_zero.mp hn).symm
      rw [he,norm_one] at hbd
      norm_num at hbd
    simp only [mainTerm,corrTerm,if_pos h]
    rw [show (k:ℂ)^(-w)+(-Complex.log (1-(k:ℂ)^(-w))-(k:ℂ)^(-w)) =
          -Complex.log (1-(k:ℂ)^(-w)) by ring,Complex.exp_neg,Complex.exp_log hn]
  · simp [mainTerm,corrTerm,h]

private theorem sector_compact (a b : ℝ) : IsCompact (sector a b) := by
  apply (isCompact_closedBall (0:ℂ) b).of_isClosed_subset
  · exact (isClosed_le continuous_const Complex.continuous_re).inter
      ((isClosed_le continuous_const Complex.continuous_im.abs).inter (isClosed_le continuous_norm continuous_const))
  · intro w hw
    simpa only [Metric.mem_closedBall,dist_zero_right] using hw.2.2

private theorem prod_uniform_aux (a b : ℝ) (ha : 0<a) :
    TendstoUniformlyOn prodPart (fun w => Complex.exp (logLim w)) atTop (sector a b) := by
  obtain ⟨C,hC⟩ := (sector_compact a b).exists_bound_of_continuousOn
    (Complex.continuous_exp.comp_continuousOn (log_cont a b ha))
  let B := max C 1
  have hB : 0<B := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hδ : 0 < min 1 (ε/(2*B)) := lt_min zero_lt_one (by positivity)
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp (log_uniform a b ha) _ hδ] with n hn w hw
  have hh := hn w hw
  rw [dist_comm,dist_eq_norm] at hh
  rw [dist_comm,dist_eq_norm,←exp_logPart n hw.1]
  have he : Complex.exp (logPart n w)-Complex.exp (logLim w)=
      (Complex.exp (logPart n w-logLim w)-1)*Complex.exp (logLim w) := by
    rw [sub_mul,←Complex.exp_add,sub_add_cancel,one_mul]
  have hz := Complex.norm_exp_sub_one_le (hh.le.trans (min_le_left _ _))
  have hfac : ‖Complex.exp (logLim w)‖ ≤ B := (hC w hw).trans (le_max_left _ _)
  rw [he,norm_mul]
  calc _ ≤ (2*‖logPart n w-logLim w‖)*B := by gcongr
       _ < ε := by
         have h := (lt_div_iff₀ (by positivity : 0<2*B)).mp (lt_of_lt_of_le hh (min_le_right _ _))
         linarith [show 2*‖logPart n w-logLim w‖*B=‖logPart n w-logLim w‖*(2*B) by ring]

private theorem exp_log_interior {w : ℂ} (hr : 1<w.re) (hi : w.im≠0) :
    Complex.exp (logLim w)=riemannZeta w := by
  have hw : w∈sector |w.im| ‖w‖ := ⟨hr.le,le_rfl,le_rfl⟩
  exact tendsto_nhds_unique ((prod_uniform_aux _ _ (abs_pos.mpr hi)).tendsto_at hw)
    ((riemannZeta_eulerProduct hr).comp (tendsto_add_atTop_nat 1))

private theorem exp_log_closed {w : ℂ} (hr : 1≤w.re) (hi : w.im≠0) :
    Complex.exp (logLim w)=riemannZeta w := by
  let d (n : ℕ) : ℝ := 1/((n:ℝ)+1)
  let u (n : ℕ) : ℂ := w+(d n:ℂ)
  have hd (n : ℕ) : 0<d n := by dsimp [d];positivity
  have hb (n : ℕ) : d n≤1 := by
    dsimp [d]; apply (div_le_one (by positivity)).mpr;linarith [Nat.cast_nonneg (α := ℝ) n]
  have hu : Tendsto u atTop (𝓝 w) := by
    simpa [u,d] using tendsto_const_nhds (x := w) |>.add
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜:=ℝ)))
  have huim (n : ℕ) : (u n).im=w.im := by simp [u]
  have hure (n : ℕ) : 1<(u n).re := by simp [u]; linarith [hd n]
  let K := sector |w.im| (‖w‖+1)
  have hw : w∈K := ⟨hr,le_rfl,by linarith⟩
  have huk (n : ℕ) : u n∈K := ⟨(hure n).le,by rw [huim],by
    calc ‖u n‖ ≤ ‖w‖ + ‖(d n:ℂ)‖ := norm_add_le _ _
         _ ≤ _ := by rw [Complex.norm_real,Real.norm_of_nonneg (hd n).le];gcongr;exact hb n⟩
  have hn : w≠1 := fun h => hi (by simp [h])
  have h1 := ((Complex.continuous_exp.comp_continuousOn (log_cont _ _ (abs_pos.mpr hi))) w hw).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hu,Eventually.of_forall huk⟩)
  have h2 := (differentiableAt_riemannZeta hn).continuousAt.tendsto.comp hu
  exact tendsto_nhds_unique (h1.congr fun n => exp_log_interior (hure n) (huim n ▸ hi)) h2

end
end EulerOneLine

open EulerOneLine in
theorem solution (a b : ℝ) (ha : 0<a) :
    TendstoUniformlyOn (fun n : ℕ => fun w : ℂ => ∏ p ∈ (n+1).primesBelow,(1-(p:ℂ)^(-w))⁻¹)
      riemannZeta atTop {w : ℂ | 1≤w.re ∧ a≤|w.im| ∧ ‖w‖≤b} := by
  exact (prod_uniform_aux a b ha).congr_right fun w hw => exp_log_closed hw.1
    (abs_pos.mp (ha.trans_le hw.2.1))
