-- Prove2me | solution 1 for IntMul.HvdH.rho_bounds
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-11T20:47:54.076661+00:00
-- url     : https://prove2.me/submissions/4d221013-cab3-431b-b007-a5c6da650634

import Definitions.Def_IntMul_HvdH_FixedPoint

namespace IntMul.HvdH.FP
open IntMul.HvdH

lemma rho0_abs_le (x : ℝ) : |((rho0 x : ℤ) : ℝ)| ≤ |x| := by
  unfold rho0
  split_ifs with h
  · rw [abs_of_nonneg (by exact_mod_cast Int.floor_nonneg.2 h), abs_of_nonneg h]
    exact Int.floor_le x
  · push Not at h
    have h1 : ((⌈x⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast Int.ceil_le.2 (by simpa using h.le)
    rw [abs_of_nonpos h1, abs_of_neg h]
    linarith [Int.le_ceil x]

lemma rho0_sub_lt (x : ℝ) : |((rho0 x : ℤ) : ℝ) - x| < 1 := by
  unfold rho0
  split_ifs with h
  · rw [abs_lt]; constructor <;> linarith [Int.floor_le x, Int.lt_floor_add_one x]
  · rw [abs_lt]; constructor <;> linarith [Int.le_ceil x, Int.ceil_lt_add_one x]

/-- If `2x ∈ ℤ` then rounding towards zero moves `x` by at most `1/2`. -/
lemma rho0_sub_half (x : ℝ) (hx : ∃ n : ℤ, 2 * x = n) : |((rho0 x : ℤ) : ℝ) - x| ≤ 1 / 2 := by
  obtain ⟨n, hn⟩ := hx
  rcases Int.emod_two_eq_zero_or_one n with h | h
  · have : x = ((n / 2 : ℤ) : ℝ) := by
      have := Int.mul_ediv_add_emod n 2
      rw [h, add_zero] at this
      have e : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) := by exact_mod_cast this.symm
      linarith
    rw [this]; unfold rho0
    split_ifs <;> simp
  · have hx : x = ((n / 2 : ℤ) : ℝ) + 1 / 2 := by
      have := Int.mul_ediv_add_emod n 2
      rw [h] at this
      have e : (n : ℝ) = 1 + 2 * ((n / 2 : ℤ) : ℝ) := by
        have e' : (n : ℝ) = 2 * ((n / 2 : ℤ) : ℝ) + 1 := by exact_mod_cast this.symm
        linarith
      linarith
    set m := n / 2
    unfold rho0
    split_ifs with h0
    · have : ⌊x⌋ = m := by rw [Int.floor_eq_iff, hx]; constructor <;> linarith
      rw [this, hx, abs_le]; constructor <;> linarith
    · have : ⌈x⌉ = m + 1 := by
        rw [Int.ceil_eq_iff, hx]; push_cast; constructor <;> linarith
      rw [this, hx, abs_le]; push_cast; constructor <;> linarith

lemma norm_rho0C_le (u : ℂ) : ‖rho0C u‖ ≤ ‖u‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  have h1 := rho0_abs_le u.re
  have h2 := rho0_abs_le u.im
  have hre : (rho0C u).re = rho0 u.re := by simp [rho0C]
  have him : (rho0C u).im = rho0 u.im := by simp [rho0C]
  rw [hre, him]
  nlinarith [sq_abs ((rho0 u.re : ℤ) : ℝ), sq_abs u.re, sq_abs ((rho0 u.im : ℤ) : ℝ), sq_abs u.im,
    abs_nonneg ((rho0 u.re : ℤ) : ℝ), abs_nonneg ((rho0 u.im : ℤ) : ℝ)]

lemma norm_rho0C_sub_lt (u : ℂ) : ‖rho0C u - u‖ < Real.sqrt 2 := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_lt_sqrt (by positivity)
  have h1 := rho0_sub_lt u.re
  have h2 := rho0_sub_lt u.im
  simp only [rho0C, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, zero_mul]
  have a1 : (((rho0 u.re : ℤ) : ℝ) - u.re) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.re : ℤ) : ℝ) - u.re)]
  have a2 : (((rho0 u.im : ℤ) : ℝ) - u.im) ^ 2 < 1 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.im : ℤ) : ℝ) - u.im)]
  linarith

lemma norm_rho0C_sub_half (u : ℂ) (hre : ∃ n : ℤ, 2 * u.re = n) (him : ∃ n : ℤ, 2 * u.im = n) :
    ‖rho0C u - u‖ ≤ Real.sqrt 2 / 2 := by
  have hs : Real.sqrt (1 / 2) = Real.sqrt 2 / 2 := by
    rw [show (1 / 2 : ℝ) = 2 / 2 ^ 2 by norm_num, Real.sqrt_div' _ (by positivity),
      Real.sqrt_sq (by norm_num)]
  rw [Complex.norm_eq_sqrt_sq_add_sq, ← hs]
  apply Real.sqrt_le_sqrt
  have h1 := rho0_sub_half u.re hre
  have h2 := rho0_sub_half u.im him
  simp only [rho0C, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.intCast_re, Complex.intCast_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
    Complex.I_im]
  simp only [mul_zero, sub_zero, mul_one, zero_add, add_zero, zero_mul]
  have a1 : (((rho0 u.re : ℤ) : ℝ) - u.re) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.re : ℤ) : ℝ) - u.re)]
  have a2 : (((rho0 u.im : ℤ) : ℝ) - u.im) ^ 2 ≤ 1 / 4 := by
    rw [← sq_abs]; nlinarith [abs_nonneg (((rho0 u.im : ℤ) : ℝ) - u.im)]
  linarith

/-- `|ρ(u)| ≤ |u|` and `|ρ(u) - u| < √2 · 2^{-p}`. -/
theorem rho_bounds (p : ℕ) (u : ℂ) :
    ‖rho p u‖ ≤ ‖u‖ ∧ ‖rho p u - u‖ < Real.sqrt 2 * ((2 : ℝ) ^ p)⁻¹ := by
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  have hn : ‖(2 : ℂ) ^ p‖ = 2 ^ p := by simp
  constructor
  · unfold rho
    rw [norm_mul, norm_inv, hn]
    calc ((2 : ℝ) ^ p)⁻¹ * ‖rho0C ((2 : ℂ) ^ p * u)‖ ≤ ((2 : ℝ) ^ p)⁻¹ * ‖(2 : ℂ) ^ p * u‖ :=
          mul_le_mul_of_nonneg_left (norm_rho0C_le _) (by positivity)
      _ = ‖u‖ := by rw [norm_mul, hn, ← mul_assoc, inv_mul_cancel₀ h2.ne', one_mul]
  · have e : rho p u - u = ((2 : ℂ) ^ p)⁻¹ * (rho0C ((2 : ℂ) ^ p * u) - (2 : ℂ) ^ p * u) := by
      unfold rho; field_simp
    rw [e, norm_mul, norm_inv, hn, mul_comm (Real.sqrt 2)]
    exact mul_lt_mul_of_pos_left (norm_rho0C_sub_lt _) (by positivity)

/-- **Lemma 2.2 (scaling), error part.** If `‖u‖ ≤ 1/c` then `ṽ = scaleFP p c ũ` lies in the unit
disc and `2^p ‖ṽ - c u‖ < 2 c · 2^p ‖ũ - u‖ + 3`. -/
theorem scaleFP_bound (p c : ℕ) (hc : 1 ≤ c) (u ũ : ℂ) (hu : ‖u‖ ≤ (c : ℝ)⁻¹) :
    ‖scaleFP p c ũ‖ ≤ 1 ∧
      (2 : ℝ) ^ p * ‖scaleFP p c ũ - c * u‖ < 2 * c * ((2 : ℝ) ^ p * ‖ũ - u‖) + 3 := by
  have hc0 : (0 : ℝ) < c := by exact_mod_cast hc
  have h2 : (0 : ℝ) < 2 ^ p := by positivity
  set w := (c : ℂ) * ũ with hw
  have hv : ‖(c : ℂ) * u‖ ≤ 1 := by
    rw [norm_mul, Complex.norm_natCast]
    calc (c : ℝ) * ‖u‖ ≤ c * (c : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hu hc0.le
      _ = 1 := mul_inv_cancel₀ hc0.ne'
  have hwv : ‖w - c * u‖ = c * ‖ũ - u‖ := by
    rw [hw, ← mul_sub, norm_mul, Complex.norm_natCast]
  have hε : 0 ≤ (2 : ℝ) ^ p * ‖ũ - u‖ := by positivity
  unfold scaleFP
  rw [← hw]
  split_ifs with hw1
  · refine ⟨hw1, ?_⟩
    rw [hwv]
    nlinarith
  · push Not at hw1
    set B : ℝ := ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℝ) with hB
    have hB1 : (2 : ℝ) ^ p * ‖w‖ ≤ B := Int.le_ceil _
    have hB2 : B < (2 : ℝ) ^ p * ‖w‖ + 1 := Int.ceil_lt_add_one _
    have hBp : (2 : ℝ) ^ p < B := by nlinarith
    have hB0 : 0 < B := by linarith
    set z : ℂ := (((2 : ℝ) ^ p / B : ℝ) : ℂ) * w with hz
    have hzdef : (2 : ℂ) ^ p * w / ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℂ) = z := by
      rw [hz]
      have : ((⌈(2 : ℝ) ^ p * ‖w‖⌉ : ℤ) : ℂ) = (B : ℂ) := by rw [hB]; push_cast; rfl
      rw [this]; push_cast; ring
    rw [hzdef]
    have hzn : ‖z‖ ≤ 1 := by
      rw [hz, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity),
        div_mul_eq_mul_div, div_le_one hB0]
      exact hB1
    obtain ⟨hr1, hr2⟩ := rho_bounds p z
    refine ⟨hr1.trans hzn, ?_⟩
    have hzw : (2 : ℝ) ^ p * ‖z - w‖ ≤ B - 2 ^ p := by
      have e : z - w = (((2 : ℝ) ^ p / B - 1 : ℝ) : ℂ) * w := by rw [hz]; push_cast; ring
      have hneg : (2 : ℝ) ^ p / B - 1 ≤ 0 := by
        rw [div_sub_one hB0.ne']; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hB0.le
      rw [e, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos hneg]
      have hq : -((2 : ℝ) ^ p / B - 1) = (B - 2 ^ p) / B := by field_simp; ring
      rw [hq, div_mul_eq_mul_div, mul_div_assoc', div_le_iff₀ hB0]
      have := mul_le_mul_of_nonneg_left hB1 (show 0 ≤ B - 2 ^ p by linarith)
      nlinarith [norm_nonneg w]
    have hwle : ‖w‖ ≤ 1 + ‖w - c * u‖ := by
      calc ‖w‖ = ‖(c * u) + (w - c * u)‖ := by ring_nf
        _ ≤ ‖(c : ℂ) * u‖ + ‖w - c * u‖ := norm_add_le _ _
        _ ≤ 1 + ‖w - c * u‖ := by linarith
    have htri : ‖rho p z - c * u‖ ≤ ‖rho p z - z‖ + ‖z - w‖ + ‖w - c * u‖ := by
      calc ‖rho p z - c * u‖ = ‖(rho p z - z) + (z - w) + (w - c * u)‖ := by ring_nf
        _ ≤ ‖(rho p z - z) + (z - w)‖ + ‖w - c * u‖ := norm_add_le _ _
        _ ≤ ‖rho p z - z‖ + ‖z - w‖ + ‖w - c * u‖ := by gcongr; exact norm_add_le _ _
    have hs2 : Real.sqrt 2 < 2 := by
      rw [show (2 : ℝ) = Real.sqrt 4 by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      · exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    have hr2' : (2 : ℝ) ^ p * ‖rho p z - z‖ < Real.sqrt 2 := by
      have := mul_lt_mul_of_pos_left hr2 h2
      rwa [mul_comm (Real.sqrt 2), ← mul_assoc, mul_inv_cancel₀ h2.ne', one_mul] at this
    rw [hwv] at hwle htri
    have hpw : (2 : ℝ) ^ p * ‖w‖ ≤ 2 ^ p + c * ((2 : ℝ) ^ p * ‖ũ - u‖) := by nlinarith
    calc (2 : ℝ) ^ p * ‖rho p z - c * u‖
        ≤ (2 : ℝ) ^ p * ‖rho p z - z‖ + (2 : ℝ) ^ p * ‖z - w‖ + c * ((2 : ℝ) ^ p * ‖ũ - u‖) := by
          nlinarith
      _ < 2 * c * ((2 : ℝ) ^ p * ‖ũ - u‖) + 3 := by nlinarith

end IntMul.HvdH.FP

theorem solution (p : ℕ) (u : ℂ) :
    ‖IntMul.HvdH.rho p u‖ ≤ ‖u‖ ∧ ‖IntMul.HvdH.rho p u - u‖ < Real.sqrt 2 * ((2 : ℝ) ^ p)⁻¹ :=
  IntMul.HvdH.FP.rho_bounds p u
