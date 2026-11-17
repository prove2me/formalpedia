-- Prove2me | solution 1 for N25.etaAnalytic25_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:32:35.958816+00:00
-- url     : https://prove2.me/submissions/0fb5685b-8d94-43cd-b691-2a8b53fcb392

import Mathlib
import Definitions.Def_N25_UnitAnalytic

set_option autoImplicit false

namespace N25

private theorem geometric_stream (a b : ℂ) (ha : ‖a‖ < 1)
    (hab : ‖a‖ * ‖b‖ < 1) :
    Multipliable (fun n : ℕ => 1 - a ^ (n + 1) * b) ∧
      (∏' n : ℕ, (1 - a ^ (n + 1) * b)) ≠ 0 := by
  have hs : Summable (fun n : ℕ => ‖-(a ^ (n + 1) * b)‖) := by
    simpa only [norm_neg, norm_mul, norm_pow] using
      ((summable_nat_add_iff 1).mpr
        (summable_geometric_of_lt_one (norm_nonneg a) ha)).mul_right ‖b‖
  have hne : ∀ n : ℕ, 1 + -(a ^ (n + 1) * b) ≠ 0 := by
    intro n h
    have hp : ‖a‖ ^ n ≤ 1 := pow_le_one₀ (norm_nonneg a) ha.le
    have hlt : ‖a ^ (n + 1) * b‖ < 1 := by
      calc
        ‖a ^ (n + 1) * b‖ = ‖a‖ ^ n * (‖a‖ * ‖b‖) := by
          rw [norm_mul, norm_pow, pow_succ]; ring
        _ ≤ 1 * (‖a‖ * ‖b‖) :=
          mul_le_mul_of_nonneg_right hp (mul_nonneg (norm_nonneg a) (norm_nonneg b))
        _ < 1 := by simpa using hab
    have heq : a ^ (n + 1) * b = 1 := (sub_eq_zero.mp (by simpa [sub_eq_add_neg] using h)).symm
    rw [heq, norm_one] at hlt
    exact lt_irrefl _ hlt
  simpa only [sub_eq_add_neg] using
    And.intro (multipliable_one_add_of_summable hs)
      (tprod_one_add_ne_zero_of_summable hne hs)

private theorem exponential_norm (r : ℝ) (τ : UpperHalfPlane) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))‖ =
      Real.exp (-2 * Real.pi * r * (τ : ℂ).im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

private theorem exponential_norm_lt_one (r : ℝ) (hr : 0 < r) (τ : UpperHalfPlane) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (τ : ℂ))‖ < 1 := by
  rw [exponential_norm, Real.exp_lt_one_iff]
  have h := mul_pos (mul_pos Real.pi_pos hr) τ.im_pos
  change 0 < Real.pi * r * (τ : ℂ).im at h
  nlinarith

/-- The unpowered residue factors have no zeros in the upper half-plane. -/
theorem _root_.solution (g : ℕ) (hg : 0 < g) (hg25 : g < 25)
    (τ : UpperHalfPlane) : etaAnalytic25 g τ ≠ 0 := by
  let a := Complex.exp (2 * Real.pi * Complex.I * (25 : ℂ) * (τ : ℂ))
  let b := Complex.exp (2 * Real.pi * Complex.I * (g : ℂ) * (τ : ℂ))
  have ha : ‖a‖ < 1 := exponential_norm_lt_one 25 (by norm_num) τ
  have hb : ‖b‖ < 1 := exponential_norm_lt_one g (by exact_mod_cast hg) τ
  have hab : ‖a‖ * ‖b‖ < 1 :=
    (mul_le_mul_of_nonneg_right ha.le (norm_nonneg b)).trans_lt (by simpa using hb)
  have habi : ‖a‖ * ‖b⁻¹‖ < 1 := by
    rw [norm_inv]
    change ‖Complex.exp (2 * Real.pi * Complex.I * ((25 : ℝ) : ℂ) * (τ : ℂ))‖ *
      ‖Complex.exp (2 * Real.pi * Complex.I * ((g : ℝ) : ℂ) * (τ : ℂ))‖⁻¹ < 1
    rw [exponential_norm, exponential_norm, ← Real.exp_neg, ← Real.exp_add,
      Real.exp_lt_one_iff]
    have hdiff : 0 < (25 : ℝ) - g := sub_pos.mpr (by exact_mod_cast hg25)
    have h := mul_pos (mul_pos Real.pi_pos hdiff) τ.im_pos
    change 0 < Real.pi * (25 - (g : ℝ)) * (τ : ℂ).im at h
    nlinarith
  have hs := geometric_stream a b ha hab
  have hsi := geometric_stream a b⁻¹ ha habi
  have hprod : (∏' n : ℕ, ((1 - a ^ (n + 1) * b) *
      (1 - a ^ (n + 1) * b⁻¹))) ≠ 0 := by
    rw [hs.1.tprod_mul hsi.1]
    exact mul_ne_zero hs.2 hsi.2
  have hfactor : 1 - b ≠ 0 := by
    intro h
    have h' : b = 1 := (sub_eq_zero.mp h).symm
    rw [h', norm_one] at hb
    exact lt_irrefl _ hb
  have harg : Complex.exp (2 * Real.pi * Complex.I *
      (((g : ℤ) : ℂ) * (25 * (τ : ℂ)) + (0 : ℤ)) / ((25 : ℕ) : ℂ)) = b := by
    congr 1
    push_cast
    ring
  have haarg : Complex.exp (2 * Real.pi * Complex.I * (25 * (τ : ℂ))) = a := by
    congr 1
    ring
  unfold etaAnalytic25
  rw [ModularCurve.siegelFun_def, harg, haarg]
  exact neg_ne_zero.mpr (mul_ne_zero
    (mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero _))
      (Complex.exp_ne_zero _)) hfactor) hprod)

end N25
