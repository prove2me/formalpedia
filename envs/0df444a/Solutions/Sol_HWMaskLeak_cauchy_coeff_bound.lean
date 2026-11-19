-- Prove2me | solution 1 for HWMaskLeak.cauchy_coeff_bound
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T07:31:32.248863+00:00
-- url     : https://prove2.me/submissions/fbd42820-d0c3-41f8-803a-0bea8bc4b718

import Mathlib

open Polynomial Complex

lemma int_exp_orth (m : ℤ) :
    ∫ θ in (-Real.pi)..Real.pi, Complex.exp ((m : ℂ) * I * (θ : ℂ)) =
      if m = 0 then (2 * Real.pi : ℂ) else 0 := by
  split_ifs with hm
  · subst hm; simp; ring
  · have hc : (m : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hm) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((m : ℂ) * I * (Real.pi : ℂ)) = Complex.exp ((m : ℂ) * I * ((-Real.pi : ℝ) : ℂ)) := by
      have h2 := Complex.exp_int_mul_two_pi_mul_I m
      have : (m : ℂ) * I * (Real.pi : ℂ) = (m : ℂ) * I * ((-Real.pi : ℝ) : ℂ) + m * (2 * Real.pi * I) := by
        push_cast; ring
      rw [this, Complex.exp_add, h2, mul_one]
    rw [h1, sub_self, zero_div]

lemma coeff_formula (P : ℂ[X]) (r : ℝ) (hr : 0 < r) (w : ℕ) :
    P.coeff w = 1 / ((2 * Real.pi * r ^ w : ℝ) : ℂ) *
      ∫ θ in (-Real.pi)..Real.pi,
        P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I) := by
  set N := max P.natDegree w + 1 with hN
  have hPN : P.natDegree < N := by omega
  have hexp : ∀ θ : ℝ, P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I) =
      ∑ k ∈ Finset.range N, P.coeff k * (r : ℂ) ^ k *
        Complex.exp ((((k : ℤ) - (w : ℤ) : ℤ) : ℂ) * I * (θ : ℂ)) := by
    intro θ
    rw [eval_eq_sum_range' hPN, Finset.sum_mul]
    apply Finset.sum_congr rfl; intro k _
    rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, mul_assoc, ← Complex.exp_add]
    push_cast
    ring_nf
  simp_rw [hexp]
  rw [intervalIntegral.integral_finset_sum (fun k _ => by
    apply Continuous.intervalIntegrable; fun_prop)]
  simp_rw [intervalIntegral.integral_const_mul, int_exp_orth]
  rw [Finset.sum_eq_single w]
  · simp only [sub_self, if_true]
    have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    push_cast
    field_simp
  · intro k _ hk
    rw [if_neg (by omega), mul_zero]
  · intro hw; exact absurd (Finset.mem_range.mpr (by omega)) hw

theorem solution (n : ℕ) (ξ : Fin n → ℂ) (hξ : ∀ j, ‖ξ j‖ = 1) (P : ℂ[X])
    (hP : P = ∏ j, (1 + X * C (ξ j))) :
    (∀ r : ℝ, 0 < r → ∀ w : ℕ,
      P.coeff w = 1 / ((2 * Real.pi * r ^ w : ℝ) : ℂ) *
        ∫ θ in (-Real.pi)..Real.pi,
          P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
            Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I)) ∧
    (∀ w : ℕ, 0 < w → w < n →
      ‖P.coeff w‖ ≤
        1 / (2 * Real.pi * ((w : ℝ) / n) ^ w * (1 - (w : ℝ) / n) ^ (n - w)) *
          ∫ θ in (-Real.pi)..Real.pi,
            ∏ j, ‖((1 - (w : ℝ) / n : ℝ) : ℂ) + (((w : ℝ) / n : ℝ) : ℂ) * ξ j *
              Complex.exp ((θ : ℂ) * Complex.I)‖) := by
  refine ⟨fun r hr w => coeff_formula P r hr w, fun w hw hwn => ?_⟩
  have hn : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  set p : ℝ := (w : ℝ) / n with hp
  have hp0 : 0 < p := by rw [hp]; exact div_pos (by exact_mod_cast hw) hn
  have hp1 : p < 1 := by rw [hp, div_lt_one hn]; exact_mod_cast hwn
  have h1p : 0 < 1 - p := by linarith
  set r : ℝ := p / (1 - p) with hr
  have hr0 : 0 < r := div_pos hp0 h1p
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [coeff_formula P r hr0 w, norm_mul]
  have hA : ∀ θ : ℝ, ‖P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I)‖ =
      (∏ j, ‖((1 - p : ℝ) : ℂ) + ((p : ℝ) : ℂ) * ξ j * Complex.exp ((θ : ℂ) * Complex.I)‖) /
        (1 - p) ^ n := by
    intro θ
    rw [norm_mul, Complex.norm_exp]
    have hre : (-((w : ℂ) * (θ : ℂ)) * Complex.I).re = 0 := by simp
    rw [hre, Real.exp_zero, mul_one, hP, eval_prod, norm_prod]
    rw [show (1 - p) ^ n = ∏ _j : Fin n, (1 - p) by simp, ← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl; intro j _
    simp only [eval_add, eval_one, eval_mul, eval_X, eval_C]
    have hkey : (1:ℂ) + (r:ℂ) * Complex.exp ((θ:ℂ) * I) * ξ j =
        (((1 - p : ℝ) : ℂ) + ((p:ℝ):ℂ) * ξ j * Complex.exp ((θ:ℂ) * I)) / ((1 - p : ℝ) : ℂ) := by
      have : ((1 - p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast h1p.ne'
      rw [hr]; push_cast
      have h' : (1:ℂ) - (p:ℂ) ≠ 0 := by exact_mod_cast h1p.ne'
      field_simp
    rw [hkey, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h1p]
  have hle := intervalIntegral.norm_integral_le_integral_norm (μ := MeasureTheory.volume)
    (f := fun θ : ℝ => P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
      Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I)) (by linarith : -Real.pi ≤ Real.pi)
  simp_rw [hA] at hle
  rw [intervalIntegral.integral_div] at hle
  have hconst : ‖(1 : ℂ) / ((2 * Real.pi * r ^ w : ℝ) : ℂ)‖ = 1 / (2 * Real.pi * r ^ w) := by
    rw [norm_div, norm_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hconst]
  set J := ∫ θ in (-Real.pi)..Real.pi,
    ∏ j, ‖((1 - p : ℝ) : ℂ) + ((p : ℝ) : ℂ) * ξ j * Complex.exp ((θ : ℂ) * Complex.I)‖ with hJ
  have hJ0 : 0 ≤ J := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro θ _; exact Finset.prod_nonneg (fun j _ => norm_nonneg _)
  calc 1 / (2 * Real.pi * r ^ w) * ‖∫ θ in (-Real.pi)..Real.pi,
        P.eval ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) *
          Complex.exp (-((w : ℂ) * (θ : ℂ)) * Complex.I)‖
      ≤ 1 / (2 * Real.pi * r ^ w) * (J / (1 - p) ^ n) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = 1 / (2 * Real.pi * p ^ w * (1 - p) ^ (n - w)) * J := by
        have hsplit : (1 - p) ^ n = (1 - p) ^ w * (1 - p) ^ (n - w) := by
          rw [← pow_add]; congr 1; omega
        rw [hr, div_pow, hsplit]
        field_simp
