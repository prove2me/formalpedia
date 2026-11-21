-- Prove2me | solution 1 for MomentSearch.eq_11
-- status  : ACCEPTED   (prove)
-- author  : @nmegow
-- created : 2026-11-20T22:54:36.858696+00:00
-- url     : https://prove2.me/submissions/3f007763-e76a-488a-a7d3-fd2ec772733f

import Mathlib
import Theorems.Thm_bernstein_unit

open Polynomial
open scoped Topology

theorem solution (k : ℕ) (q : Polynomial ℝ) (hq : q.natDegree ≤ k) (ρ B : ℝ) (hρ : 0 < ρ)
    (hB : ∀ x ∈ Set.Icc (-ρ) ρ, |q.eval x| ≤ B) :
    ∀ x ∈ Set.Ioo (-ρ) ρ,
      |(Polynomial.derivative q).eval x| ≤ (k : ℝ) * B / Real.sqrt (ρ ^ 2 - x ^ 2) := by
  intro x hx
  have hBnonneg : 0 ≤ B :=
    (abs_nonneg _).trans (hB 0 ⟨by linarith, hρ.le⟩)
  by_cases hBzero : B = 0
  · have heq : (fun y : ℝ => q.eval y) =ᶠ[𝓝 x] (fun _ => 0) := by
      filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
      have hh := hB y ⟨hy.1.le, hy.2.le⟩
      rw [hBzero, abs_nonpos_iff] at hh
      exact hh
    have hzero := (q.hasDerivAt x).unique ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq heq)
    simp [hzero, hBzero]
  have hBp : 0 < B := lt_of_le_of_ne hBnonneg (Ne.symm hBzero)
  let s : Polynomial ℝ := C ρ * X
  let Q : Polynomial ℝ := C B⁻¹ * q.comp s
  have hQdeg : Q.natDegree ≤ k := by
    calc
      Q.natDegree ≤ (q.comp s).natDegree := natDegree_C_mul_le _ _
      _ ≤ q.natDegree * s.natDegree := natDegree_comp_le
      _ = q.natDegree := by simp [s, natDegree_C_mul_X _ hρ.ne']
      _ ≤ k := hq
  have hQ (y : ℝ) (hy₁ : -1 ≤ y) (hy₂ : y ≤ 1) : |Q.eval y| ≤ 1 := by
    have hmem : ρ * y ∈ Set.Icc (-ρ) ρ := by
      constructor
      · simpa using mul_le_mul_of_nonneg_left hy₁ hρ.le
      · simpa using mul_le_mul_of_nonneg_left hy₂ hρ.le
    simp only [Q, s, eval_mul, eval_C, eval_comp, eval_X, abs_mul, abs_inv,
      abs_of_pos hBp]
    calc
      B⁻¹ * |q.eval (ρ * y)| ≤ B⁻¹ * B := mul_le_mul_of_nonneg_left (hB _ hmem) (by positivity)
      _ = 1 := inv_mul_cancel₀ hBzero
  have hy₁ : -1 ≤ x / ρ := (le_div_iff₀ hρ).2 (by simpa using hx.1.le)
  have hy₂ : x / ρ ≤ 1 := (div_le_iff₀ hρ).2 (by simpa using hx.2.le)
  have hderiv : Q.derivative.eval (x / ρ) = B⁻¹ * (ρ * q.derivative.eval x) := by
    have harg : ρ * (x / ρ) = x := by field_simp
    simp [Q, s, derivative_mul, derivative_comp, harg]
  have hunit := bernstein_unit Q hQdeg hQ (x / ρ) hy₁ hy₂
  rw [hderiv] at hunit
  have hsq :
      (ρ ^ 2 - x ^ 2) * (q.derivative.eval x) ^ 2 ≤ ((k : ℝ) * B) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hunit (sq_nonneg B)
    have hleft :
        (1 - (x / ρ) ^ 2) * (B⁻¹ * (ρ * q.derivative.eval x)) ^ 2 * B ^ 2 =
          (ρ ^ 2 - x ^ 2) * (q.derivative.eval x) ^ 2 := by
      field_simp [hρ.ne', hBzero]
    rw [hleft] at hmul
    simpa only [mul_pow] using hmul
  have hrad : 0 < ρ ^ 2 - x ^ 2 := by
    have hprod : 0 < (ρ - x) * (ρ + x) := mul_pos (sub_pos.mpr hx.2) (by linarith [hx.1])
    nlinarith only [hprod]
  have hsqrt := Real.sqrt_pos.2 hrad
  apply (le_div_iff₀ hsqrt).2
  apply (sq_le_sq₀ (mul_nonneg (abs_nonneg _) hsqrt.le) (by positivity)).1
  rw [mul_pow, sq_abs, Real.sq_sqrt hrad.le, mul_comm]
  exact hsq
