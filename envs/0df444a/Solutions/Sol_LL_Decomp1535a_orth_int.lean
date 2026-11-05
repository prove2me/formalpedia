-- Prove2me | solution 1 for LL_Decomp1535a.orth_int
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-04T10:04:56.58145+00:00
-- url     : https://prove2.me/submissions/6b5f7b2c-362c-4c6f-b505-8d98b2e0c512

import Mathlib

open MeasureTheory

theorem GbAAux.orth_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have hc : (2 * Real.pi * Complex.I * k : ℂ) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hk']
    have e : ∀ α : ℝ, Complex.exp (2 * Real.pi * Complex.I * α * k) =
        Complex.exp ((2 * Real.pi * Complex.I * k) * α) := fun α => by ring_nf
    simp_rw [e]
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((2 * Real.pi * Complex.I * k) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * Real.pi * Complex.I * k) * ((1 : ℝ) : ℂ) = (k : ℂ) * (2 * Real.pi * Complex.I)
        by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [h1]
    simp

theorem solution (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 :=
  GbAAux.orth_int k
