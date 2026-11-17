-- Prove2me | solution 1 for N25.fifth_root_exp_ne_rat
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:34:09.911803+00:00
-- url     : https://prove2.me/submissions/aa7be8c8-84ac-47ea-817b-02993e294bf1

import Mathlib

set_option autoImplicit false

namespace N25

/-- A nontrivial fifth-root exponential cannot be rational. -/
theorem _root_.solution (v : ℤ) (hv : ¬ (5 : ℤ) ∣ v) (c : ℚ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5))) ≠ (c : ℂ) := by
  intro h
  have hz5 : Complex.exp (-(2 * Real.pi * Complex.I * ((v : ℂ) / 5))) ^ 5 = 1 := by
    rw [← Complex.exp_nat_mul]
    apply Complex.exp_eq_one_iff.mpr
    refine ⟨-v,?_⟩
    push_cast
    ring
  have hc5 : c ^ 5 = 1 := by
    have hC : (c : ℂ) ^ 5 = 1 := by rw [← h]; exact hz5
    exact_mod_cast hC
  have hc : c = 1 := (Odd.pow_injective (by decide : Odd 5)) (by simpa using hc5)
  rw [hc,Rat.cast_one] at h
  obtain ⟨n,hn⟩ := Complex.exp_eq_one_iff.mp h
  have hvn : (v : ℂ) / 5 = -(n : ℂ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    linear_combination -hn
  have hvC : (v : ℂ) = ((-5*n : ℤ) : ℂ) := by
    push_cast
    linear_combination 5 * hvn
  have hvZ : v = -5*n := by exact_mod_cast hvC
  apply hv
  exact ⟨-n,by omega⟩

end N25
