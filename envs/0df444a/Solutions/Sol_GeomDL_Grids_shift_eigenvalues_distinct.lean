-- Prove2me | solution 1 for GeomDL.Grids.shift_eigenvalues_distinct
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T19:49:24.288257+00:00
-- url     : https://prove2.me/submissions/ee094488-1b2a-468f-b0c7-80c9504c1f39

import Mathlib
open Complex

theorem eq_of_exp_aux {n : ℕ} (hn : 0 < n) {a b : ℕ} (ha : a < n) (hb : b < n)
    (h : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (a : ℂ) / (n : ℂ)) =
      Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (b : ℂ) / (n : ℂ))) : a = b := by
  obtain ⟨m, hm⟩ := Complex.exp_eq_exp_iff_exists_int.mp h
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  field_simp at hm
  have k2 : ((a : ℤ) : ℂ) = ((b + m * n : ℤ) : ℂ) := by
    push_cast
    linear_combination hm
  have k3 : (a : ℤ) = b + m * n := by exact_mod_cast k2
  have : m = 0 := by
    rcases lt_trichotomy m 0 with h1 | h1 | h1
    · have : m * (n:ℤ) ≤ -n := by nlinarith
      omega
    · exact h1
    · have : (n:ℤ) ≤ m * n := by nlinarith
      omega
  subst this
  omega

theorem solution {n : ℕ} [NeZero n] (k l : ZMod n)
    (hkl : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (k.val : ℂ) / (n : ℂ))) =
      Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (l.val : ℂ) / (n : ℂ)))) :
    k = l := by
  rw [Complex.exp_neg, Complex.exp_neg, _root_.inv_inj] at hkl
  exact ZMod.val_injective n
    (eq_of_exp_aux (Nat.pos_of_ne_zero (NeZero.ne n)) (ZMod.val_lt k) (ZMod.val_lt l) hkl)
