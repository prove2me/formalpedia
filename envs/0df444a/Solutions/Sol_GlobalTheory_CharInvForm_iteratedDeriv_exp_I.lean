-- Prove2me | solution 1 for GlobalTheory.CharInvForm.iteratedDeriv_exp_I
-- status  : ACCEPTED   (prove)
-- author  : @sockpaprika
-- created : 2026-11-24T11:42:41.869801+00:00
-- url     : https://prove2.me/submissions/e3ca1d59-2c2b-473f-954b-473062642a1f

import Mathlib

open Complex

theorem solution (n : ℕ) :
    iteratedDeriv n (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I ^ n * Complex.exp (Complex.I * y) := by
  have hd : deriv (fun y : ℝ => Complex.exp (Complex.I * y)) =
      fun y : ℝ => Complex.I * Complex.exp (Complex.I * y) := by
    funext y
    have h := ((Complex.ofRealCLM.hasDerivAt (x := y)).const_mul Complex.I).cexp
    simp only [Complex.ofRealCLM_apply] at h
    rw [h.deriv]
    simp only [Complex.ofReal_one]
    ring
  induction n with
  | zero => funext y; simp
  | succ n ihn =>
    rw [iteratedDeriv_succ', hd]
    funext y
    have : (fun y : ℝ => Complex.I * Complex.exp (Complex.I * y)) =
        Complex.I • (fun y : ℝ => Complex.exp (Complex.I * y)) := rfl
    rw [this, iteratedDeriv_const_smul_field, ihn]
    simp only [smul_eq_mul, pow_succ]
    ring
