-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_spatial_taylor_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:44:37.856996+00:00
-- url     : https://prove2.me/submissions/02d54936-5c8d-4582-992a-ff5b91b21256

import Mathlib
open Set
set_option autoImplicit false

/-- Second-order Taylor error controlled by the oscillation of the second derivative. -/
theorem solution (f : ℝ → ℝ) (hf : ContDiff ℝ 2 f) (x y c M : ℝ)
    (hM : 0 ≤ M) (hb : ∀ z ∈ uIcc x y, |iteratedDeriv 2 f z - c| ≤ M) :
    |f y - f x - deriv f x * (y-x) - c * (y-x)^2 / 2| ≤ M * (y-x)^2 / 2 := by
  by_cases hxy : x = y
  · subst y
    simp
  obtain ⟨z,hz,hz'⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
    (n := 1) hxy hf.contDiffOn
  have hd : derivWithin f (uIcc x y) x = deriv f x :=
    ((hf.differentiable (by norm_num) x).hasDerivAt.hasDerivWithinAt).derivWithin
      (uniqueDiffOn_uIcc hxy _ left_mem_uIcc)
  have hT : taylorWithinEval f 1 (uIcc x y) x y = f x + deriv f x * (y-x) := by
    rw [show (1 : ℕ) = 0+1 from rfl,taylorWithinEval_succ,taylor_within_zero_eval]
    simp [iteratedDerivWithin_one,hd,smul_eq_mul,mul_comm]
  rw [hT] at hz'
  norm_num at hz'
  have he : f y - f x - deriv f x * (y-x) - c * (y-x)^2 / 2 =
      (iteratedDeriv 2 f z - c) * ((y-x)^2 / 2) := by
    linarith only [hz',show (iteratedDeriv 2 f z - c)*((y-x)^2/2) =
      iteratedDeriv 2 f z * (y-x)^2/2 - c * (y-x)^2/2 by ring]
  rw [he,abs_mul,abs_of_nonneg (by positivity : 0 ≤ (y-x)^2/2)]
  simpa only [mul_div_assoc] using
    mul_le_mul_of_nonneg_right (hb z (uIoo_subset_uIcc_self hz)) (by positivity : 0 ≤ (y-x)^2/2)
