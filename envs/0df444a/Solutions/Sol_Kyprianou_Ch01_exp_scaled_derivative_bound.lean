-- Prove2me | solution 1 for Kyprianou.Ch01.exp_scaled_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T18:18:09.017321+00:00
-- url     : https://prove2.me/submissions/82b63611-c711-4188-89e9-4d36a1907242

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
set_option autoImplicit false

/-- A scaled exponential derivative is uniformly bounded for positive Laplace arguments. -/
theorem solution
    (delta : ℝ) (hd : 0 < delta) (k : ℕ) (z : ℝ) (hz : delta ≤ z) :
    (k : ℝ) * Real.exp (-z * (k : ℝ)) ≤ delta⁻¹ := by
  have hk : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
  have hexp : Real.exp (-z * (k : ℝ)) ≤
      Real.exp (-(delta * (k : ℝ))) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have h0 := Real.mul_exp_neg_le_exp_neg_one (delta * (k : ℝ))
  have h1 : Real.exp (-(1 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by norm_num)
  have h2 : (k : ℝ) * Real.exp (-z * (k : ℝ)) ≤
      (k : ℝ) * Real.exp (-(delta * (k : ℝ))) :=
    mul_le_mul_of_nonneg_left hexp hk
  have h3 : delta * ((k : ℝ) * Real.exp (-z * (k : ℝ))) ≤ 1 := by
    nlinarith [h0, h1, h2]
  rw [inv_eq_one_div]
  exact (le_div_iff₀ hd).2 (by nlinarith)
