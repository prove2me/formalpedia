-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_vanish_above
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:54:38.661124+00:00
-- url     : https://prove2.me/submissions/de42b646-4f8c-48e7-82da-a4f187d9a2d4

import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_product_coeff_degree_bound
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_linear_factor_coeff_degree_bound

open scoped BigOperators

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (s : Finset ℕ) (a : ℕ → R) (n : σ →₀ ℕ)
    (h : s.card < n.sum (fun _ m => m)) :
    MvPowerSeries.coeff n
      (∏ i ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a i))) = 0 := by
  apply OAI.PiExponent.AdmissibleFormalInterpolation.product_coeff_degree_bound
  · intro i hi m hm
    exact OAI.PiExponent.AdmissibleFormalInterpolation.linear_factor_coeff_degree_bound
      x (a i) m hm
  · exact h
