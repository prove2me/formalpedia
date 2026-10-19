-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support_top
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:31:17.949732+00:00
-- url     : https://prove2.me/submissions/f6463cfb-63f8-4258-b764-8db3f27a9a37

import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_top_coefficient
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_constant_shift_pow_support

open scoped BigOperators

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single x n)
        ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) = 1 ∧
      ∀ k : σ →₀ ℕ,
        MvPowerSeries.coeff k ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) ≠ 0 →
          k ≤ Finsupp.single x n := by
  exact ⟨OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_top_coefficient x a n,
    OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_support x a n⟩