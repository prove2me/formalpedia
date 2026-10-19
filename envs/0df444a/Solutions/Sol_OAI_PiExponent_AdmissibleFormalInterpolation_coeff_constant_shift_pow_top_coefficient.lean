-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_constant_shift_pow_top_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:36:32.261386+00:00
-- url     : https://prove2.me/submissions/f907e46c-d5b2-46e6-b304-3715ffef1e30

import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_top_coefficient

open scoped BigOperators

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single x n)
        ((MvPowerSeries.X x + MvPowerSeries.C a) ^ n) = 1 := by
  simpa only [Finset.prod_const, Finset.card_range] using
    OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_coefficient
      x (Finset.range n) (fun _ => a)