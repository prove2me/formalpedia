-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_top_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:50:39.174499+00:00
-- url     : https://prove2.me/submissions/adc9194f-f1cd-4b81-a2d8-1830cfb0521b

import Mathlib.RingTheory.MvPowerSeries.Basic
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_vanish_above
import Theorems.Thm_OAI_PiExponent_AdmissibleFormalInterpolation_coeff_product_constant_shift_step

open scoped BigOperators

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (s : Finset ℕ) (a : ℕ → R) :
    MvPowerSeries.coeff (Finsupp.single x s.card)
        (∏ i ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a i))) = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have hs : ∀ n : σ →₀ ℕ, s.card < n.sum (fun _ m => m) →
          MvPowerSeries.coeff n
            (∏ j ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a j))) = 0 := by
        intro n hn
        exact OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_vanish_above
          x s a n hn
      rw [Finset.card_insert_of_notMem hi]
      simpa [mul_comm] using
        OAI.PiExponent.AdmissibleFormalInterpolation.coeff_product_constant_shift_step
          (x := x) (k := s.card)
          (φ := ∏ j ∈ s, (MvPowerSeries.X x + MvPowerSeries.C (a j)))
          (a i) hs ih
