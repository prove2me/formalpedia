-- Prove2me | solution 1 for OAI.PiExponent.AdmissibleFormalInterpolation.linear_factor_coeff_degree_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-16T18:59:22.518853+00:00
-- url     : https://prove2.me/submissions/4b9f7971-393d-4f17-a18a-ea475d050cbd

import Mathlib.RingTheory.MvPowerSeries.Basic

theorem solution
    {σ R : Type*} [DecidableEq σ] [CommSemiring R]
    (x : σ) (a : R) (m : σ →₀ ℕ)
    (hm : MvPowerSeries.coeff m
      (MvPowerSeries.X x + MvPowerSeries.C a) ≠ 0) :
    m.sum (fun _ k => k) ≤ 1 := by
  classical
  by_cases hzero : m = 0
  · simp [hzero]
  · have hsingle : m = Finsupp.single x 1 := by
      have hcoeff : (if m = Finsupp.single x 1 then (1 : R) else 0) ≠ 0 := by
        simpa [MvPowerSeries.coeff_X, MvPowerSeries.coeff_C, hzero] using hm
      by_contra hne
      simp [hne] at hcoeff
    simp [hsingle]