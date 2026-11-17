-- Prove2me | solution 1 for Kyprianou.Ch01.realLogSeriesMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:27.258308+00:00
-- url     : https://prove2.me/submissions/6d32c74e-fb3d-41ce-a48c-5087785a5440

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    HasSum (fun n : ℕ => q ^ (n + 1) / ((n : ℝ) + 1))
      (-Real.log (1 - q)) := by
  have hqnorm : ‖(q : ℂ)‖ < 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0] using hq1
  have hc := Complex.hasSum_taylorSeries_neg_log' hqnorm
  have hqle : 0 ≤ 1 - q := sub_nonneg.mpr (le_of_lt hq1)
  have hlog : ((-Real.log (1 - q) : ℝ) : ℂ) =
      -Complex.log (1 - (q : ℂ)) := by
    rw [Complex.ofReal_neg, Complex.ofReal_log hqle]
    push_cast
    rfl
  have hcoe : (fun n : ℕ => ((q ^ (n + 1) / ((n : ℝ) + 1) : ℝ) : ℂ)) =
      (fun n : ℕ => (q : ℂ) ^ (n + 1) / ((n : ℂ) + 1)) := by
    funext n
    push_cast
    ring
  apply Complex.hasSum_ofReal.mp
  simpa only [hcoe, hlog] using hc
