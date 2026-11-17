-- Prove2me | solution 1 for Kyprianou.Ch01.logarithmicJumpComplexExponent
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:55:33.19046+00:00
-- url     : https://prove2.me/submissions/c1b020a5-dcc8-41af-bdd5-cc8175e76777

import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Complex
set_option autoImplicit false

theorem solution (q z : ℂ) (hq : ‖q‖ < 1)
    (hqz : ‖q * z‖ < 1) :
    (∑' n : ℕ,
        ((q * z) ^ (n + 1) / ((n : ℂ) + 1) -
          q ^ (n + 1) / ((n : ℂ) + 1))) =
      Complex.log (1 - q) - Complex.log (1 - q * z) := by
  have hA := Complex.hasSum_taylorSeries_neg_log' hqz
  have hB := Complex.hasSum_taylorSeries_neg_log' hq
  have hdiff := hA.sub hB
  simpa only [neg_sub_neg, neg_sub] using hdiff.tsum_eq
