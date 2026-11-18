-- Prove2me | solution 1 for Kyprianou.Ch06.competingPoissonRateExponentialTailIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:41:42.32732+00:00
-- url     : https://prove2.me/submissions/7656f555-bac8-48c3-a8d9-1fca5de76cd3

import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

theorem solution
    (a b t : Real) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ s in Set.Ioi t, a * Real.exp (-(a + b) * s)) =
      (a / (a + b)) * Real.exp (-(a + b) * t) := by
  have hab : 0 < a + b := add_pos_of_pos_of_nonneg ha hb
  have hc : -(a + b) < 0 := neg_lt_zero.mpr hab
  have hIntegral :
      (∫ s in Set.Ioi t, Real.exp (-(a + b) * s)) =
        Real.exp (-(a + b) * t) / (a + b) := by
    simpa only [neg_div_neg_eq] using
      (integral_exp_mul_Ioi (a := -(a + b)) hc t)
  calc
    (∫ s in Set.Ioi t, a * Real.exp (-(a + b) * s)) =
        a * (∫ s in Set.Ioi t, Real.exp (-(a + b) * s)) := by
      simp only [integral_const_mul, smul_eq_mul]
    _ = a * (Real.exp (-(a + b) * t) / (a + b)) := by
      rw [hIntegral]
    _ = (a / (a + b)) * Real.exp (-(a + b) * t) := by
      ring
