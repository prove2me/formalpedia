-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaPositiveKernelIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:35:55.495237+00:00
-- url     : https://prove2.me/submissions/7a777372-3567-48e5-981c-9530db6eb0ea

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Real Set
set_option autoImplicit false

/-- Absolute integrability of the positive, scaled Euler Gamma kernel. -/
theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      Real.exp (-(u * x)) * x ^ (-alpha))
      (Set.Ioi (0 : ℝ)) := by
  have ha : 0 < 1 - alpha := by linarith
  have heval := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 - alpha) (r := u) ha hu
  have hint : IntegrableOn (fun x : ℝ =>
      x ^ ((1 - alpha) - 1) * Real.exp (-(u * x)))
      (Set.Ioi (0 : ℝ)) :=
    .of_integral_ne_zero (by rw [heval]; positivity)
  have heq : (1 - alpha) - 1 = -alpha := by ring
  simpa only [heq, mul_comm] using hint
