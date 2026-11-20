-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftRealMellinAnchor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T11:32:32.952185+00:00
-- url     : https://prove2.me/submissions/8364f7e8-3d4f-414b-b24b-6af078029ace

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Real Set
set_option autoImplicit false

/-- Exact real-axis Mellin-Gamma anchor for the strict-left complex identity. -/
theorem solution
    (alpha u : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (hu : 0 < u) :
    (∫ r in Set.Ioi (0 : ℝ),
      Real.exp (-(u * r)) * r ^ (-alpha) ∂volume) =
      (1 / u) ^ (1 - alpha) * Real.Gamma (1 - alpha) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi
    (a := 1 - alpha) (r := u) (by linarith) hu
  calc
    _ = (∫ r in Set.Ioi (0 : ℝ),
      r ^ (1 - alpha - 1) * Real.exp (-(u * r)) ∂volume) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro r hr
        rw [show 1 - alpha - 1 = -alpha by ring]
        ring
    _ = _ := h
