-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneSineKernelIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T12:13:51.178037+00:00
-- url     : https://prove2.me/submissions/29a46daf-6eb5-42d8-ac8e-845e31ad8b3f

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseIntegrableExact
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseImagKernel
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real Complex
set_option autoImplicit false
/-! Imaginary projection of source integrability gives the sine-kernel L1 estimate. -/
theorem solution
    (z : ℝ) (hz : 0 < z) :
    IntegrableOn (fun r : ℝ =>
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2)
      (Set.Ioi (0 : ℝ)) := by
  have h := (Kyprianou.Ch01.stableAlphaOneLogPhaseIntegrableExact z hz).im
  have hEq :
      (fun r : ℝ =>
        ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2) =
      (fun r : ℝ =>
        (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).im) := by
    funext r
    exact (Kyprianou.Ch01.stableAlphaOneLogPhaseImagKernel z r).symm
  change Integrable
    (fun r : ℝ =>
      ((z * r) * (if r < 1 then (1 : ℝ) else 0) - Real.sin (z * r)) / r ^ 2)
    (volume.restrict (Set.Ioi (0 : ℝ)))
  rw [hEq]
  exact h
