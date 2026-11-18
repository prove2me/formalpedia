-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneLogPhaseRealIntegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T10:31:35.682916+00:00
-- url     : https://prove2.me/submissions/a0ef5929-db3e-4940-ba20-8a697cdf7c14

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneLogPhaseRealKernel
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineScaling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Set Real
set_option autoImplicit false
/-! Extract the exact real part of the original compensated alpha-one Lévy integral. -/
theorem solution
    (z : ℝ) (hz : 0 < z)
    (hInt : IntegrableOn
      (fun r : ℝ =>
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)) (Set.Ioi (0 : ℝ))) :
    (∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).re =
      Real.pi * z / 2 := by
  have hReal := (integral_re
    (μ := volume.restrict (Set.Ioi (0 : ℝ))) hInt)
  calc
    (∫ r in Set.Ioi (0 : ℝ),
      ((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
        Complex.I * (((z * r : ℝ) : ℂ)) *
          (if r < 1 then (1 : ℂ) else 0)) /
        ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) ∂volume).re =
      ∫ r in Set.Ioi (0 : ℝ),
        (((1 : ℂ) - Complex.exp (Complex.I * (((z * r : ℝ) : ℂ))) +
          Complex.I * (((z * r : ℝ) : ℂ)) *
            (if r < 1 then (1 : ℂ) else 0)) /
          ((((r : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ)).re ∂volume :=
        hReal.symm
    _ = ∫ r in Set.Ioi (0 : ℝ),
          (1 - Real.cos (z * r)) / r ^ 2 ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with r
        exact Kyprianou.Ch01.stableAlphaOneLogPhaseRealKernel z r
    _ = Real.pi * z / 2 :=
      Kyprianou.Ch01.stableAlphaOneCosineScaling z hz
