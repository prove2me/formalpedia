-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaAboveOneReducedFourierIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T09:13:33.516446+00:00
-- url     : https://prove2.me/submissions/3da001a3-8aa9-4372-8c72-c6604cc85638

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set
set_option autoImplicit false

/-- Integrability of the reduced stable Fourier kernel from the α<1 theorem. -/
theorem solution
    (alpha : ℝ) (ha1 : 1 < alpha) (ha2 : alpha < 2) :
    IntegrableOn (fun r : ℝ =>
      (Complex.exp (Complex.I * (r : ℂ)) - 1) *
        (((r ^ (-alpha) : ℝ)) : ℂ))
      (Set.Ioi (0 : ℝ)) := by
  have hβ0 : 0 < alpha - 1 := by linarith
  have hβ1 : alpha - 1 < 1 := by linarith
  have h := Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
    (alpha - 1) hβ0 hβ1 Complex.I (by simp) (by simp)
  simpa only [show -(alpha - 1) - 1 = -alpha by ring] using h
