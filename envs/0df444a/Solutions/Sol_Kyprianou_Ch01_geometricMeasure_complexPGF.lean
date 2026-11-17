-- Prove2me | solution 1 for Kyprianou.Ch01.geometricMeasure_complexPGF
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T22:40:45.810439+00:00
-- url     : https://prove2.me/submissions/97a5ce9d-eca4-4994-b931-aa89b052fb00

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_geometricComplexGeneratingSeries
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Complex
set_option autoImplicit false

theorem solution
    (p : unitInterval.Elem) (hp : p ≠ 0)
    (z : ℂ)
    (hbound : ‖(1 - ((p : ℝ) : ℂ)) * z‖ < 1) :
    (∫ n : ℕ, z ^ n ∂ProbabilityTheory.geometricMeasure p) =
      ((p : ℝ) : ℂ) / (1 - (1 - ((p : ℝ) : ℂ)) * z) := by
  rw [ProbabilityTheory.integral_geometricMeasure hp]
  rw [← Kyprianou.Ch01.geometricComplexGeneratingSeries
    ((p : ℝ) : ℂ) z hbound]
  congr 1
  funext n
  rw [Complex.real_smul]
  push_cast
  ring
