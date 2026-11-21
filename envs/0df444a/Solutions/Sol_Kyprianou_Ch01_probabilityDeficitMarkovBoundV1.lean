-- Prove2me | solution 1 for Kyprianou.Ch01.probabilityDeficitMarkovBoundV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:07:31.608813+00:00
-- url     : https://prove2.me/submissions/745d753e-3ad1-4ca1-8530-7f4750565ad0

import Mathlib
open MeasureTheory
open scoped ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (f : Ω → ℝ) (hf : Integrable f P)
    (hf_le : ∀ᵐ ω ∂P, f ω ≤ 1)
    (ε : ℝ) :
    ε * (P {ω | ε ≤ 1 - f ω}).toReal ≤
      1 - ∫ ω, f ω ∂P := by
  have hNonneg : 0 ≤ᵐ[P] (fun ω => 1 - f ω) := by
    filter_upwards [hf_le] with ω hle
    simpa using (sub_nonneg.mpr hle)
  have hInt : Integrable (fun ω => 1 - f ω) P :=
    (integrable_const (1 : ℝ)).sub hf
  have hMarkov :=
    MeasureTheory.mul_meas_ge_le_integral_of_nonneg
      (μ := P) (f := fun ω => 1 - f ω) hNonneg hInt ε
  have hMean : (∫ ω, 1 - f ω ∂P) =
      1 - ∫ ω, f ω ∂P := by
    rw [integral_sub (integrable_const (1 : ℝ)) hf]
    simp
  exact hMean ▸ hMarkov
