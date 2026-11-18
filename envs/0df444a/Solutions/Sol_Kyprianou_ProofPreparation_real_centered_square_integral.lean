-- Prove2me | solution 1 for Kyprianou.ProofPreparation.real_centered_square_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T13:15:55.347079+00:00
-- url     : https://prove2.me/submissions/152473c5-dae4-4461-be6b-aaf4bb084f79

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
set_option autoImplicit false

/-- The integral of (J-c)² expands into the first and second moments. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (J : Ω → ℝ) (c : ℝ)
    (hJ : Integrable J P)
    (hJ2 : Integrable (fun ω => J ω ^ 2) P) :
    (∫ ω, (J ω - c) ^ 2 ∂P) =
      (∫ ω, J ω ^ 2 ∂P) -
        (2 * c) * (∫ ω, J ω ∂P) + c ^ 2 := by
  have hlinear : Integrable (fun ω => (2 * c) * J ω) P :=
    hJ.const_mul _
  calc
    (∫ ω, (J ω - c) ^ 2 ∂P) =
        (∫ ω, (J ω ^ 2 - (2 * c) * J ω) + c ^ 2 ∂P) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by ring
    _ = (∫ ω, J ω ^ 2 ∂P) -
          (2 * c) * (∫ ω, J ω ∂P) + c ^ 2 := by
      calc
        (∫ ω, (J ω ^ 2 - (2 * c) * J ω) + c ^ 2 ∂P) =
            (∫ ω, J ω ^ 2 - (2 * c) * J ω ∂P) +
              (∫ ω, (c ^ 2 : ℝ) ∂P) :=
          integral_add (hJ2.sub hlinear) (integrable_const _)
        _ = ((∫ ω, J ω ^ 2 ∂P) -
            (∫ ω, (2 * c) * J ω ∂P)) +
              (∫ ω, (c ^ 2 : ℝ) ∂P) := by
          rw [integral_sub hJ2 hlinear]
        _ = _ := by
          simp only [integral_const_mul]
          simp
