-- Prove2me | solution 1 for Kyprianou.Ch04.klsSimpleMarkMeanV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T21:40:41.832607+00:00
-- url     : https://prove2.me/submissions/d2946ccf-2c46-4102-a6ea-546e83542b96

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_klsSimpleMarkRawFibreMeanV1
import Theorems.Thm_Kyprianou_Ch04_simpleMarkIntensityFibresV1
open MeasureTheory ProbabilityTheory Filter Set LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : PoissonRandomMeasure.{0,0,0} P ν) (B : Set ℝ)
    (hB : MeasurableSet B) (hfinite : ν B < ⊤) (g : SimpleFunc ℝ ℝ) (t : ℝ≥0) :
    (∫ ω, (∫ z in Ioc (0 : ℝ) (t : ℝ) ×ˢ B, g z.2 ∂(N.N ω)) ∂P) =
      (t : ℝ) * ∫ x in B, g x ∂ν := by
  rw [Kyprianou.Ch04.klsSimpleMarkRawFibreMeanV1 P ν N B hB hfinite g t,
    Kyprianou.Ch04.simpleMarkIntensityFibresV1 ν B hB hfinite g, Finset.mul_sum]
  exact Finset.sum_congr rfl fun r _ => by ring
