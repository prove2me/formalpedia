-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonIntegralIndependentIncrementsNNRealV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:57:31.097213+00:00
-- url     : https://prove2.me/submissions/4b1d0c5d-b7bf-41a6-a9e3-ec1ed8c897ea
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIndependentIncrementsV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

open Kyprianou.Ch02

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasIndependentIncrements
      (fun (t : ℝ≥0) ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by
  exact Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1 P ν N B hB hfinite
