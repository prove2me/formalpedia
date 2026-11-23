-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonIntegralStationaryIncrementsNNRealV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:57:40.763527+00:00
-- url     : https://prove2.me/submissions/099a098e-3b2e-4207-966e-a7b2c5c69dc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryIncrementsV1
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
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by
  exact Kyprianou.Ch02.prmFiniteRegionStationaryIncrementsV1 P ν N B hB hfinite
