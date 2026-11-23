-- Prove2me | solution 3 for Kyprianou.Ch02.finiteRegionPoissonIntegralCadlagAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:52:48.981433+00:00
-- url     : https://prove2.me/submissions/14897e04-6f7c-4d35-9e3e-36d2f86c9045

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
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
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by
  exact Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N B hB hfinite
