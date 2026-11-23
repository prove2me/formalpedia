-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonIntegralCharFunV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:34:00.28103+00:00
-- url     : https://prove2.me/submissions/04103d07-57b3-4c1e-b979-c5f1124e3c58

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCountCharacteristicV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionMarkedCharFromCountCharV2
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν)  := by
  exact Kyprianou.Ch02.finiteRegionMarkedCharFromCountCharV2
    P ν N B hB hfinite
    (fun t u =>
      Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1
        P ν N B hB hfinite t u)
