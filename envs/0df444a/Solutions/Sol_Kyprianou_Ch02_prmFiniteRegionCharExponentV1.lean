-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionCharExponentV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:54:06.232274+00:00
-- url     : https://prove2.me/submissions/5f23c80b-9a93-4807-ab4c-249587791c3f

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionMarkedCharFromCountCharV2
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCountCharacteristicV1

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
      charFun (P.map (fun ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  have hCount : ∀ (t : ℝ≥0) (u : ℝ),
      ∫ ω, Complex.exp (Complex.I *
      ((u * (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal : ℝ) : ℂ)) ∂P =
    Complex.exp ((LevyStochCalc.Poisson.referenceIntensity ν
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B)).toReal *
      (Complex.exp (Complex.I * (u : ℂ)) - 1)) := by
    intro t u
    exact Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1
      P ν N B hB hfinite t u
  exact Kyprianou.Ch02.finiteRegionMarkedCharFromCountCharV2
    P ν N B hB hfinite hCount
