-- Prove2me | solution 1 for Kyprianou.finiteRegionPoissonIntegralCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:58:13.217794+00:00
-- url     : https://prove2.me/submissions/b89898b9-2698-4456-8adb-c0e2e37bf184

import Mathlib
import Definitions.Def_LeanLevy_RandomMeasure_PoissonPointFamily
import Definitions.Def_LeanLevy_RandomMeasure_PoissonRandomMeasure
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStartZeroV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIndependentIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryIncrementsV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagAEV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCharExponentV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false
open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P ∧
    ∀ (t : ℝ≥0) (ξ : ℝ),
      charFun (P.map
        (fun ω => ∫ z in
          (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))) ξ =
      Complex.exp ((((t : ℝ) : ℂ)) *
        ∫ x in B,
          (Complex.exp (Complex.I * (((ξ * x : ℝ) : ℂ))) - 1) ∂ν) := by
  constructor
  · exact ⟨
      Kyprianou.Ch02.prmFiniteRegionStartZeroV1 P ν N B,
      Kyprianou.Ch02.prmFiniteRegionIndependentIncrementsV1 P ν N B hB hfinite,
      Kyprianou.Ch02.prmFiniteRegionStationaryIncrementsV1 P ν N B hB hfinite,
      Kyprianou.Ch02.prmFiniteRegionCadlagAEV1 P ν N B hB hfinite⟩
  · exact Kyprianou.Ch02.prmFiniteRegionCharExponentV1 P ν N B hB hfinite
