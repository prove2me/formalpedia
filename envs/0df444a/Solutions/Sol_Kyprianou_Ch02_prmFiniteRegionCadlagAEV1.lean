-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionCadlagAEV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:21:05.472673+00:00
-- url     : https://prove2.me/submissions/f3f14955-be22-4a33-be71-22239a39cda1

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmUnitStripsFiniteMassAEV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionCadlagWithFiniteStripsV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, IsCadlag (fun (t : ℝ≥0) =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by
  exact Kyprianou.Ch02.prmFiniteRegionCadlagWithFiniteStripsV1
    P ν N B hB hfinite
    (Kyprianou.Ch02.prmUnitStripsFiniteMassAEV1 P ν N B hB hfinite)
