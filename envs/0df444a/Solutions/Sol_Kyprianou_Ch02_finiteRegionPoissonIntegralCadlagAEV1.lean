-- Prove2me | solution 1 for Kyprianou.Ch02.finiteRegionPoissonIntegralCadlagAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:25:56.406802+00:00
-- url     : https://prove2.me/submissions/638199d3-8884-4eba-aeb5-90cd8d0b4a42
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMFiniteSupportAllNaturalWindowsV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonCadlagFromFiniteSupportV2

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))  := by
  exact Kyprianou.Ch02.finiteRegionPoissonCadlagFromFiniteSupportV2
    P ν N B hB hfinite
    (Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV1
      P ν N B hB hfinite)
