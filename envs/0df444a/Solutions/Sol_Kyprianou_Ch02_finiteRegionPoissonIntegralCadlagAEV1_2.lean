-- Prove2me | solution 2 for Kyprianou.Ch02.finiteRegionPoissonIntegralCadlagAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T10:39:03.323879+00:00
-- url     : https://prove2.me/submissions/9934f4ce-4a13-4279-81c9-52cc45426a90
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPRMFiniteSupportAllNaturalWindowsV2
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
    (Kyprianou.Ch02.finiteRegionPRMFiniteSupportAllNaturalWindowsV2
      P ν N B hB hfinite)
