-- Prove2me | solution 2 for Kyprianou.Ch02.finiteRegionPoissonCadlagFromFiniteSupportV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:49:13.42682+00:00
-- url     : https://prove2.me/submissions/f30d579a-61b4-4faf-a780-6ba91c0afb6f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_finiteRegionPoissonIntegralLocalFiniteStepV1
import Theorems.Thm_Kyprianou_Ch02_finiteRegionCadlagOfLocalStepNNRealV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hSupport : ∀ᵐ ω ∂P, ∀ T : ℕ, ∃ s : Finset (ℝ × ℝ),
      N.N ω ((Set.Ioc (0 : ℝ) (T : ℝ) ×ˢ B) \ (s : Set (ℝ × ℝ))) = 0) :
    ∀ᵐ ω ∂P, ProbabilityTheory.IsCadlag
      (fun t : ℝ≥0 => ∫ z in
        (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) := by
  filter_upwards
    [Kyprianou.Ch02.finiteRegionPoissonIntegralLocalFiniteStepV1
      P ν N B hB hfinite hSupport] with ω hω
  exact Kyprianou.Ch02.finiteRegionCadlagOfLocalStepNNRealV1
    (fun t : ℝ≥0 =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
    (hω)
