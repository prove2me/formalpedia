-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionIntegralIncrementStripAEV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:21:12.540654+00:00
-- url     : https://prove2.me/submissions/97042833-aa36-411f-99a3-08efedb951c5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegrableAllTimesAEV1
import Theorems.Thm_Kyprianou_Ch02_markIntegralIncrementFromIntegrableV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), s ≤ t →
      ProbabilityTheory.increment (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) s t ω =
        ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω) := by
  have hint :=
    Kyprianou.Ch02.prmFiniteRegionMarkedIntegrableAllTimesAEV1
      P ν N B hB hfinite
  filter_upwards [hint] with ω hω s t hst
  change (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
    (∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), z.2 ∂(N.N ω)) =
      ∫ z in (Set.Ioc (s : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)
  exact Kyprianou.Ch02.markIntegralIncrementFromIntegrableV1
    (N.N ω) B hB s t hst (hω t)
