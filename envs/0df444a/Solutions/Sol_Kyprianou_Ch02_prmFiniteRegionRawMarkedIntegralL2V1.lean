-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionRawMarkedIntegralL2V1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:48:16.834413+00:00
-- url     : https://prove2.me/submissions/390d6553-e717-495d-bfda-b73d32043f66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionMarkedIntegralSquareIntegrableV1
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hsecond : MemLp (fun x : ℝ => x) 2 (ν.restrict B)) :
    ∀ t : ℝ≥0, MemLp
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) 2 P := by
  intro t
  have hR : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hm : Measurable (fun ω =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) :=
    Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1
      P ν N (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) hR
  have hs : Integrable (fun ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) ^ 2) P :=
    Kyprianou.Ch02.prmFiniteRegionMarkedIntegralSquareIntegrableV1
      P ν N B hB hfinite hsecond t
  exact (memLp_two_iff_integrable_sq hm.aestronglyMeasurable).2 hs
