-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionMarkedIntegralSquareIntegrableV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T14:11:53.284991+00:00
-- url     : https://prove2.me/submissions/a6a7b788-21ab-4d82-ac25-99f86a40a86f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableAmbientV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteWeightedCountSumL2V1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteMarkedIntegralSimpleApproxL2BoundV1
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
    ∀ t : ℝ≥0, Integrable
      (fun ω => (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) ^ 2) P := by
  intro t
  have hR : MeasurableSet (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hMeas : Measurable (fun ω =>
      ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) :=
    Kyprianou.Ch02.prmMarkedIntegralMeasurableAmbientV1 P ν N _ hR
  obtain ⟨F, C, a, hC, hCf, _, hconv, hbound⟩ :=
    Kyprianou.Ch02.prmFiniteMarkedIntegralSimpleApproxL2BoundV1
      P ν N B hB hfinite hsecond t
  have hSimple : ∀ n, MemLp
      (fun ω => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) 2 P := by
    intro n
    exact Kyprianou.Ch02.prmFiniteWeightedCountSumL2V1
      P ν N (F n) (C n) (hC n) (hCf n) (a n)
  have hFatou : eLpNorm
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
      2 P ≤
      Filter.liminf
        (fun n => eLpNorm
          (fun ω => ∑ i ∈ F n, a n i * (N.N ω (C n i)).toReal) 2 P)
        Filter.atTop :=
    MeasureTheory.Lp.eLpNorm_lim_le_liminf_eLpNorm
      (fun n => (hSimple n).1) _ hconv
  have hLp : MemLp
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω))
      2 P := ⟨hMeas.aestronglyMeasurable, lt_of_le_of_lt hFatou hbound⟩
  exact (memLp_two_iff_integrable_sq hMeas.aestronglyMeasurable).1 hLp
