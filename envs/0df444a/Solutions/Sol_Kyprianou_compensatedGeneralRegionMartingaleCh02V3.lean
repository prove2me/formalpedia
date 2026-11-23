-- Prove2me | solution 1 for Kyprianou.compensatedGeneralRegionMartingaleCh02V3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:05:32.331231+00:00
-- url     : https://prove2.me/submissions/b1108e6c-c2b5-4b81-93ff-7ff7e7c25998

import Mathlib
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch02_completedPoissonFiltrationExistsGeneralV1
import Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
import Theorems.Thm_Kyprianou_Ch02_compensatedFiniteRegionL2GivenSecondMomentV1
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤)
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B)) :
    ∃ (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω)),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
      MeasureTheory.Martingale
        (fun (t : ℝ≥0) ω =>
          (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
             z.2 ∂(N.N ω)) -
          (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P ∧
      (MemLp (fun x : ℝ => x) 2 (ν.restrict B) →
       ∀ t : ℝ≥0, MemLp
         (fun ω =>
           (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
              z.2 ∂(N.N ω)) -
           (t : ℝ) * (∫ x in B, x ∂ν)) 2 P) := by
  obtain ⟨ℱ, hℱ⟩ :=
    Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1 P ν N
  refine ⟨ℱ, hℱ, ?_, ?_⟩
  · exact Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
      P ν N B hB hfinite hfirst ℱ hℱ
  · intro hsecond
    exact Kyprianou.Ch02.compensatedFiniteRegionL2GivenSecondMomentV1
      P ν N B hB hfinite hsecond
