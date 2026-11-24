-- Prove2me | solution 1 for Kyprianou.Ch02.prmIntegrableMarkCompensatedMartingaleV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:35:06.238549+00:00
-- url     : https://prove2.me/submissions/43a6b054-f6a8-41a8-a89a-a320faaad95b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch02_CompletedPoissonFiltration
import Theorems.Thm_Kyprianou_Ch02_completedPoissonFiltrationExistsGeneralV1
import Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedAdaptedV1
import Theorems.Thm_Kyprianou_Ch02_prmIntegrableMarkCompensatedSetIntegralV1
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (f : ℝ → ℝ) (hf : Measurable f) (hi : Integrable f ν) :
    ∃ ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω),
      Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ ∧
      MeasureTheory.Martingale
        (fun (t : ℝ≥0) ω =>
          (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ Set.univ),
              f z.2 ∂(N.N ω)) -
          (t : ℝ) * ∫ x, f x ∂ν) ℱ P := by
  obtain ⟨ℱ, hℱ⟩ := Kyprianou.Ch02.completedPoissonFiltrationExistsGeneralV1 P ν N
  have hAI := Kyprianou.Ch02.prmIntegrableMarkCompensatedAdaptedV1 P ν N f hf hi ℱ hℱ
  refine ⟨ℱ, hℱ, ⟨hAI.1, ?_⟩⟩
  intro s t hst
  exact (ae_eq_condExp_of_forall_setIntegral_eq (ℱ.le s) (hAI.2 t)
    (fun E _ _ => (hAI.2 s).integrableOn)
    (fun E hE _ => Kyprianou.Ch02.prmIntegrableMarkCompensatedSetIntegralV1
      P ν N f hf hi ℱ hℱ s t hst E hE)
    (hAI.1 s).aestronglyMeasurable).symm
