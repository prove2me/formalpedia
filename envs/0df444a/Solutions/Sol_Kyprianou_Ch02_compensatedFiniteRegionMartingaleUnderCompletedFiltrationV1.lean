-- Prove2me | solution 1 for Kyprianou.Ch02.compensatedFiniteRegionMartingaleUnderCompletedFiltrationV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:05:47.326278+00:00
-- url     : https://prove2.me/submissions/39ce1458-8f12-47de-9acf-bbd00bc1af74
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedStronglyAdaptedIntegrableV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteCompensatedConditionalExpectationV1
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
    (hfirst : Integrable (fun x : ℝ => x) (ν.restrict B))
    (ℱ : Filtration ℝ≥0 (inferInstance : MeasurableSpace Ω))
    (hℱ : Kyprianou.Ch02.IsCompletedPoissonFiltration P ν N ℱ) :
    MeasureTheory.Martingale
      (fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) ℱ P := by
  have hAI := Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedIntegrableV1
    P ν N B hB hfinite hfirst ℱ hℱ
  refine ⟨hAI.1, ?_⟩
  intro s t hst
  exact Kyprianou.Ch02.prmFiniteCompensatedConditionalExpectationV1
    P ν N B hB hfinite hfirst ℱ hℱ s t hst
