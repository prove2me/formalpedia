-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteCompensatedStronglyAdaptedV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T19:43:02.345797+00:00
-- url     : https://prove2.me/submissions/7fa0262a-f755-4e3f-8120-b1719e98d08d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
import Theorems.Thm_Kyprianou_Ch02_prmPastLocalEvalSigmaLeCompletedFiltrationV1
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
    ∀ t : ℝ≥0, StronglyMeasurable[ℱ t] ((fun (t : ℝ≥0) ω =>
      (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) -
      (t : ℝ) * (∫ x in B, x ∂ν)) t) := by
  intro t
  have hR : MeasurableSet
      (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B) :=
    measurableSet_Ioc.prod hB
  have hlocal : Measurable[
      ⨆ C ∈ {C : Set (ℝ × ℝ) |
            C ⊆ Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance]
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) :=
    Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1
      P ν N _ hR
  have hmeas : Measurable[ℱ t]
      (fun ω => ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
        z.2 ∂(N.N ω)) :=
    hlocal.mono
      (Kyprianou.Ch02.prmPastLocalEvalSigmaLeCompletedFiltrationV1
        P ν N B hB ℱ hℱ t) le_rfl
  change StronglyMeasurable[ℱ t]
    (fun ω => (∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
      z.2 ∂(N.N ω)) - (t : ℝ) * (∫ x in B, x ∂ν))
  exact hmeas.stronglyMeasurable.sub stronglyMeasurable_const
