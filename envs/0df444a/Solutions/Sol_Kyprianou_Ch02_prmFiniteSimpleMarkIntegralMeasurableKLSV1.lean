-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteSimpleMarkIntegralMeasurableKLSV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T18:28:20.91951+00:00
-- url     : https://prove2.me/submissions/1228ceb1-de28-4971-bcdf-42d8124d08a6

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
import Theorems.Thm_Kyprianou_Ch02_prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Local evaluation measurability implies ambient measurability for simple marks. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (R : Set (ℝ × ℝ)) (hRm : MeasurableSet R)
    (f : SimpleFunc ℝ ℝ) :
    Measurable (fun (ω : Ω) =>
      ∫ z in R, f z.2 ∂(N.N ω)) := by
  have hg : Measurable (fun z : ℝ × ℝ => f z.2) :=
    f.measurable.comp measurable_snd
  have hp :=
    Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
      P ν N R hRm
      (R.indicator (fun z : ℝ × ℝ => ENNReal.ofReal (f z.2)))
      (hg.ennreal_ofReal.indicator hRm)
      (fun z hz => Set.indicator_of_notMem hz _)
  have hn :=
    Kyprianou.Ch02.prmNonnegativeIntegralMeasurableLocalEvalSigmaV1
      P ν N R hRm
      (R.indicator (fun z : ℝ × ℝ => ENNReal.ofReal (-(f z.2))))
      (hg.neg.ennreal_ofReal.indicator hRm)
      (fun z hz => Set.indicator_of_notMem hz _)
  have hlocal :=
    Kyprianou.Ch02.prmSignedSimpleIntegralMeasurableFromPosNegKLSV1
      P ν N R hRm f hp hn
  have hle :
      (⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
        MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) ≤
      (inferInstance : MeasurableSpace Ω) := by
    exact iSup₂_le fun C hC => (N.measurable_eval hC.2).comap_le
  exact hlocal.mono hle le_rfl
