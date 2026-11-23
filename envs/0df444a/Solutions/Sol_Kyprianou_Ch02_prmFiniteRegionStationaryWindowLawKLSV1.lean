-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionStationaryWindowLawKLSV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T13:43:50.186207+00:00
-- url     : https://prove2.me/submissions/8e7090a4-0981-48e8-bbd8-8be7a9eac3fe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Theorems.Thm_Kyprianou_Ch02_realLawEqOfAETendstoApproximantsV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionShiftedSimpleApproxLawV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Stationarity follows from common finite-simple marked Poisson approximants. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B) (hfinite : ν B < ⊤) :
    ∀ s t : ℝ≥0,
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) =
      P.map (fun (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B),
          z.2 ∂(N.N ω)) := by
  have hmeas (R : Set (ℝ × ℝ)) (hR : MeasurableSet R) :
      Measurable (fun ω => ∫ z in R, z.2 ∂(N.N ω)) := by
    have hlocal :=
      Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1 P ν N R hR
    have hle :
        (⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) ≤
        (inferInstance : MeasurableSpace Ω) :=
      iSup₂_le fun C hC => (N.measurable_eval hC.2).comap_le
    exact hlocal.mono hle le_rfl
  intro s t
  obtain ⟨F, G, hF, hG, hLaw, hFlim, hGlim⟩ :=
    Kyprianou.Ch02.prmFiniteRegionShiftedSimpleApproxLawV1
      P ν N B hB hfinite s t
  exact Kyprianou.Ch02.realLawEqOfAETendstoApproximantsV1
    P F G _ _ hF hG
    (hmeas _ (measurableSet_Ioc.prod hB))
    (hmeas _ (measurableSet_Ioc.prod hB))
    hLaw hFlim hGlim
