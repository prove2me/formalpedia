-- Prove2me | solution 1 for Kyprianou.Ch02.prmFiniteRegionStationaryIncrementsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T12:53:08.970682+00:00
-- url     : https://prove2.me/submissions/5a9ce79a-6469-4a1b-83cc-9423ecaa7c6e

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch06_stationaryIncrementsFromMarginalLaw
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStartZeroV1
import Theorems.Thm_Kyprianou_Ch02_prmMarkedIntegralMeasurableLocalEvalSigmaV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionStationaryWindowLawKLSV1
import Theorems.Thm_Kyprianou_Ch02_prmFiniteRegionIntegralIncrementStripAEV1

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hfinite : ν B < ⊤) :
    ProbabilityTheory.HasStationaryIncrements
      (fun (t : ℝ≥0) (ω : Ω) =>
        ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)) P := by
  let X : ℝ≥0 → Ω → ℝ := fun t ω =>
    ∫ z in (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B), z.2 ∂(N.N ω)
  have hmeas : ∀ t : ℝ≥0, Measurable (X t) := by
    intro t
    let R : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ B
    have hR : MeasurableSet R := measurableSet_Ioc.prod hB
    have hlocal :=
      Kyprianou.Ch02.prmMarkedIntegralMeasurableLocalEvalSigmaV1 P ν N R hR
    have hle :
        (⨆ C ∈ {C : Set (ℝ × ℝ) | C ⊆ R ∧ MeasurableSet C},
          MeasurableSpace.comap (fun ω => N.N ω C) inferInstance) ≤
        (inferInstance : MeasurableSpace Ω) :=
      iSup₂_le fun C hC => (N.measurable_eval hC.2).comap_le
    exact hlocal.mono hle le_rfl
  have hzero : ∀ᵐ ω ∂P, X 0 ω = 0 :=
    Filter.Eventually.of_forall
      (fun ω => congrFun (Kyprianou.Ch02.prmFiniteRegionStartZeroV1 P ν N B) ω)
  have hAE :=
    Kyprianou.Ch02.prmFiniteRegionIntegralIncrementStripAEV1
      P ν N B hB hfinite
  have hlaw : ∀ s t : ℝ≥0,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t) := by
    intro s t
    calc
      P.map (fun ω => X (s + t) ω - X s ω) =
        P.map (fun (ω : Ω) =>
          ∫ z in (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ B),
            z.2 ∂(N.N ω)) := by
          apply Measure.map_congr
          filter_upwards [hAE] with ω hω
          exact hω s (s + t) (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from zero_le))
      _ = P.map (X t) :=
        Kyprianou.Ch02.prmFiniteRegionStationaryWindowLawKLSV1
          P ν N B hB hfinite s t
  exact Kyprianou.Ch06.stationaryIncrementsFromMarginalLaw P X hmeas hzero hlaw
