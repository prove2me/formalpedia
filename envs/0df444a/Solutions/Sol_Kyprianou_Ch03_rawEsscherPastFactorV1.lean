-- Prove2me | solution 1 for Kyprianou.Ch03.rawEsscherPastFactorV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T23:18:54.549608+00:00
-- url     : https://prove2.me/submissions/96ccbe8d-c655-4752-b188-35f608e22c6a

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_PerfCorrMSQ_NaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_rawEsscherPastLIntegralFactorV1
import Theorems.Thm_Kyprianou_Ch03_nonnegativeIndicatorIntegralOfRealV1
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch03

theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : NNReal → Ω → ℝ) (hX : IsLevyProcess X P)
    (beta : ℝ)
    (hm : ∀ t, Measurable (X t))
    (k : ℝ)
    (hunit : ∀ t : NNReal, Integrable (esscherDensity X beta k t) P ∧
      (∫ w, esscherDensity X beta k t w ∂P) = 1) :
    ∀ s t : NNReal, s ≤ t → ∀ A,
      MeasurableSet[PerfCorrMSQ.natFiltr X s] A →
      (∫ w, A.indicator (esscherDensity X beta k t) w ∂P) =
        (∫ w, A.indicator (esscherDensity X beta k s) w ∂P) := by
  intro s t hst A hA
  have hle : PerfCorrMSQ.natFiltr X s ≤ (inferInstance : MeasurableSpace Ω) :=
    iSup₂_le fun v _ => (hm v).comap_le
  have hAm : MeasurableSet A := hle A hA
  have he (u : NNReal) := Kyprianou.Ch03.nonnegativeIndicatorIntegralOfRealV1
    P (esscherDensity X beta k u) A hAm (hunit u).1 (fun w => (Real.exp_pos _).le)
  have hn (u : NNReal) : 0 ≤ ∫ w, A.indicator (esscherDensity X beta k u) w ∂P :=
    integral_nonneg fun w => Set.indicator_nonneg (fun _ _ => (Real.exp_pos _).le) w
  have hh := Kyprianou.Ch03.rawEsscherPastLIntegralFactorV1 P X hX beta hm k hunit s t hst A hA
  have hr := congrArg ENNReal.toReal ((he t).trans (hh.trans (he s).symm))
  simpa only [ENNReal.toReal_ofReal (hn t), ENNReal.toReal_ofReal (hn s)] using hr
