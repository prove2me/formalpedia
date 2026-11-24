-- Prove2me | solution 2 for Kyprianou.Ch03.temperedStableTripletSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:52:12.784327+00:00
-- url     : https://prove2.me/submissions/0406bb62-3195-47de-91ad-5a75c549738d

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
import Theorems.Thm_Kyprianou_Ch03_temperedStableMeasureMonoV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableMeasureReflectionV1
import Theorems.Thm_Kyprianou_Ch03_temperedStableExponentReflectionV1
import Theorems.Thm_ProbabilityTheory_integrable_levyCompensatedIntegrand
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (T : LevyKhintchineTriple)
    (cp ap gp cm am gm : ℝ) (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      Kyprianou.Ch03.temperedStableSignedMeasure cp ap gp cm am gm) :
    ∃ TP TM : LevyKhintchineTriple,
      TP.gaussianVariance = 0 ∧ TM.gaussianVariance = 0 ∧
      TP.levyMeasure = Kyprianou.Ch03.temperedStablePositiveMeasure cp ap gp ∧
      TM.levyMeasure = Kyprianou.Ch03.temperedStablePositiveMeasure cm am gm ∧
      ∀ xi, Kyprianou.Ch01.levyTripleExponent T xi =
        Kyprianou.Ch01.levyTripleExponent TP xi +
        Kyprianou.Ch01.levyTripleExponent TM (-xi) := by
  let nuP := Kyprianou.Ch03.temperedStablePositiveMeasure cp ap gp
  let nuM := Kyprianou.Ch03.temperedStablePositiveMeasure cm am gm
  have hsum : T.levyMeasure = nuP + nuM.map (fun x : ℝ => -x) := hMeasure
  have hP := Kyprianou.Ch03.temperedStableMeasureMonoV1 nuP T.levyMeasure
    (by rw [hsum]; exact Measure.le_add_right (le_refl nuP)) T.levyMeasure_isLevyMeasure
  have hR := Kyprianou.Ch03.temperedStableMeasureMonoV1 (nuM.map (fun x : ℝ => -x))
    T.levyMeasure (by rw [hsum]; exact Measure.le_add_left (le_refl _)) T.levyMeasure_isLevyMeasure
  have hM := Kyprianou.Ch03.temperedStableMeasureReflectionV1 nuM hR
  refine ⟨⟨T.drift, 0, nuP, hP⟩, ⟨0, 0, nuM, hM⟩, rfl, rfl, rfl, rfl, ?_⟩
  intro xi
  simp only [Kyprianou.Ch01.levyTripleExponent, hGaussian, hsum]
  rw [integral_add_measure (ProbabilityTheory.integrable_levyCompensatedIntegrand hP xi)
    (ProbabilityTheory.integrable_levyCompensatedIntegrand hR xi),
    Kyprianou.Ch03.temperedStableExponentReflectionV1]
  push_cast
  ring
