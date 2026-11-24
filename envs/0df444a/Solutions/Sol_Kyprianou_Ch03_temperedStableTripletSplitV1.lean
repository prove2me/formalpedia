-- Prove2me | solution 1 for Kyprianou.Ch03.temperedStableTripletSplitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T17:43:23.254025+00:00
-- url     : https://prove2.me/submissions/9c280606-425a-4ac7-b488-8ff8e22c3d1d

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
  let p := Kyprianou.Ch03.temperedStablePositiveMeasure cp ap gp
  let m := Kyprianou.Ch03.temperedStablePositiveMeasure cm am gm
  have he : T.levyMeasure = p + m.map (fun x : ℝ => -x) := hMeasure
  have hP : IsLevyMeasure p :=
    Kyprianou.Ch03.temperedStableMeasureMonoV1 p T.levyMeasure
      (by rw [he]; exact Measure.le_add_right le_rfl) T.levyMeasure_isLevyMeasure
  have hM' : IsLevyMeasure (m.map (fun x : ℝ => -x)) :=
    Kyprianou.Ch03.temperedStableMeasureMonoV1 _ T.levyMeasure
      (by rw [he]; exact Measure.le_add_left le_rfl) T.levyMeasure_isLevyMeasure
  have hM : IsLevyMeasure m := Kyprianou.Ch03.temperedStableMeasureReflectionV1 m hM'
  let TP : LevyKhintchineTriple := ⟨T.drift, 0, p, hP⟩
  let TM : LevyKhintchineTriple := ⟨0, 0, m, hM⟩
  refine ⟨TP, TM, rfl, rfl, rfl, rfl, fun xi => ?_⟩
  unfold Kyprianou.Ch01.levyTripleExponent
  simp only [TP, TM, hGaussian, NNReal.coe_zero, zero_mul, zero_div, Complex.ofReal_zero, sub_zero, zero_add]
  rw [he, integral_add_measure
    (ProbabilityTheory.integrable_levyCompensatedIntegrand hP xi)
    (ProbabilityTheory.integrable_levyCompensatedIntegrand hM' xi),
    Kyprianou.Ch03.temperedStableExponentReflectionV1 m xi]
  ring
