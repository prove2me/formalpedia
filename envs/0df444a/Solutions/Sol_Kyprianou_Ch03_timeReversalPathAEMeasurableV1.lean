-- Prove2me | solution 1 for Kyprianou.Ch03.timeReversalPathAEMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T08:17:57.185432+00:00
-- url     : https://prove2.me/submissions/a1d83e3f-bc02-450a-bd6e-4a583af35aeb

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch03_measurableLeftEvaluationOnCadlagV1
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    AEMeasurable (fun omega : Omega =>
      fun s : {s : NNReal // s <= t} =>
        (if (s : NNReal) = t then X 0 omega
         else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
           X t omega) P ∧
    AEMeasurable (fun omega : Omega => fun s : {s : NNReal // s <= t} => -(X (s : NNReal) omega)) P := by
  obtain ⟨L, hL, hLc⟩ := Kyprianou.Ch03.measurableLeftEvaluationOnCadlagV1
  have hm := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  let R (f : NNReal → ℝ) (s : {s : NNReal // s <= t}) :=
    (if (s : NNReal) = t then f 0 else L (t - (s : NNReal)) f) - f t
  have hr : Measurable R := by
    apply measurable_pi_iff.mpr
    intro s
    by_cases hs : (s : NNReal) = t
    · simp only [R, if_pos hs]
      exact
        (measurable_pi_apply (0 : NNReal)).sub (measurable_pi_apply t)
    · simp only [R, if_neg hs]
      exact
        (hL (t - (s : NNReal))).sub (measurable_pi_apply t)
  constructor
  · refine (hr.comp_aemeasurable hm).congr ?_
    filter_upwards [hX.cadlag_ae] with ω hc
    funext s
    change R (fun r => X r ω) s = _
    by_cases hs : (s : NNReal) = t
    · simp [R, hs]
    · have hu : 0 < t - (s : NNReal) :=
        tsub_pos_of_lt (lt_of_le_of_ne s.property hs)
      simp [R, hs, hLc (fun r => X r ω) hc _ hu]
  · let G (f : NNReal → ℝ) (s : {s : NNReal // s <= t}) := -f (s : NNReal)
    have hg : Measurable G :=
      measurable_pi_iff.mpr fun s => (measurable_pi_apply (s : NNReal)).neg
    exact hg.comp_aemeasurable hm
