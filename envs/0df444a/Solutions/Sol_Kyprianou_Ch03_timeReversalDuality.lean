-- Prove2me | solution 1 for Kyprianou.Ch03.timeReversalDuality
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:57:13.99784+00:00
-- url     : https://prove2.me/submissions/26a8fc56-1fb9-4c71-8972-e7cf59113786

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_LevyExtrema_SBA_runSup
import Theorems.Thm_AvramDividend_Classical_piPathMeasure_eq_of_finite_cylinder_masses
import Theorems.Thm_Kyprianou_Ch03_timeReversalPathAEMeasurableV1
import Theorems.Thm_Kyprianou_Ch03_timeReversalFiniteCylinderPreimagesV1
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (ht : 0 < t) :
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          (if (s : NNReal) = t then X 0 omega
           else Function.leftLim (fun r : NNReal => X r omega) (t - (s : NNReal))) -
             X t omega) P =
    Measure.map
      (fun omega : Omega =>
        fun s : {s : NNReal // s <= t} =>
          -(X (s : NNReal) omega)) P := by
  have hm := Kyprianou.Ch03.timeReversalPathAEMeasurableV1 P X hX t ht
  apply AvramDividend.Classical.piPathMeasure_eq_of_finite_cylinder_masses
  · rw [Measure.map_apply_of_aemeasurable hm.1 MeasurableSet.univ]
    simp
  · intro J B hB
    have hs : MeasurableSet (Set.pi (J : Set {s : NNReal // s <= t}) B) :=
      MeasurableSet.pi J.countable_toSet hB
    rw [Measure.map_apply_of_aemeasurable hm.1 hs,
      Measure.map_apply_of_aemeasurable hm.2 hs]
    exact Kyprianou.Ch03.timeReversalFiniteCylinderPreimagesV1 P X hX t ht J B hB
