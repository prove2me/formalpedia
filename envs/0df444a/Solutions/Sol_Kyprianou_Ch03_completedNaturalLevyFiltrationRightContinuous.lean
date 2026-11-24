-- Prove2me | solution 1 for Kyprianou.Ch03.completedNaturalLevyFiltrationRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T04:00:44.690764+00:00
-- url     : https://prove2.me/submissions/26aa4e26-dac5-4a68-9621-52b0facecf17

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_levy_natFiltr_rightGerm_le_completed
import Theorems.Thm_Kyprianou_Ch03_completedNaturalFiltration_isRightContinuous_of_natRightGerm

open MeasureTheory ProbabilityTheory
open scoped NNReal

set_option autoImplicit false

/-!
Exercise 3.1: completed natural filtration of a Lévy process is right continuous.

Reduction:
1. Lévy right-germ inclusion into the completed past (`levy_natFiltr_rightGerm_le_completed`).
2. Lattice packaging under that germ hypothesis
   (`completedNaturalFiltration_isRightContinuous_of_natRightGerm`).
-/

open Kyprianou.Ch03 in
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (hCompleted : IsCompletedNaturalFiltration P X F) :
    F.IsRightContinuous :=
  completedNaturalFiltration_isRightContinuous_of_natRightGerm P X F hCompleted
    (fun t => levy_natFiltr_rightGerm_le_completed P X hX t)
