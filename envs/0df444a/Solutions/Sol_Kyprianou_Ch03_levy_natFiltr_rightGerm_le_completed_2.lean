-- Prove2me | solution 2 for Kyprianou.Ch03.levy_natFiltr_rightGerm_le_completed
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:20:19.939421+00:00
-- url     : https://prove2.me/submissions/b8aee57a-ace1-494a-9a49-f67df32554df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_levyRightGermPastEventApproximationV1
import Theorems.Thm_Kyprianou_Ch03_eventApproximationImpliesNullCompletedMeasurableV2
open MeasureTheory ProbabilityTheory
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) :
    (⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s) ≤
      PerfCorrMSQ.natFiltr X t ⊔
        MeasurableSpace.generateFrom
            {A : Set Omega |
              exists N : Set Omega,
                MeasurableSet N ∧ P N = 0 ∧ A ⊆ N} := by
  intro A hA
  exact eventApproximationImpliesNullCompletedMeasurableV2 P
    (PerfCorrMSQ.natFiltr X t) A
    (fun ε hε => levyRightGermPastEventApproximationV1 P X hX t A hA ε hε)
