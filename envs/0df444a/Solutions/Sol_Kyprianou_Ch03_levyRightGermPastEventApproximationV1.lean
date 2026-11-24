-- Prove2me | solution 1 for Kyprianou.Ch03.levyRightGermPastEventApproximationV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T07:28:57.038977+00:00
-- url     : https://prove2.me/submissions/11492501-6427-4967-9ba9-edd2383503f2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch02_aemeasurableWholePathOfIsLevyProcessV1
import Theorems.Thm_Kyprianou_Ch03_rawRightGermPastFutureLatticeV1
import Theorems.Thm_Kyprianou_Ch03_rawRightGermIndepFuturePathV1
import Theorems.Thm_Kyprianou_Ch03_indepPastFutureJoinEventApproximationV1
open MeasureTheory ProbabilityTheory
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The probabilistic approximation follows from full-future independence and lattice bounds. -/
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (t : NNReal) (A : Set Omega)
    (hA : MeasurableSet[⨅ s : NNReal, ⨅ (_ : t < s), PerfCorrMSQ.natFiltr X s] A)
    (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ B : Set Omega, MeasurableSet[PerfCorrMSQ.natFiltr X t] B ∧
      P ((A \ B) ∪ (B \ A)) < ε := by
  obtain ⟨hmg, hgh, hjoin⟩ := rawRightGermPastFutureLatticeV1 X t
  have hInd := rawRightGermIndepFuturePathV1 P X hX t
  have hpath := Kyprianou.Ch02.aemeasurableWholePathOfIsLevyProcessV1 P X hX
  refine indepPastFutureJoinEventApproximationV1 P _ _ _ hmg hgh hInd ?_ A hA ε hε
  intro S hS
  obtain ⟨D, hD, rfl⟩ := MeasurableSpace.measurableSet_comap.mp (hjoin S hS)
  exact hpath.nullMeasurableSet_preimage hD
