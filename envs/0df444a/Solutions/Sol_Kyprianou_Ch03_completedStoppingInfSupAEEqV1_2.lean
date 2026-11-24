-- Prove2me | solution 2 for Kyprianou.Ch03.completedStoppingInfSupAEEqV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:20:42.264328+00:00
-- url     : https://prove2.me/submissions/11b57356-2724-4970-b893-f44fafdb7a43

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_completedStoppingTimeIInfISupAEEqV1
open MeasureTheory ProbabilityTheory Filter Set
open Kyprianou.Ch03
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → Real)
    (hX : IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : Omega → WithTop NNReal)
    (U : ℕ → ℕ → Omega → WithTop NNReal)
    (hRC : F.IsRightContinuous)
    (hU : ∀ m n, IsStoppingTime F (U m n))
    (hEq : T =ᵐ[P] (fun w => ⨅ m : ℕ, ⨆ n : ℕ, U m n w)) :
    IsStoppingTime F T := by
  exact Kyprianou.Ch03.completedStoppingTimeIInfISupAEEqV1 P F X hX hNatural hRC U hU T hEq
