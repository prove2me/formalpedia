-- Prove2me | solution 1 for Kyprianou.Ch05.completeStrictPassageMarkovLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:13.343901+00:00
-- url     : https://prove2.me/submissions/1ca95601-1bab-49da-bb3c-65f7afc595ea

import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Probability.ConditionalProbability
import Theorems.Thm_Kyprianou_Ch03_completedNaturalFiltrationExistsV1
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime_of_isOpen
import Theorems.Thm_Kyprianou_Ch03_strongMarkovAtExtendedStoppingTime
import Definitions.Def_Kyprianou_Ch05_CompleteStrictPassageMarkovLaw
open MeasureTheory Filter ProbabilityTheory
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05
/-- Compose the verified Chapter 3 filtration, stopping time and Markov laws. -/
theorem solution : CompleteStrictPassageMarkovLaw := by
  unfold CompleteStrictPassageMarkovLaw
  intro Omega m P hP hComplete Y hLevy hCoord x entranceTime finiteTime hEntrance hFinite
  obtain ⟨F, hF⟩ := Kyprianou.Ch03.completedNaturalFiltrationExistsV1 P Y hCoord
  have hStop := Kyprianou.Ch03.entranceHit_firstHittingIsStoppingTime_of_isOpen
    P F Y hLevy hF (Set.Ioi x) isOpen_Ioi entranceTime finiteTime (fun w hw => hEntrance w (by simpa using hw))
    (fun w hw => hFinite w (by simpa using hw))
  refine ⟨F, hF, hStop, ?_⟩
  intro A hA
  simpa using Kyprianou.Ch03.strongMarkovAtExtendedStoppingTime P F Y hLevy hF
    (Kyprianou.Ch03.firstHittingTime Y (Set.Ioi x)) hStop finiteTime
    (fun w hw => hFinite w (by simpa using hw)) A hA
