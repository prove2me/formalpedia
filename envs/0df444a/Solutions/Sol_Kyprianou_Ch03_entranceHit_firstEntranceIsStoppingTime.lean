-- Prove2me | solution 1 for Kyprianou.Ch03.entranceHit_firstEntranceIsStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T09:43:40.250806+00:00
-- url     : https://prove2.me/submissions/06631e77-64fb-4d83-a05d-166f5bcfbfe9

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch03_EntryAndHittingTimes
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Theorems.Thm_Kyprianou_Ch03_entranceHit_firstHittingIsStoppingTime
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch03

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (B : Set Real) (hB : IsOpen B ∨ IsClosed B)
    (entranceTime hittingTime : Omega -> NNReal)
    (hEntranceTime : forall omega,
      firstEntranceTime X B omega != ⊤ ->
        firstEntranceTime X B omega = (entranceTime omega : WithTop NNReal))
    (hHittingTime : forall omega,
      firstHittingTime X B omega != ⊤ ->
        firstHittingTime X B omega = (hittingTime omega : WithTop NNReal)) :
    IsStoppingTime F (firstEntranceTime X B) := by
  have hz (omega : Omega) : X 0 omega = 0 := congrFun hX.start_zero omega
  by_cases h0 : (0 : Real) ∈ B
  · have heq : firstEntranceTime X B = fun _ => ((0 : NNReal) : WithTop NNReal) := by
      funext omega
      unfold firstEntranceTime
      apply le_antisymm
      · apply sInf_le
        exact ⟨0, by simpa only [Set.mem_setOf_eq, hz omega] using h0, rfl⟩
      · exact bot_le
    rw [heq]
    intro t
    have hset : {omega : Omega | ((0 : NNReal) : WithTop NNReal) ≤ t} = Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact bot_le
    rw [hset]
    exact MeasurableSet.univ
  · have heq : firstEntranceTime X B = firstHittingTime X B := by
      funext omega
      unfold firstEntranceTime firstHittingTime
      have hs : {t : NNReal | X t omega ∈ B} =
          {t : NNReal | 0 < t ∧ X t omega ∈ B} := by
        ext t
        simp only [Set.mem_setOf_eq]
        constructor
        · intro ht
          refine ⟨lt_of_le_of_ne (zero_le : (0 : NNReal) ≤ t) ?_, ht⟩
          intro ht0
          subst t
          exact h0 (by simpa only [hz omega] using ht)
        · exact And.right
      rw [hs]
    rw [heq]
    exact entranceHit_firstHittingIsStoppingTime P F X hX hNatural B hB
      entranceTime hittingTime hEntranceTime hHittingTime
