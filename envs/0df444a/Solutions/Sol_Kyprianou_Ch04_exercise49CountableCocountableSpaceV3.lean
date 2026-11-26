-- Prove2me | solution 1 for Kyprianou.Ch04.exercise49CountableCocountableSpaceV3
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:49:25.512798+00:00
-- url     : https://prove2.me/submissions/b831aabd-d319-4ab3-870f-ac92e6a93aa2

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {E : Type} :
    ∃ m : MeasurableSpace E, ∀ S : Set E,
      @MeasurableSet E m S ↔ S.Countable ∨ Sᶜ.Countable := by
  classical
  let m : MeasurableSpace E :=
    { MeasurableSet' := fun S => S.Countable ∨ Sᶜ.Countable
      measurableSet_empty := Or.inl Set.countable_empty
      measurableSet_compl := by
        intro S hS
        rcases hS with h | h
        · exact Or.inr (by simpa only [compl_compl] using h)
        · exact Or.inl h
      measurableSet_iUnion := by
        intro S hS
        by_cases h : ∀ n, (S n).Countable
        · exact Or.inl (Set.countable_iUnion h)
        · push_neg at h
          obtain ⟨n,hn⟩ := h
          have hc := (hS n).resolve_left hn
          exact Or.inr (hc.mono (compl_subset_compl.mpr (subset_iUnion S n))) }
  exact ⟨m,fun _ => Iff.rfl⟩
