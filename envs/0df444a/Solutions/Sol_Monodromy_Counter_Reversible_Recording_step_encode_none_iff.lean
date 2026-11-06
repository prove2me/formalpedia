-- Prove2me | solution 1 for Monodromy.Counter.Reversible.Recording.step_encode_none_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:37:20.548064+00:00
-- url     : https://prove2.me/submissions/43f4f774-a65d-4edf-8b41-410ae3bec83d

module
public import Definitions.Def_Monodromy_Counter
public import Theorems.Thm_Monodromy_Counter_Reversible_Recording_halt_no_outgoing

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
open Monodromy.Counter.Reversible.Recording
variable {n m : ℕ}

private theorem step_halt_aux (program : Counter.Program n m)
    (state : Counter.Configuration n m) (instruction : program state.pc = .halt) :
    Counter.step program state = none := by
  simp [Counter.step, instruction]

private theorem step_none_iff_aux {n q e : ℕ} (table : Table n q e) (state : State n q) :
    Reversible.step table state = none ↔ ¬ ∃ index, (table index).enabled state := by
  unfold Reversible.step
  split_ifs <;> simp_all

private theorem extraOperation_inc_aux (program : Counter.Program n m) (arc : Extra program)
    (register : Fin n) (target : Fin m) (instruction : program arc.val.1 = .inc register target) :
    extraOperation program arc = .shift (Fin.castAdd 2 register) 1 := by
  unfold extraOperation
  split <;> simp_all

@[simp] private theorem frame_old_aux (values : Fin n → ℕ) (history workspace : ℤ) (index : Fin n) :
    frame values history workspace (Fin.castAdd 2 index) = (values index : ℤ) := by
  simp [frame]

theorem solution (program : Counter.Program n m)
    (state : Counter.Configuration n m) (history : ℕ) :
    step (table program) (encode state history) = none ↔ Counter.step program state = none := by
  rw [step_none_iff_aux]
  cases instruction : program state.pc with
  | halt =>
      constructor
      · intro _
        exact step_halt_aux program state instruction
      · intro _
        rintro ⟨index, enabled⟩
        exact halt_no_outgoing program state.pc instruction index enabled.1
  | inc register target =>
      simp only [Counter.step, instruction, reduceCtorEq, iff_false, not_not]
      let arc : Extra program := ⟨(state.pc, 0), by simp [Active, instruction]⟩
      refine ⟨arcEquiv program (.inr arc), ?_⟩
      rw [table_arc]
      change (extraEdge program arc).enabled (encode state history)
      simp only [extraEdge, Edge.enabled, encode, framed]
      rw [extraOrigin_inc program arc register target instruction,
        extraOperation_inc_aux program arc register target instruction]
      exact ⟨rfl, trivial⟩
  | dec register zero nonzero =>
      have live : Counter.step program state ≠ none := by
        cases count : state.counters register <;> simp [Counter.step, instruction, count]
      simp only [live, iff_false, not_not]
      by_cases empty : state.counters register = 0
      · let arc : Extra program := ⟨(state.pc, 0), by simp [Active, instruction]⟩
        refine ⟨arcEquiv program (.inr arc), ?_⟩
        rw [table_arc]
        change (extraEdge program arc).enabled (encode state history)
        simp only [extraEdge, Edge.enabled, encode, framed]
        rw [extraOrigin_dec program arc register zero nonzero instruction,
          extraOperation_dec program arc register zero nonzero instruction]
        exact ⟨rfl, by simp [Action.enabled, arc, empty]⟩
      · let arc : Extra program := ⟨(state.pc, 1), by simp [Active, instruction]⟩
        refine ⟨arcEquiv program (.inr arc), ?_⟩
        rw [table_arc]
        change (extraEdge program arc).enabled (encode state history)
        simp only [extraEdge, Edge.enabled, encode, framed]
        rw [extraOrigin_dec program arc register zero nonzero instruction,
          extraOperation_dec program arc register zero nonzero instruction]
        exact ⟨rfl, by simp [Action.enabled, arc, empty]⟩
