-- Prove2me | solution 1 for Monodromy.Counter.Reversible.step_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:32:40.149324+00:00
-- url     : https://prove2.me/submissions/a253425f-7089-45ca-be5a-7182cf8a8b48

module
public import Definitions.Def_Monodromy_Counter

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.Reversible
variable {n q e : ℕ}

theorem solution (table : Table n q e) (deterministic : Deterministic table)
    {first last : State n q} : Monodromy.Counter.Reversible.step table first = some last ↔ StepRel table first last := by
  constructor
  · intro selected
    unfold Monodromy.Counter.Reversible.step at selected
    split at selected
    next available =>
      exact ⟨Fin.find (fun index => (table index).enabled first) available,
        Fin.find_spec available,
        Option.some.inj selected⟩
    next unavailable => contradiction
  · rintro ⟨index, enabled, executed⟩
    have available : ∃ index, (table index).enabled first := ⟨index, enabled⟩
    unfold Monodromy.Counter.Reversible.step
    rw [dif_pos available, Option.some.injEq]
    by_cases same : Fin.find (fun index => (table index).enabled first) available = index
    · rw [same]
      exact executed
    · exfalso
      have selected_enabled := Fin.find_spec available
      have compatible := deterministic _ _ same (selected_enabled.1.trans enabled.1.symm)
      rcases selected_enabled with ⟨-, selected_guard⟩
      rcases enabled with ⟨-, given_guard⟩
      cases selected_action : (table (Fin.find (fun index => (table index).enabled first) available)).action with
      | shift register amount =>
          cases given_action : (table index).action <;>
            simp_all [Action.Compatible]
      | test register atZero =>
          cases given_action : (table index).action with
          | shift other amount => simp_all [Action.Compatible]
          | test other otherZero =>
              cases atZero <;> cases otherZero <;>
                simp_all [Action.Compatible, Action.enabled]
