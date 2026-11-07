-- Prove2me | solution 1 for Monodromy.ReversibleTuring.macroStep_live
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:14:58.243386+00:00
-- url     : https://prove2.me/submissions/16d4eff0-4116-434e-9967-33935fdb7ea8

import Definitions.Def_Monodromy_FormalCompilation
import Theorems.Thm_Monodromy_ReversibleTuring_step_firstReturn
import Mathlib.Computability.StateTransition

open Monodromy
open Monodromy.ReversibleTuring
open Turing

variable (a q : ℕ) [NeZero a] [NeZero q]

private theorem boundaryTransition_stops (machine : TM0.Machine (Fin a) (Fin q))
    {state : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (marked : Boundary a q machine state) : boundaryTransition a q machine state = none := by
  simp only [boundaryTransition, ite_eq_left marked]

private theorem internal_marked_reaches (machine : TM0.Machine (Fin a) (Fin q))
    {first last : Counter.Reversible.State 4
      (Counter.Reversible.Recording.size (RecordedTuring.size a q machine))}
    (run : Counter.Reversible.Recording.InternalMarkedReaches
      (NativeTuring.source2 a q machine) (NativeTuring.counterMark a q machine) first last) :
    StateTransition.Reaches (boundaryTransition a q machine) first last := by
  induction run with
  | refl => exact Relation.ReflTransGen.refl
  | @tail first last _ edge previous =>
      apply previous.tail
      change (if Boundary a q machine first then none
        else Counter.Reversible.step (table a q machine) first) = some last
      have unmarked : ¬ Boundary a q machine first := edge.2
      rw [ite_eq_right unmarked]
      exact edge.1

theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      macroStep a q machine (encode a q machine first history) =
        Part.some (some (encode a q machine last finalHistory)) := by
  obtain ⟨finalHistory, grew, _, marked, next, initial, rest⟩ :=
    step_firstReturn a q machine transition history
  have completed : StateTransition.eval (boundaryTransition a q machine) next =
      Part.some (encode a q machine last finalHistory) := by
    apply Part.eq_some_iff.mpr
    exact StateTransition.mem_eval.mpr
      ⟨internal_marked_reaches a q machine rest, boundaryTransition_stops a q machine marked⟩
  refine ⟨finalHistory, grew, ?_⟩
  change Counter.Reversible.step (table a q machine) (encode a q machine first history) =
    some next at initial
  simp only [macroStep, initial, completed, Part.map_some]
