-- Prove2me | solution 1 for Monodromy.Counter.TuringCompiler.step_firstReturn
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:05:35.716915+00:00
-- url     : https://prove2.me/submissions/6aaf623a-43ee-47a7-a53f-09f39fc9b826

module
public import Definitions.Def_Monodromy_Counter
public import Theorems.Thm_Monodromy_Counter_TuringCompiler_move_reaches

@[expose] public section

open Monodromy
open Monodromy.Counter
open Monodromy.Counter.TuringCompiler
open Turing
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (source : TM0.step machine first = some last) :
    FirstReturn a q machine (encode a q first) (encode a q last) := by
  cases transition : machine first.q first.Tape.head with
  | none => simp [TM0.step, transition] at source
  | some command =>
      rcases command with ⟨target, operation⟩
      cases operation with
      | write value =>
          have destination : (⟨target, first.Tape.write value⟩ : TM0.Cfg (Fin a) (Fin q)) = last := by
            simpa [TM0.step, transition] using source
          subst last
          exact ⟨_, by simp [step, encode, transition, counters, Tape.write],
            Relation.ReflTransGen.refl⟩
      | move direction =>
          have destination : (⟨target, first.Tape.move direction⟩ : TM0.Cfg (Fin a) (Fin q)) = last := by
            simpa [TM0.step, transition] using source
          subst last
          refine ⟨⟨mulTarget a q (first.q, first.Tape.head) 0, (encode a q first).counters⟩, ?_,
            move_reaches a q machine first target direction transition⟩
          simp [step, encode, transition, counters]
