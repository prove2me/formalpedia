-- Prove2me | solution 1 for Monodromy.Observation.stopped_dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:30:13.8019+00:00
-- url     : https://prove2.me/submissions/6aeb8e46-d5eb-48e0-9ae1-7f1ee44d3472

module
public import Definitions.Def_Monodromy_Observation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

open Monodromy
open Monodromy.Observation
variable {S : Type*}

theorem solution (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds : ℕ, halt ((next^[rounds]) state) = true := by
  constructor
  · intro hdom
    obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp hdom
    refine StateTransition.evalInduction hb (fun a _ ih ↦ ?_)
    cases hstep : stopped next halt a with
    | none =>
        have hh : halt a = true := by
          cases hhalt : halt a with
          | false => simp [stopped, hhalt] at hstep
          | true => rfl
        exact ⟨0, by simpa using hh⟩
    | some a' =>
        obtain ⟨rounds, hr⟩ := ih a' hstep
        refine ⟨rounds + 1, ?_⟩
        have hnext : next a = a' := by
          cases hhalt : halt a with
          | false => simpa [stopped, hhalt] using hstep
          | true => simp [stopped, hhalt] at hstep
        simpa [Function.iterate_succ_apply, hnext] using hr
  · rintro ⟨rounds, hr⟩
    induction rounds generalizing state with
    | zero =>
        have hh : halt state = true := by simpa using hr
        refine Part.dom_iff_mem.mpr ⟨state, StateTransition.mem_eval.mpr
          ⟨Relation.ReflTransGen.refl, ?_⟩⟩
        simp [stopped, hh]
    | succ rounds ih =>
        by_cases hh : halt state = true
        · exact Part.dom_iff_mem.mpr ⟨state, StateTransition.mem_eval.mpr
            ⟨Relation.ReflTransGen.refl, by simp [stopped, hh]⟩⟩
        · have hr' : halt ((next^[rounds]) (next state)) = true := by
            simpa [Function.iterate_succ_apply] using hr
          obtain ⟨b, hb⟩ := Part.dom_iff_mem.mp (ih (next state) hr')
          obtain ⟨hreaches, hnone⟩ := StateTransition.mem_eval.mp hb
          refine Part.dom_iff_mem.mpr ⟨b, StateTransition.mem_eval.mpr ⟨?_, hnone⟩⟩
          exact Relation.ReflTransGen.head (by simp [stopped, hh]) hreaches
