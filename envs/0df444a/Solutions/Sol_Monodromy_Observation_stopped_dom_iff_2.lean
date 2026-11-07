-- Prove2me | solution 2 for Monodromy.Observation.stopped_dom_iff
-- status  : ACCEPTED   (prove)
-- author  : @Xiaoyang Liu
-- created : 2026-11-06T14:58:38.738424+00:00
-- url     : https://prove2.me/submissions/e441af9e-ad83-4a95-aeb9-ff28009680c3

-- Generated mechanically from the frozen source; no own-target import.
module
public import Definitions.Def_Monodromy_Observation
public import Lean.Elab.Tactic.Omega
public import Mathlib.Computability.StateTransition
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section


-- Original target, hoisted to top-level theorem solution.
open Monodromy
open Monodromy.Observation
variable {S : Type*}
theorem solution (next : S → S) (halt : S → Bool) (state : S) :
    (StateTransition.eval (stopped next halt) state).Dom ↔
      ∃ rounds : ℕ, halt ((next^[rounds]) state) = true := by
  constructor
  · intro terminates
    obtain ⟨target, finished⟩ := Part.dom_iff_mem.mp terminates
    exact StateTransition.evalInduction finished fun current _ successors => by
      cases done : halt current with
      | true => exact ⟨0, done⟩
      | false =>
          obtain ⟨rounds, stops⟩ := successors (next current) (by simp [stopped, done])
          exact ⟨rounds + 1, by simpa only [Function.iterate_succ_apply] using stops⟩
  · rintro ⟨rounds, stops⟩
    induction rounds generalizing state with
    | zero =>
        exact Part.dom_iff_mem.mpr ⟨state,
          StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, by simpa [stopped] using stops⟩⟩
    | succ rounds previous =>
        cases done : halt state with
        | true =>
            exact Part.dom_iff_mem.mpr ⟨state,
              StateTransition.mem_eval.mpr ⟨Relation.ReflTransGen.refl, by simp [stopped, done]⟩⟩
        | false =>
            have reaches : StateTransition.Reaches (stopped next halt) state (next state) :=
              Relation.ReflTransGen.single (by simp [stopped, done])
            rw [StateTransition.reaches_eval reaches]
            exact previous (next state) (by simpa only [Function.iterate_succ_apply] using stops)
