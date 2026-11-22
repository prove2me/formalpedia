-- Prove2me | solution 1 for Nock.Verb.run_soundP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:25:05.289419+00:00
-- url     : https://prove2.me/submissions/214c41ca-2659-4488-93d5-831d6598066a

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_denP_terminal
public import Theorems.Thm_Nock_Verb_den_stepP
public import Theorems.Thm_Nock_Verb_editOk_next


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, denP f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [run] at h
  | succ fuel ih =>
      intro hwf h
      rw [run] at h
      cases hnext : next v with
      | some v' =>
          rw [hnext] at h
          exact (den_stepP hwf hnext).2 (ih (editOk_next hnext hwf) h)
      | none =>
          rw [hnext] at h
          simp only [result] at h
          split at h
          · rename_i hterm
            have hr : v.noun = r := Option.some.inj h
            subst hr
            exact ⟨v.noun.size, denP_terminal v v.noun.size hterm (Nat.le_refl _)⟩
          · simp at h
end Nock.Verb
