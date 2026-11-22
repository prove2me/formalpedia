-- Prove2me | solution 1 for Nock.Verb.runHint_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:24:27.452823+00:00
-- url     : https://prove2.me/submissions/fdbfb99e-fe95-4e98-9b51-b21a39293a56

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_editOk_nextHint
public import Theorems.Thm_Nock_Verb_denHint_step
public import Theorems.Thm_Nock_Verb_den_terminal


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → runHint fuel v = some r → (∃ f, den f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [runHint] at h
  | succ fuel ih =>
      intro hwf h
      rw [runHint] at h
      cases hnext : nextHint v with
      | some v' =>
          rw [hnext] at h
          exact (denHint_step hwf hnext).2 (ih (editOk_nextHint hnext hwf) h)
      | none =>
          rw [hnext] at h
          simp only [result] at h
          split at h
          · rename_i hterm
            have hr : v.noun = r := Option.some.inj h
            subst hr
            exact ⟨v.noun.size, den_terminal v v.noun.size hterm (Nat.le_refl _)⟩
          · simp at h
end Nock.Verb
