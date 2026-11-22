-- Prove2me | solution 1 for Nock.Verb.run_sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:44.66489+00:00
-- url     : https://prove2.me/submissions/369c6670-6095-4c30-8b7f-b7295b62cbee

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_den_terminal
public import Theorems.Thm_Nock_Verb_editOk_next
public import Theorems.Thm_Nock_Verb_den_step

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {v : Verb} {r : Noun} :
    ∀ fuel, editOk v = true → run fuel v = some r → (∃ f, den f v = some r) := by
  intro fuel
  induction fuel generalizing v with
  | zero => intro _ h; simp [run] at h
  | succ fuel ih =>
      intro hwf h
      rw [run] at h
      cases hnext : next v with
      | some v' =>
          rw [hnext] at h
          exact (den_step hwf hnext).2 (ih (editOk_next hnext hwf) h)
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
