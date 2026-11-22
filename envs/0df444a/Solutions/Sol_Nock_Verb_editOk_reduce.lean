-- Prove2me | solution 1 for Nock.Verb.editOk_reduce
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:12:08.798223+00:00
-- url     : https://prove2.me/submissions/b76240a1-fb7b-49ba-ab11-8cc50e55af4a

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_editOk_ofNoun
public import Theorems.Thm_Nock_Verb_editOk_null_eq
public import Theorems.Thm_Nock_Verb_editOk_star_eq
public import Theorems.Thm_Nock_Verb_editOk_children

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub r₀} (hr : reduce sub = some r₀) (hok : editOk sub = true) :
    editOk r₀ = true := by
  cases sub with
  | leaf => simp [reduce] at hr
  | node a n1 t =>
    simp only [editOk, Bool.and_eq_true] at hok
    obtain ⟨⟨_, hokn1⟩, hokt⟩ := hok
    cases a with
    | null => simp [reduce] at hr
    | wut => simp [reduce] at hr
    | equal => rw [reduce] at hr; obtain rfl := Option.some.inj hr; exact editOk_ofNoun _
    | slot =>
        rw [reduce] at hr
        cases hln : n1.noun with
        | cell => simp [hln] at hr
        | atom ax =>
            rw [hln, Option.map_eq_some_iff] at hr
            obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
    | minus =>
        rw [reduce] at hr
        split at hr
        · obtain rfl := Option.some.inj hr; exact editOk_ofNoun _
        · rw [Option.map_eq_some_iff] at hr; obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
        · simp at hr
    | edit =>
        cases hln : n1.noun with
        | cell => simp [reduce, hln] at hr
        | atom ax =>
            cases t with
            | leaf => simp [reduce, hln] at hr
            | node b nw od =>
                simp only [reduce, hln, Option.map_eq_some_iff] at hr
                obtain ⟨sr, _, rfl⟩ := hr; exact editOk_ofNoun _
    | star =>
        -- redex
        cases t with
        | leaf => simp [reduce, redex] at hr
        | node ra i n2 =>
          simp only [editOk, Bool.and_eq_true] at hokt
          obtain ⟨⟨_, hoki⟩, hokn2⟩ := hokt
          rw [reduce] at hr
          cases i with
          | node bi ic id =>
              rw [redex] at hr
              obtain rfl := Option.some.inj hr
              simp only [editOk_null_eq, editOk_star_eq, hokn1, hoki, hokn2, Bool.and_self]
          | leaf op =>
              simp only [redex] at hr
              have ecell : ∀ (bn b c : _), n2 = Verb.node bn b c →
                  editOk b = true ∧ editOk c = true := by
                intro bn b c he; subst he; exact editOk_children hokn2
              split at hr
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · obtain rfl := Option.some.inj hr; exact hokn2
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokn2]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr; simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn b c =>
                    obtain ⟨hokb, hokc⟩ := ecell bn b c rfl
                    obtain rfl := Option.some.inj hr
                    simp [editOk, hokn1, hokb, hokc]
              · cases n2 with
                | leaf => simp at hr
                | node bn hd d =>
                    cases hd with
                    | leaf => simp at hr
                    | node bhd ax c =>
                        obtain ⟨hokhd, hokd⟩ := editOk_children hokn2
                        obtain ⟨hokax, hokc⟩ := editOk_children hokhd
                        obtain rfl := Option.some.inj hr
                        simp [editOk, Verb.isPending, Action.isNull, hokn1, hokax, hokc, hokd]
              · simp at hr
end Nock.Verb
