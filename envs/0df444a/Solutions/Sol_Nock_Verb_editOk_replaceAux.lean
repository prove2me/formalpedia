-- Prove2me | solution 1 for Nock.Verb.editOk_replaceAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:31.443643+00:00
-- url     : https://prove2.me/submissions/73947d56-9a22-47a7-8ce4-6c73aaf27a96

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_editOk_null_eq
public import Theorems.Thm_Nock_Verb_editOk_star_eq
public import Theorems.Thm_Nock_Verb_editOk_children
public import Theorems.Thm_Nock_Verb_replaceAux_counter
public import Theorems.Thm_Nock_Verb_editOk_edit_cond
public import Theorems.Thm_Nock_Verb_editOk_editN_eq
public import Theorems.Thm_Nock_Verb_isPending_replaceAux
public import Theorems.Thm_Nock_Verb_enum_index_range
public import Theorems.Thm_Nock_Verb_findAt_append
public import Theorems.Thm_Nock_Verb_findAt_eq_none
public import Theorems.Thm_Nock_Verb_findAt_some_mem


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution (i : Nat) (r₀ : Verb) (hr0 : editOk r₀ = true) :
    ∀ (v : Verb) (c : Nat), editOk v = true →
      (∀ s, findAt i (enum v c).2 = some s → s.isPending = true) →
      editOk (replaceAux i r₀ v c).2 = true := by
  intro v
  induction v with
  | leaf k => intro c _ _; simp [replaceAux, editOk]
  | node a l r ihl ihr =>
      intro c hok hpend
      obtain ⟨hokl, hokr⟩ := editOk_children hok
      simp only [replaceAux]
      by_cases hci : c = i
      · subst hci; rw [if_pos rfl]; exact hr0
      · simp only [if_neg hci]
        have hine : ¬ (i = c) := fun h => hci h.symm
        have hcL : (replaceAux i r₀ l (c+1)).1 = (enum l (c+1)).1 := replaceAux_counter i r₀ l (c+1)
        have hpl : ∀ s, findAt i (enum l (c+1)).2 = some s → s.isPending = true := by
          intro s hs; apply hpend s; simp only [enum, findAt, if_neg hine]; rw [findAt_append,
            hs]
        have hokl' : editOk (replaceAux i r₀ l (c+1)).2 = true := ihl (c+1) hokl hpl
        have hleftNone : ∀ s, findAt i (enum r (enum l (c+1)).1).2 = some s →
            findAt i (enum l (c+1)).2 = none := by
          intro s hs
          apply findAt_eq_none; intro q hq
          have := enum_index_range l (c+1) q hq
          have := enum_index_range r (enum l (c+1)).1 (i, s) (findAt_some_mem hs)
          omega
        have hpr : ∀ s, findAt i (enum r (enum l (c+1)).1).2 = some s → s.isPending = true := by
          intro s hs; apply hpend s
          simp only [enum, findAt, if_neg hine]; rw [findAt_append, hleftNone s hs, hs]
        have hokr' : editOk (replaceAux i r₀ r (enum l (c+1)).1).2 = true :=
          ihr (enum l (c+1)).1 hokr hpr
        rw [hcL]
        cases a with
        | edit =>
            have hcond : Verb.isPending r = false := editOk_edit_cond hok
            have hnp : Verb.isPending (replaceAux i r₀ r (enum l (c+1)).1).2 = false := by
              by_cases hcLi : (enum l (c+1)).1 = i
              · cases r with
                | leaf => simp [replaceAux, Verb.isPending]
                | node b nw od =>
                    exfalso
                    have hn : findAt i (enum l (c+1)).2 = none := by
                      apply findAt_eq_none; intro q hq
                      have := enum_index_range l (c+1) q hq; omega
                    have hf : findAt i (enum (Verb.node .edit l (Verb.node b nw od)) c).2
                              = some (Verb.node b nw od) := by
                      simp only [enum, findAt, if_neg hine, findAt_append, hn]
                      rw [← hcLi]; simp
                    have := hpend _ hf
                    rw [hcond] at this; simp at this
              · rw [isPending_replaceAux i r₀ r _ hcLi, hcond]
            simp only [editOk_editN_eq, hnp, hokl', hokr', Bool.not_false, Bool.and_self]
        | null => simp only [editOk_null_eq, hokl', hokr', Bool.and_self]
        | star => simp only [editOk_star_eq, hokl', hokr', Bool.and_self]
        | wut => simp only [editOk, hokl', hokr', Bool.and_self]
        | slot => simp only [editOk, hokl', hokr', Bool.and_self]
        | equal => simp only [editOk, hokl', hokr', Bool.and_self]
        | minus => simp only [editOk, hokl', hokr', Bool.and_self]
end Nock.Verb
