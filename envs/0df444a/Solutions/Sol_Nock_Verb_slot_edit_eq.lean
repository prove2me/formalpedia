-- Prove2me | solution 1 for Nock.Verb.slot_edit_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:21:25.730085+00:00
-- url     : https://prove2.me/submissions/f8462653-fa40-48b4-84af-626eb7122ead

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Theorems.Thm_Nock_Verb_slot_one

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution :
    ∀ (ax : Nat) {new old res : Noun},
      Noun.edit ax new old = some res → Noun.slot ax res = some new := by
  intro ax
  induction ax using Nat.strongRecOn with
  | ind ax ih =>
    intro new old res h
    match ax with
    | 0 => rw [Noun.edit] at h; exact absurd h (by simp)
    | 1 =>
        rw [Noun.edit] at h
        obtain rfl := Option.some.inj h
        exact slot_one
    | (a + 2) =>
        rw [Noun.edit] at h
        simp only at h
        cases hs : Noun.slot (if (a + 2) % 2 == 0 then a + 2 + 1 else a + 2 - 1) old with
        | none => rw [hs] at h; exact absurd h (by simp)
        | some sib =>
            rw [hs] at h
            have hres :
                Noun.slot ((a + 2) / 2)
                    res
                  = some (if (a + 2) % 2 == 0 then Noun.cell new sib else Noun.cell sib new) :=
              ih ((a + 2) / 2) (by omega) h
            rw [Noun.slot, hres]
            by_cases hpar : ((a + 2) % 2 == 0) = true
            · simp only [hpar, ite_true]
            · simp only [Bool.not_eq_true] at hpar
              simp only [hpar, ite_false, Bool.false_eq_true]
end Nock.Verb
