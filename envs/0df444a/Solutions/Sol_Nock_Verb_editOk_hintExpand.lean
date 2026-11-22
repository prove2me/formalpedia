-- Prove2me | solution 1 for Nock.Verb.editOk_hintExpand
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:22:26.330629+00:00
-- url     : https://prove2.me/submissions/fa05b47a-f77e-47d3-a397-3c834505962d

module
public import Definitions.Def_LeanPool_PureNock_Agreement
public import Definitions.Def_LeanPool_PureNock_Trace
public import Definitions.Def_LeanPool_PureNock_PaperReference
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_LeanPool_PureNock_PureAgreement
public import Theorems.Thm_Nock_Verb_editOk_of_terminal

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {sub e} (he : hintExpand sub = some e) : editOk e = true := by
  unfold hintExpand at he
  split at he
  · rename_i n1 ra n2
    split at he
    · rename_i hguard
      simp only [Bool.and_eq_true] at hguard
      obtain ⟨⟨h1, _⟩, hn2⟩ := hguard
      split at he
      · rename_i rn2 innerA tb clue body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨⟨_, ⟨_, hclue⟩⟩, hbody⟩ := hn2
        simp [editOk, editOk_of_terminal h1,
          editOk_of_terminal hclue, editOk_of_terminal hbody]
      · rename_i rn2 t body
        obtain rfl := Option.some.inj he
        simp only [isTerminal, Bool.and_eq_true] at hn2
        obtain ⟨_, hbody⟩ := hn2
        simp [editOk, editOk_of_terminal h1,
          editOk_of_terminal hbody]
      · simp at he
    · simp at he
  · simp at he
end Nock.Verb
