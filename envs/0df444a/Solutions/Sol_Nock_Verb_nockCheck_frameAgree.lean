-- Prove2me | solution 1 for Nock.Verb.nockCheck_frameAgree
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:31:06.976925+00:00
-- url     : https://prove2.me/submissions/c29a402e-d4ed-4935-a66b-da358ea5e148

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Definitions.Def_LeanPool_PureNock_Reference
public import Definitions.Def_LeanPool_PureNock_Verb
public import Theorems.Thm_Nock_Verb_getIndex_eq_some_iff
public import Theorems.Thm_Nock_Verb_next_eq_some_iff
public import Theorems.Thm_Nock_Verb_nockCheck_eq_true_iff

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {a b : Verb} (h : NockCheck a (some b) = true) :
    ∃ i, getIndex a = some i ∧ FrameAgree i a b := by
  rcases nockCheck_eq_true_iff.1 h with ⟨v, hbv, hnext⟩ | ⟨hb, _⟩
  · have hvb : v = b := (Option.some.inj hbv).symm
    subst hvb
    obtain ⟨i, sub, r, hmax, _, _, _, hb⟩ := next_eq_some_iff.1 hnext
    exact ⟨i, getIndex_eq_some_iff.2 hmax, r, hb⟩
  · exact absurd hb (by simp)
end Nock.Verb
