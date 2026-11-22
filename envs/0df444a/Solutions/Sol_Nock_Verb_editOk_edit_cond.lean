-- Prove2me | solution 1 for Nock.Verb.editOk_edit_cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:03:17.962438+00:00
-- url     : https://prove2.me/submissions/330eca7b-3d00-4af7-8d53-e1a113388c4b

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Definitions.Def_LeanPool_PureNock_Semantics
public import Definitions.Def_LeanPool_PureNock_Agreement

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
open Noun
namespace Nock.Verb
theorem _root_.solution {l r} (h : editOk (.node .edit l r) = true) : Verb.isPending r = false :=
  by
  simp only [editOk, Bool.and_eq_true] at h
  have := h.1.1
  simpa using this
end Nock.Verb
