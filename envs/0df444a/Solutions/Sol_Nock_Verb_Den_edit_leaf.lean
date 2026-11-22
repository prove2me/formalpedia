-- Prove2me | solution 1 for Nock.Verb.Den_edit_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:12.810127+00:00
-- url     : https://prove2.me/submissions/987c0869-ecf4-48ab-a516-3b623afbf3c4

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
theorem _root_.solution {l k x} : ¬ Den (.node .edit l (.leaf k)) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [den] at h
  | succ f => simp [den] at h
end Nock.Verb
