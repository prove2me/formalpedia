-- Prove2me | solution 1 for Nock.Verb.Den_wut
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:13.245245+00:00
-- url     : https://prove2.me/submissions/2a2575fe-9ed5-4e13-9392-f7b0cd333c9d

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
theorem _root_.solution {l r x} : ¬ Den (.node .wut l r) x := by
  rintro ⟨fuel, h⟩
  cases fuel with
  | zero => simp [den] at h
  | succ f => simp [den] at h
end Nock.Verb
