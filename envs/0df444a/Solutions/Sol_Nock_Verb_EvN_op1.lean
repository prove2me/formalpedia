-- Prove2me | solution 1 for Nock.Verb.EvN_op1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:41.448566+00:00
-- url     : https://prove2.me/submissions/dbc17cf6-c3e4-4c09-9c1c-9ad96b8da14d

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
theorem _root_.solution {subj tail x} : Ev subj (.cell (.atom 1) tail) x ↔ x = tail := by
  constructor
  · rintro ⟨fuel, h⟩
    cases fuel with
    | zero => simp [evalN] at h
    | succ f => simp only [evalN] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨1, by simp only [evalN]⟩
end Nock.Verb
