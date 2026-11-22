-- Prove2me | solution 1 for Nock.Verb.Den_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:11:08.903632+00:00
-- url     : https://prove2.me/submissions/77c6e892-6047-4f44-b91f-1e644a0d3efd

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
theorem _root_.solution {k x} : Den (.leaf k) x ↔ x = .atom k := by
  constructor
  · rintro ⟨fuel, h⟩; simp only [den] at h; exact (Option.some.inj h).symm
  · rintro rfl; exact ⟨0, by simp [den]⟩
end Nock.Verb
