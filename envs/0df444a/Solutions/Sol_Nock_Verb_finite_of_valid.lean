-- Prove2me | solution 1 for Nock.Verb.finite_of_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:10:38.844399+00:00
-- url     : https://prove2.me/submissions/4c264330-7b13-4246-8173-f82a43967dc1

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {F : Verb} (h : Valid F) : Finite F := by
  obtain ⟨T, v, hT, hl, hn, _⟩ := h
  exact ⟨T, hT, v, hl, hn⟩
end Nock.Verb
