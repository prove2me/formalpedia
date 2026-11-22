-- Prove2me | solution 1 for Nock.Verb.eval_crash_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:15.858595+00:00
-- url     : https://prove2.me/submissions/94293da3-4f18-4d90-8aa8-8ac89f2d121a

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_crash_of_trace

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution {v : Verb} (h : Invalid v) : ∃ n, eval n v = .crash := by
  obtain ⟨T, w, ⟨hhead, hcons⟩, hlast, hnext, hnt⟩ := h
  exact ⟨T.length, crash_of_trace T v w hhead hcons hlast hnext hnt⟩
end Nock.Verb
