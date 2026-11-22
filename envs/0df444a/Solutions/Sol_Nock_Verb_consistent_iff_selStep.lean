-- Prove2me | solution 1 for Nock.Verb.consistent_iff_selStep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:20:50.070566+00:00
-- url     : https://prove2.me/submissions/8b0bba9c-ff29-42a4-8c25-d75fd4468cad

module
public import Definitions.Def_LeanPool_PureNock_Verb
public import Batteries.Tactic.Alias
public import Definitions.Def_LeanPool_PureNock_Trace
public import Theorems.Thm_Nock_Verb_next_eq_some_iff


set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Verb
namespace Nock.Verb
theorem _root_.solution : ∀ (T : List Verb),
    Consistent T ↔ ConsistentR (SelStep dfsLt) T
  | []             => Iff.rfl
  | [_]            => Iff.rfl
  | a :: b :: rest => by
      simp only [Consistent, ConsistentR]
      exact and_congr next_eq_some_iff (solution (b :: rest))
end Nock.Verb
