-- Prove2me | solution 1 for Nock.Noun.size_eq_leaves_add_internal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:30:59.419055+00:00
-- url     : https://prove2.me/submissions/c14ba5e1-9093-485d-904e-3d2272351465

module
public import Definitions.Def_LeanPool_PureNock_Tree

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) : n.size = n.leaves + n.internal := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves, internal]; omega
end Nock.Noun
