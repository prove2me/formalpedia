-- Prove2me | solution 1 for Nock.Noun.shape_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:17:15.781742+00:00
-- url     : https://prove2.me/submissions/c35f9629-e203-4ce6-9957-24d26c964e30

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Mathlib.Combinatorics.Enumerative.Catalan.Tree
public import Definitions.Def_LeanPool_PureNock_Dyck

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) : n.shape.size = n.size := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [shape, Nock.BTree.size, size]; omega
end Nock.Noun
