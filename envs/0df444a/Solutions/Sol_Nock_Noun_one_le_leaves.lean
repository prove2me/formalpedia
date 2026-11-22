-- Prove2me | solution 1 for Nock.Noun.one_le_leaves
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:24.96475+00:00
-- url     : https://prove2.me/submissions/bdf035b0-b9a2-4c48-85b3-68efb454a0ca

module
public import Definitions.Def_LeanPool_PureNock_Tree

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) : 1 ≤ n.leaves := by
  induction n with
  | atom k => simp [leaves]
  | cell l r ihl ihr => simp only [leaves]; omega
end Nock.Noun
