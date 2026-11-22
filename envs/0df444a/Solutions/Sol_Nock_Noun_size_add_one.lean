-- Prove2me | solution 1 for Nock.Noun.size_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T11:59:24.406246+00:00
-- url     : https://prove2.me/submissions/f71d9104-8227-4a51-aad6-499670bf4d52

module
public import Definitions.Def_LeanPool_PureNock_Tree

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) : n.size + 1 = 2 * n.leaves := by
  induction n with
  | atom k => rfl
  | cell l r ihl ihr => simp only [size, leaves]; omega
end Nock.Noun
