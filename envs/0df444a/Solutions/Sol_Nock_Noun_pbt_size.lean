-- Prove2me | solution 1 for Nock.Noun.pbt_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:09:57.180031+00:00
-- url     : https://prove2.me/submissions/f7157764-b5a6-409c-b250-865a114d5c47

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Theorems.Thm_Nock_Noun_size_add_one

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution (n : Noun) :
    n.size = 2 * n.leaves - 1 ∧ n.internal = n.leaves - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  refine ⟨by omega, ?_⟩
  induction n with
  | atom k => rfl
  | cell l r ihl ihr =>
      have hl := size_add_one l
      have hr := size_add_one r
      simp only [internal, leaves]; omega
end Nock.Noun
