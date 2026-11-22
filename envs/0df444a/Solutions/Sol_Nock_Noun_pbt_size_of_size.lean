-- Prove2me | solution 1 for Nock.Noun.pbt_size_of_size
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:19:07.157118+00:00
-- url     : https://prove2.me/submissions/892575a9-31bb-4073-9edb-e3c3d9b328b1

module
public import Definitions.Def_LeanPool_PureNock_Tree
public import Theorems.Thm_Nock_Noun_size_add_one
public import Theorems.Thm_Nock_Noun_pbt_size

set_option autoImplicit true
@[expose] public section
public section
open Nock
open Nock.Noun
namespace Nock.Noun
theorem _root_.solution {n : Noun} {lam : Nat} (hlam : 1 ≤ lam)
    (h : n.size = 2 * lam - 1) : n.leaves = lam ∧ n.internal = lam - 1 := by
  have hs : n.size + 1 = 2 * n.leaves := size_add_one n
  have hi : n.internal = n.leaves - 1 := (pbt_size n).2
  refine ⟨by omega, by omega⟩
end Nock.Noun
