-- Prove2me | solution 1 for GwExact.find_node
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:25.85419+00:00
-- url     : https://prove2.me/submissions/04c3ffd7-4fbe-4a0c-bb1e-5d7fffd15dc3

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_land_one
public import Theorems.Thm_GwExact_shiftRight_one

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (l r : Trie) (v : Option Cls) (k : Nat) :
    (Trie.node l v r).find k =
      if k = 0 then v else if k % 2 = 1 then l.find (k / 2) else r.find (k / 2 - 1) := by
  simp only [Trie.find, land_one, shiftRight_one, Bool.cond_eq_ite, Nat.beq_eq, Nat.sub_eq]
end GwExact
