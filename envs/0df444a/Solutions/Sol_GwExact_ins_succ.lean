-- Prove2me | solution 1 for GwExact.ins_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:26.48183+00:00
-- url     : https://prove2.me/submissions/9c7b4560-142d-4d87-9beb-e4b639451a9f

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_land_one
public import Theorems.Thm_GwExact_shiftRight_one

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (f : Nat) (t : Trie) (k : Nat) (c : Cls) :
    Trie.ins (f + 1) t k c =
      if k = 0 then .node t.left (some c) t.right
      else if k % 2 = 1 then .node (Trie.ins f t.left (k / 2) c) t.val t.right
      else .node t.left t.val (Trie.ins f t.right (k / 2 - 1) c) := by
  simp only [Trie.ins, land_one, shiftRight_one, Bool.cond_eq_ite, Nat.beq_eq, Nat.sub_eq]
end GwExact
