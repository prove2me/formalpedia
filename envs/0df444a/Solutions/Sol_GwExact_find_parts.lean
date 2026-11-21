-- Prove2me | solution 1 for GwExact.find_parts
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:52.109294+00:00
-- url     : https://prove2.me/submissions/c25b426c-b7a7-423e-ad0a-424c466d8f7a

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_find_node

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (t : Trie) (k : Nat) :
    t.find k = if k = 0 then t.val else if k % 2 = 1 then t.left.find (k / 2) else t.right.find (k / 2 - 1) := by
  cases t with
  | leaf => simp [Trie.find, Trie.val, Trie.left, Trie.right]
  | node l v r => rw [find_node]; rfl
end GwExact
