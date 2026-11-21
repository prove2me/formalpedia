-- Prove2me | solution 1 for GwExact.good_ins
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:22:55.651111+00:00
-- url     : https://prove2.me/submissions/17e28929-0584-4d79-b783-abc9761747ea

module
public import Definitions.Def_GwExact_Check
public import Theorems.Thm_GwExact_find_ins

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {σ : Nat → Bool} {db : Trie} (hdb : Good σ db) (f k : Nat) {c : Cls}
    (hc : c.Holds σ) : Good σ (Trie.ins f db k c) := by
  intro k' c' h
  rcases find_ins f db k c k' c' h with h1 | h1
  · exact h1 ▸ hc
  · exact hdb k' c' h1
end GwExact
