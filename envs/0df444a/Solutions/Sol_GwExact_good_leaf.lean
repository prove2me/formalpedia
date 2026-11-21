-- Prove2me | solution 1 for GwExact.good_leaf
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:52.814013+00:00
-- url     : https://prove2.me/submissions/fab1218a-1952-4a63-89a5-ee77e5f224bf

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (σ : Nat → Bool) : Good σ .leaf := by
  intro k c h
  simp [Trie.find] at h
end GwExact
