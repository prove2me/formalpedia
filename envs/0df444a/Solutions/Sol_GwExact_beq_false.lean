-- Prove2me | solution 1 for GwExact.beq_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:29.460395+00:00
-- url     : https://prove2.me/submissions/00273169-a6ce-4796-8f28-e2f3c79884b4

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {a b : Nat} (h : ¬ a = b) : Nat.beq a b = false := by
  cases hb : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h
end GwExact
