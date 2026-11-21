-- Prove2me | solution 1 for GwExact.not_beq_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:05.488676+00:00
-- url     : https://prove2.me/submissions/5b87a85b-90b6-4bcd-aa91-f7435534c0ed

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (a b : Nat) : (!Nat.beq a b) = true ↔ a ≠ b := by
  cases h : Nat.beq a b
  · simp only [Bool.not_false, true_iff]; intro e; subst e; simp at h
  · simp only [Bool.not_true, Bool.false_eq_true, false_iff, Classical.not_not]
    exact Nat.eq_of_beq_eq_true h
end GwExact
