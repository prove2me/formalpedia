-- Prove2me | solution 1 for GwExact.testBit_bit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:20:24.470733+00:00
-- url     : https://prove2.me/submissions/8b2f5e90-7e66-4b8f-a261-3f62069259b4

module
public import Batteries.Tactic.Alias
public import Definitions.Def_GwExact_Check
public import Definitions.Def_GwExact_Clauses

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (v u : Nat) : (bit v).testBit u = decide (v = u) := by
  show (1 <<< v).testBit u = _
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]
end GwExact
