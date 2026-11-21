-- Prove2me | solution 1 for GwExact.testBit_rem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:27.12572+00:00
-- url     : https://prove2.me/submissions/44dfceeb-5cd0-48b1-98e1-deeab67810e1

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (a b v : Nat) :
    (Nat.xor a (Nat.land a b)).testBit v = (a.testBit v && !b.testBit v) := by
  show (a ^^^ (a &&& b)).testBit v = _
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases a.testBit v <;> cases b.testBit v <;> rfl
end GwExact
