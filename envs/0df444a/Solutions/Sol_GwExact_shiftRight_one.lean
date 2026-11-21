-- Prove2me | solution 1 for GwExact.shiftRight_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:18:55.637911+00:00
-- url     : https://prove2.me/submissions/55ba3eb5-59d4-4e0d-8b03-ae1149e9ca7a

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (k : Nat) : Nat.shiftRight k 1 = k / 2 := by
  show k >>> 1 = k / 2
  simp [Nat.shiftRight_eq_div_pow]
end GwExact
