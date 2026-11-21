-- Prove2me | solution 1 for GwExact.land_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:18:55.138637+00:00
-- url     : https://prove2.me/submissions/d35e36ae-336e-4a7d-8823-64300d2871b8

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (k : Nat) : Nat.land k 1 = k % 2 := Nat.and_one_is_mod k
end GwExact
