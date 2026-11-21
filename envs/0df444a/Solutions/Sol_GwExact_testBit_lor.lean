-- Prove2me | solution 1 for GwExact.testBit_lor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:53.388916+00:00
-- url     : https://prove2.me/submissions/b412e5f1-1a51-49ec-be1b-3c7f6de0f1cb

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution (a b v : Nat) : (Nat.lor a b).testBit v = (a.testBit v || b.testBit v) :=
  Nat.testBit_or a b v
end GwExact
