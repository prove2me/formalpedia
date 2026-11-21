-- Prove2me | solution 1 for GwExact.beq_true
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:19:41.746176+00:00
-- url     : https://prove2.me/submissions/0d4ef1a2-646e-4917-b62d-9eb393a5fb5a

module
public import Definitions.Def_GwExact_Check

set_option autoImplicit true
@[expose] public section
public section
open GwExact
namespace GwExact
theorem _root_.solution {a b : Nat} (h : a = b) : Nat.beq a b = true := by
  subst h; exact Nat.beq_refl a
end GwExact
