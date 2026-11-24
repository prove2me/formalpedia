-- Prove2me | solution 1 for Kirkman.boseQ_idem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:44:10.602764+00:00
-- url     : https://prove2.me/submissions/9795e2d4-f28c-4536-8a98-63f85b013eb5

module
public import Mathlib
public import Definitions.Def_KirkmanLib_Constructions
public import Definitions.Def_KirkmanLib_Instances

set_option autoImplicit true
@[expose] public section
public section
open Kirkman
variable {n : ℕ} (hn : n % 2 = 1)
namespace Kirkman
theorem _root_.solution (x : ZMod n) : (boseQ hn).L x x = x := by
  change (x + x) * half n = x
  linear_combination x * two_mul_half hn
end Kirkman
