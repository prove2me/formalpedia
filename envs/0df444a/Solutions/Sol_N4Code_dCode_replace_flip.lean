-- Prove2me | solution 1 for N4Code.dCode_replace_flip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:08:39.458796+00:00
-- url     : https://prove2.me/submissions/de5fd57f-f3bf-4571-b5dc-73b04bfa9672

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dCode_replace_1_3

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) (hcol : C t = col1) :
    dCode (replaceColumn C t col3) (flipBit t y) = min (dOp C t y) (dP C y) := by
  rw [dCode_replace_1_3 C t (flipBit t y) hcol]
  unfold dOp dPp
  rw [flipBit_involutive]
end N4Code
