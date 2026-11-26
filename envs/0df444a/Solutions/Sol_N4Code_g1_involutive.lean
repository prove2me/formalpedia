-- Prove2me | solution 1 for N4Code.g1_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:15.234696+00:00
-- url     : https://prove2.me/submissions/3680c3fb-6386-4308-b7b3-1e833c2f7073

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    g1 C t (g1 C t y) = y := by
  by_cases hy : Y1 C t y ∨ Y3 C t y
  · simp [g1, hy]
  · have hcl := Y13_complement_closed C t y hy
    simp [g1, hy, hcl, flipBit_involutive t y]
end N4Code
