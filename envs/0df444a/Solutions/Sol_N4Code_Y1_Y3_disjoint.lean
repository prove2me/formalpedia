-- Prove2me | solution 1 for N4Code.Y1_Y3_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:29:57.163774+00:00
-- url     : https://prove2.me/submissions/b8cb7e60-dea8-4d20-9c77-090ddd5ac7f6

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y3 C t y) := by
  rintro ⟨hy1, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega
end N4Code
