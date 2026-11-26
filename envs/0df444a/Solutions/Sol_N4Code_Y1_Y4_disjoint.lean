-- Prove2me | solution 1 for N4Code.Y1_Y4_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:50.084941+00:00
-- url     : https://prove2.me/submissions/7c170aac-8839-4b81-b2e2-3a588e1de51d

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y4 C t y) := by
  rintro ⟨hy1, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega
end N4Code
