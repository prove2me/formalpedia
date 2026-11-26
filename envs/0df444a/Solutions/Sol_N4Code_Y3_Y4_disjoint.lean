-- Prove2me | solution 1 for N4Code.Y3_Y4_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:56.104866+00:00
-- url     : https://prove2.me/submissions/88a1273c-2f3a-492b-9d4b-d23a3cf1a8ad

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y4 C t y) := by
  rintro ⟨hy3, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega
end N4Code
