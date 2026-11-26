-- Prove2me | solution 1 for N4Code.Y1_Y5_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:36.922644+00:00
-- url     : https://prove2.me/submissions/e67a12a5-e200-48c6-aa40-efd41eb9905c

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y5 C t y) := by
  rintro ⟨hy1, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy1 with hy1 | hy1
  · rcases hy1 with ⟨h1a, h1b⟩
    omega
  · rcases hy1 with ⟨h1a, h1b, h1c⟩
    omega
end N4Code
