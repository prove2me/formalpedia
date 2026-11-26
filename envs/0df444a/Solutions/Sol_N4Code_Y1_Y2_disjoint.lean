-- Prove2me | solution 1 for N4Code.Y1_Y2_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:49.710605+00:00
-- url     : https://prove2.me/submissions/0648ea4f-0e37-48e6-9324-deba83987372

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y1 C t y ∧ Y2 C t y) := by
  rintro ⟨hy1, hy2⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    rcases hy1 with hy1 | hy1
    · rcases hy1 with ⟨h1a, h1b⟩
      omega
    · rcases hy1 with ⟨h1a, h1b, h1c⟩
      omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    rcases hy1 with hy1 | hy1
    · rcases hy1 with ⟨h1a, h1b⟩
      omega
    · rcases hy1 with ⟨h1a, h1b, h1c⟩
      omega
end N4Code
