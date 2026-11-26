-- Prove2me | solution 1 for N4Code.Y2_Y3_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:51.41737+00:00
-- url     : https://prove2.me/submissions/def52611-929d-415a-89ae-d257598afbaf

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y3 C t y) := by
  rintro ⟨hy2, hy3⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega
end N4Code
