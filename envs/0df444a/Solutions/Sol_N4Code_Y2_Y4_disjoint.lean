-- Prove2me | solution 1 for N4Code.Y2_Y4_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:04.183932+00:00
-- url     : https://prove2.me/submissions/280aed6c-7c20-49c2-a03e-b5f21e6974b1

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y4 C t y) := by
  rintro ⟨hy2, hy4⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega
end N4Code
