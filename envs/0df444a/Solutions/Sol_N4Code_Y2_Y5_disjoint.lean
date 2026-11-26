-- Prove2me | solution 1 for N4Code.Y2_Y5_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:30:05.771194+00:00
-- url     : https://prove2.me/submissions/7d807aa4-bb90-4e28-a08c-86684dfbb384

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y2 C t y ∧ Y5 C t y) := by
  rintro ⟨hy2, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy2 with hy2 | hy2
  · rcases hy2 with ⟨h2a, h2b⟩
    omega
  · rcases hy2 with ⟨h2a, h2b, h2c⟩
    omega
end N4Code
