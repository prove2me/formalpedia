-- Prove2me | solution 1 for N4Code.Y3_Y5_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:25.227068+00:00
-- url     : https://prove2.me/submissions/960bcebf-ff6e-4f96-bd45-503771bf1579

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y3 C t y ∧ Y5 C t y) := by
  rintro ⟨hy3, hy5⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  rcases hy3 with ⟨h3a, h3b, h3c⟩
  omega
end N4Code
