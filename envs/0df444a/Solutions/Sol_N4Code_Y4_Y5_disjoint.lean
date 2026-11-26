-- Prove2me | solution 1 for N4Code.Y4_Y5_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:07:12.399786+00:00
-- url     : https://prove2.me/submissions/da106a1f-33c1-4039-8a1a-cbdb273c952f

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare
import Theorems.Thm_N4Code_dOp_le_dO_add_one

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    ¬ (Y4 C t y ∧ Y5 C t y) := by
  have h1 := dOp_le_dO_add_one C t y
  rintro ⟨hy4, hy5⟩
  rcases hy4 with ⟨h4a, h4b, h4c⟩
  rcases hy5 with ⟨h5a, h5b, h5c⟩
  omega
end N4Code
