-- Prove2me | solution 1 for N4Code.dPp_le_dP_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:05:23.297212+00:00
-- url     : https://prove2.me/submissions/4e7bd850-6e34-4225-bcaa-9d4cd99cf9d1

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dPp C t y ≤ dP C y + 1 := by
  unfold dPp dP
  exact (dRow_flip_le_add_one C ⟨2, by decide⟩ t y).1
end N4Code
