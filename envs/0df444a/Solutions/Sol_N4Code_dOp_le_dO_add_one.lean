-- Prove2me | solution 1 for N4Code.dOp_le_dO_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:04:11.423631+00:00
-- url     : https://prove2.me/submissions/6e130156-2a76-4642-81a1-794a3a55a864

import Definitions.Def_N4Code_Comparison
import Mathlib.Tactic.FieldSimp
import Definitions.Def_N4Code_Compare

set_option autoImplicit true
open N4Code
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t : Fin n) (y : Word n) :
    dOp C t y ≤ dO C y + 1 := by
  unfold dOp dO
  apply min3_le_add_one
  · exact (dRow_flip_le_add_one C ⟨0, by decide⟩ t y).1
  · exact (dRow_flip_le_add_one C ⟨1, by decide⟩ t y).1
  · exact (dRow_flip_le_add_one C ⟨3, by decide⟩ t y).1
end N4Code
