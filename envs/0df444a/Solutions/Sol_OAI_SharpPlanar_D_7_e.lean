-- Prove2me | solution 1 for OAI.SharpPlanar.D_7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:25:05.626778+00:00
-- url     : https://prove2.me/submissions/d6c31744-f533-41e6-a083-05ea7ae58339

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_D_as_table_e
import Theorems.Thm_OAI_SharpPlanar_b_pos_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_lt_one : b < 1 := by nlinarith [b_sq_e, b_pos_e]

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos_e]

lemma D_7_e_oai : D 7 = -Real.pi * (3-2*b) / 18 := by
  rw [D_as_table_e, show 7 % 12 = 7 from rfl,
    show residues.erase 7 = {0, 1, 3, 4, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_e]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq_e]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.D_7_e_oai := @OAI.SharpPlanar.D_7_e_oai
