-- Prove2me | solution 1 for OAI.SharpPlanar.D_9_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T22:19:58.853144+00:00
-- url     : https://prove2.me/submissions/515993ad-753f-47fd-901f-a09554d02b74

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_D_as_table_g
import Theorems.Thm_OAI_SharpPlanar_b_pos_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma b_lt_one : b < 1 := by nlinarith [b_sq_g, b_pos_g]

lemma one_sub_b_ne : 1 - b ≠ 0 := by linarith [b_lt_one]
lemma one_add_b_ne : 1 + b ≠ 0 := by linarith [b_pos_g]

lemma D_9_g_oai : D 9 = Real.pi * (3-2*b) / 18 := by
  rw [D_as_table_g, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_g]
  norm_num
  field_simp [one_sub_b_ne, one_add_b_ne]
  ring_nf
  simp only [b_sq_g]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.D_9_g_oai := @OAI.SharpPlanar.D_9_g_oai
