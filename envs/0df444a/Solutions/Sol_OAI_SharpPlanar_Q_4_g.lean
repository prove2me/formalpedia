-- Prove2me | solution 1 for OAI.SharpPlanar.Q_4_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:11:02.821944+00:00
-- url     : https://prove2.me/submissions/1a959e1a-0169-4930-a4b3-ab1732bc9459

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_g
import Theorems.Thm_OAI_SharpPlanar_b_sq_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma Q_4_g_oai : Q 4 = Real.pi^2/3 := by
  rw [Q_as_table_g, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_g]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_4_g_oai := @OAI.SharpPlanar.Q_4_g_oai
