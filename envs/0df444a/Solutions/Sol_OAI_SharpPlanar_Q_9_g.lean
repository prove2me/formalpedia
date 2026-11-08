-- Prove2me | solution 1 for OAI.SharpPlanar.Q_9_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:11:17.706702+00:00
-- url     : https://prove2.me/submissions/53b0b86a-193a-4946-bbd5-c2e726f6dfe8

import Mathlib
import Definitions.Def_OAIQ098G072
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma Q_9_g_oai : Q 9 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table_g, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_9_g_oai := @OAI.SharpPlanar.Q_9_g_oai
