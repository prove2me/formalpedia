-- Prove2me | solution 1 for OAI.SharpPlanar.Q_9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:30:47.705073+00:00
-- url     : https://prove2.me/submissions/0d5125e1-e74a-478f-9aa2-a282224bba6b

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma Q_9_e_oai : Q 9 = (2*Real.pi^2/3)*(2+2*b) := by
  rw [Q_as_table_e, show 9 % 12 = 9 from rfl,
    show residues.erase 9 = {0, 1, 3, 4, 7} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_9_e_oai := @OAI.SharpPlanar.Q_9_e_oai
