-- Prove2me | solution 1 for OAI.SharpPlanar.Q_3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:29:38.495136+00:00
-- url     : https://prove2.me/submissions/abe7db60-3c1f-43a8-8682-a0bf9f66bff0

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

lemma Q_3_e_oai : Q 3 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table_e, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_3_e_oai := @OAI.SharpPlanar.Q_3_e_oai
