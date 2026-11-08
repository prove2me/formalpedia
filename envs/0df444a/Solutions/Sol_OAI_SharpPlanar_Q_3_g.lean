-- Prove2me | solution 1 for OAI.SharpPlanar.Q_3_g
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-07T23:10:53.521189+00:00
-- url     : https://prove2.me/submissions/1d30f995-e3f6-4ccf-995c-48f76295c52a

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

lemma Q_3_g_oai : Q 3 = (2*Real.pi^2/3)*(2-2*b) := by
  rw [Q_as_table_g, show 3 % 12 = 3 from rfl,
    show residues.erase 3 = {0, 1, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_3_g_oai := @OAI.SharpPlanar.Q_3_g_oai
