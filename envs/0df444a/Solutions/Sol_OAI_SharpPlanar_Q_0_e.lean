-- Prove2me | solution 1 for OAI.SharpPlanar.Q_0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:28:51.53462+00:00
-- url     : https://prove2.me/submissions/bbc1994a-5cad-413e-93b3-d09969f8a5ee

import Mathlib
import Definitions.Def_OAIQ098E018
import Theorems.Thm_OAI_SharpPlanar_Q_as_table_e
import Theorems.Thm_OAI_SharpPlanar_b_sq_e

section
-- module Solutions.OAIQ098_PP.PlanarPacking_Nodes
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar

lemma Q_0_e_oai : Q 0 = Real.pi^2/3 := by
  rw [Q_as_table_e, show 0 % 12 = 0 from rfl,
    show residues.erase 0 = {1, 3, 4, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_e]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_0_e_oai := @OAI.SharpPlanar.Q_0_e_oai
