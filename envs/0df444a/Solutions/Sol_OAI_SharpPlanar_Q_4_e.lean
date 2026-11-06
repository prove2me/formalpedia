-- Prove2me | solution 1 for OAI.SharpPlanar.Q_4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-05T20:30:22.687848+00:00
-- url     : https://prove2.me/submissions/27e220c8-e435-4e71-8c9c-60ff82347e5f

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

lemma Q_4_e_oai : Q 4 = Real.pi^2/3 := by
  rw [Q_as_table_e, show 4 % 12 = 4 from rfl,
    show residues.erase 4 = {0, 1, 3, 7, 9} from by decide]
  norm_num [sinTable, cosTable]
  ring_nf
  try simp only [b_sq_e]
  ring

end SharpPlanar

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Q_4_e_oai := @OAI.SharpPlanar.Q_4_e_oai
