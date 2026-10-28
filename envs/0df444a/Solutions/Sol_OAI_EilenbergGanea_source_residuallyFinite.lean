-- Prove2me | solution 1 for OAI.EilenbergGanea.source_residuallyFinite
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-25T00:13:43.321986+00:00
-- url     : https://prove2.me/submissions/e84d82ba-6a5b-4292-ab2a-91598b66db1c

import Mathlib
import Definitions.Def_EilenbergGanea
import Definitions.Def_OAIEG000
import Theorems.Thm_OAI_EilenbergGanea_artin_residuallyFinite

section
-- module Solutions.OAIEG.Model
attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Topology

namespace EilenbergGanea
/-- The second exact conjunct of the source main theorem. -/
theorem source_residuallyFinite_oai : Group.ResiduallyFinite SourceGroup := by
  have := artin_residuallyFinite SeedCell seedGraph
  infer_instance

end EilenbergGanea



end

end OAI
end

theorem solution : type_of% @OAI.EilenbergGanea.source_residuallyFinite_oai := @OAI.EilenbergGanea.source_residuallyFinite_oai
