-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_t
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:45:04.445546+00:00
-- url     : https://prove2.me/submissions/1a443251-6760-4e0b-863e-4dd8a2f82aae

import Mathlib
import Definitions.Def_OAIQ031A000

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

private theorem valid_false_t_oai : certificate (false, .t) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_t_oai := @OAI.ArExplicit.CocycleData.valid_false_t_oai
