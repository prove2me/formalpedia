-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:42:51.62692+00:00
-- url     : https://prove2.me/submissions/0a889c76-0110-4d2b-bafe-e2f3df51bb85

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

private theorem valid_false_e_oai : certificate (false, .e) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_e_oai := @OAI.ArExplicit.CocycleData.valid_false_e_oai
