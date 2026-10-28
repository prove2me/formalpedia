-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_n
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:45:03.316048+00:00
-- url     : https://prove2.me/submissions/171d262a-f722-42d8-82e8-3a334ca99e1a

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

private theorem valid_false_n_oai : certificate (false, .n) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_n_oai := @OAI.ArExplicit.CocycleData.valid_false_n_oai
