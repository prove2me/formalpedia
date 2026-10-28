-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_z
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:48:00.31209+00:00
-- url     : https://prove2.me/submissions/e145cd95-66b9-43f7-beff-45dd586c9f14

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

private theorem valid_false_z_oai : certificate (false, .z) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_z_oai := @OAI.ArExplicit.CocycleData.valid_false_z_oai
