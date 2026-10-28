-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_u
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:45:26.969986+00:00
-- url     : https://prove2.me/submissions/65e88ac2-a637-4d27-9815-c8bba9e434a9

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

private theorem valid_false_u_oai : certificate (false, .u) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_u_oai := @OAI.ArExplicit.CocycleData.valid_false_u_oai
