-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_u
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:52:02.494129+00:00
-- url     : https://prove2.me/submissions/1e928340-c668-437e-a8d9-89d1abf96ec7

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

private theorem valid_true_u_oai : certificate (true, .u) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_u_oai := @OAI.ArExplicit.CocycleData.valid_true_u_oai
