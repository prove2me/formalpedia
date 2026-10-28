-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_j
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:50:11.321261+00:00
-- url     : https://prove2.me/submissions/5975d972-f271-4b2c-a395-aa18bd34aa51

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

private theorem valid_true_j_oai : certificate (true, .j) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_j_oai := @OAI.ArExplicit.CocycleData.valid_true_j_oai
