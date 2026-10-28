-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_v
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:52:03.877045+00:00
-- url     : https://prove2.me/submissions/4a406b07-7416-4131-9a57-e8c10f993d9e

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

private theorem valid_true_v_oai : certificate (true, .v) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_v_oai := @OAI.ArExplicit.CocycleData.valid_true_v_oai
