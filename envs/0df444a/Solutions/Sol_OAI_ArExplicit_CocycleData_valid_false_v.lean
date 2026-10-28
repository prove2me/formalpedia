-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_false_v
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:45:49.158812+00:00
-- url     : https://prove2.me/submissions/1651d65c-7dde-466e-8840-74996d4f5bf4

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

private theorem valid_false_v_oai : certificate (false, .v) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_false_v_oai := @OAI.ArExplicit.CocycleData.valid_false_v_oai
