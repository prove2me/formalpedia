-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_x
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:52:05.128547+00:00
-- url     : https://prove2.me/submissions/11da1b2d-aea9-48b0-b1a7-1e3ae92a4a7a

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

private theorem valid_true_x_oai : certificate (true, .x) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_x_oai := @OAI.ArExplicit.CocycleData.valid_true_x_oai
