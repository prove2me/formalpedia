-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.valid_true_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:48:01.630217+00:00
-- url     : https://prove2.me/submissions/b8d83ca3-5f66-4c77-862f-07f42aaf27aa

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

private theorem valid_true_e_oai : certificate (true, .e) = true := by decide +kernel

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.valid_true_e_oai := @OAI.ArExplicit.CocycleData.valid_true_e_oai
