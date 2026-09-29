-- Prove2me | solution 1 for NumberField.StandardAddChar.isGlobalAddChar_stdAddChar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0c3bcaef-a7a5-5e7e-8b90-cde16b71812a

import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar

open NumberField NumberField.StandardAddChar AutomorphicForm

theorem solution
    (F : Type) [Field F] [NumberField F] :
    IsGlobalAddChar F (stdAddChar F) :=
  (adelicTraceData F).isGlobalAddChar_psiK

end S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar
end P2MW
export P2MW.S_NumberField_StandardAddChar_isGlobalAddChar_stdAddChar (solution)
