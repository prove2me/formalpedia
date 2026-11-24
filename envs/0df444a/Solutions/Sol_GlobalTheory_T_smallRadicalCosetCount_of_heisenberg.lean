-- Prove2me | solution 1 for GlobalTheory.T.smallRadicalCosetCount_of_heisenberg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:22:27.311371+00:00
-- url     : https://prove2.me/submissions/b8e67d51-22bc-44b0-a57e-77ee154b66da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenberg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallRadicalCosetCountOfHeisenbergStatement
import Theorems.Thm_GlobalTheory_InertZeta_count_of_heis


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.InertZeta
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Heis → LatIndex → TraceIndex → Count := by
  first | exact @GlobalTheory.InertZeta.count_of_heis | exact GlobalTheory.InertZeta.count_of_heis | (intros; apply GlobalTheory.InertZeta.count_of_heis <;> assumption)
end _root_.GlobalTheory.T
