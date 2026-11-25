-- Prove2me | solution 1 for GlobalTheory.T.unitaryIwasawaCosetSurj_of_leviElementExists
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:27:43.135646+00:00
-- url     : https://prove2.me/submissions/807cbc5c-33e0-42ef-a3a2-af8082885007

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCosetSurjOfLeviElementExists
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCosetSurjOfLeviElementExistsStatement
import Theorems.Thm_GlobalTheory_InertZeta_cosetSurj_of_leviExists


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
theorem _root_.solution : LeviExists → CosetSurj := by
  first | exact @GlobalTheory.InertZeta.cosetSurj_of_leviExists | exact GlobalTheory.InertZeta.cosetSurj_of_leviExists | (intros; apply GlobalTheory.InertZeta.cosetSurj_of_leviExists <;> assumption)
end _root_.GlobalTheory.T
