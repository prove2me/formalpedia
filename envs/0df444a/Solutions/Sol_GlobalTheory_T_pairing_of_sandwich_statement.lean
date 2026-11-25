-- Prove2me | solution 1 for GlobalTheory.T.pairing_of_sandwich_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:24:22.476572+00:00
-- url     : https://prove2.me/submissions/2b09ff53-0565-4ad7-99d7-7ecd8dd55781

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermLat_pairing_of_sandwich


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : StSandwich → StPairing := by
  first | exact @GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | exact GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich | (intros; apply GlobalTheory.CompanionTheory.HermLat.pairing_of_sandwich <;> assumption)
end _root_.GlobalTheory.T
