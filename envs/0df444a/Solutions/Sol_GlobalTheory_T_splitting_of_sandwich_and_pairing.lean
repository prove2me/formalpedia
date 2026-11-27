-- Prove2me | solution 1 for GlobalTheory.T.splitting_of_sandwich_and_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:16.145219+00:00
-- url     : https://prove2.me/submissions/a2e3ad75-c00a-47d9-91b0-fb8f8d76f8c4

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairing
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SplittingOfSandwichAndPairingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgSplit_stSplit


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
theorem _root_.solution : StSandwich → StPairing → StSplit := by
  first | exact @GlobalTheory.CompanionTheory.RgSplit.stSplit | exact GlobalTheory.CompanionTheory.RgSplit.stSplit | (intros; apply GlobalTheory.CompanionTheory.RgSplit.stSplit <;> assumption)
end _root_.GlobalTheory.T
