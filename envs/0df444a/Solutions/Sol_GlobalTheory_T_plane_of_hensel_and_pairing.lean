-- Prove2me | solution 1 for GlobalTheory.T.plane_of_hensel_and_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:33:22.66751+00:00
-- url     : https://prove2.me/submissions/6edea401-4c72-4f67-ab96-0d9fd1272946

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairing
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PlaneOfHenselAndPairingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermPlane_stPlane_of_hensel_pairing


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
theorem _root_.solution : StHensel → StPairing → StPlane := by
  first | exact @GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | exact GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing | (intros; apply GlobalTheory.CompanionTheory.HermPlane.stPlane_of_hensel_pairing <;> assumption)
end _root_.GlobalTheory.T
