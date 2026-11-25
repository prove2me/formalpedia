-- Prove2me | solution 1 for GlobalTheory.T.PairingStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:09.184691+00:00
-- url     : https://prove2.me/submissions/4fa15812-0ad5-43b8-af57-2f91f9cabe1b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckePair_stPair


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : StPair := by
  first | exact @GlobalTheory.CompanionTheory.HeckePair.stPair | exact GlobalTheory.CompanionTheory.HeckePair.stPair | (intros; apply GlobalTheory.CompanionTheory.HeckePair.stPair <;> assumption)
end _root_.GlobalTheory.T
