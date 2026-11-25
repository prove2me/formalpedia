-- Prove2me | solution 1 for GlobalTheory.T.HenselStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:44.701321+00:00
-- url     : https://prove2.me/submissions/d4c5d0a9-b173-4e0c-85f3-3ed2b7d05a99

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HenselStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HenselStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_LocalHensel_stHensel_holds


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
theorem _root_.solution : StHensel := by
  first | exact @GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | exact GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds | (intros; apply GlobalTheory.CompanionTheory.LocalHensel.stHensel_holds <;> assumption)
end _root_.GlobalTheory.T
