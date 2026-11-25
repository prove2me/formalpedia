-- Prove2me | solution 1 for GlobalTheory.T.WittStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:35.615946+00:00
-- url     : https://prove2.me/submissions/c1a44691-beff-4113-b6f1-8e3600497418

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_WittStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlWitt_stWitt


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
theorem _root_.solution : StWitt := by
  first | exact @GlobalTheory.CompanionTheory.FlWitt.stWitt | exact GlobalTheory.CompanionTheory.FlWitt.stWitt | (intros; apply GlobalTheory.CompanionTheory.FlWitt.stWitt <;> assumption)
end _root_.GlobalTheory.T
