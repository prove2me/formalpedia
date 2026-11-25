-- Prove2me | solution 1 for GlobalTheory.T.IwahoriStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:15:48.967939+00:00
-- url     : https://prove2.me/submissions/6c286f22-f68e-4c06-874e-dd10d490404b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IwahoriStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_stIwahori


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
theorem _root_.solution : StIwahori := by
  first | exact @GlobalTheory.CompanionTheory.Iwahori.stIwahori | exact GlobalTheory.CompanionTheory.Iwahori.stIwahori | (intros; apply GlobalTheory.CompanionTheory.Iwahori.stIwahori <;> assumption)
end _root_.GlobalTheory.T
