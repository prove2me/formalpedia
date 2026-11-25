-- Prove2me | solution 1 for GlobalTheory.T.MovingStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:05.523416+00:00
-- url     : https://prove2.me/submissions/8fc08bd7-93cd-41ba-9493-b87100571ac5

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_MovingStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartanMove_stMove


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
theorem _root_.solution : StMove := by
  first | exact @GlobalTheory.CompanionTheory.CartanMove.stMove | exact GlobalTheory.CompanionTheory.CartanMove.stMove | (intros; apply GlobalTheory.CompanionTheory.CartanMove.stMove <;> assumption)
end _root_.GlobalTheory.T
