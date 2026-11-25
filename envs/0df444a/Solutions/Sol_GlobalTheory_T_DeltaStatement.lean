-- Prove2me | solution 1 for GlobalTheory.T.DeltaStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T18:11:23.829746+00:00
-- url     : https://prove2.me/submissions/70892513-845f-421b-bd46-784e0f707a2b

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DeltaStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DeltaStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_stDelta


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
theorem _root_.solution : StDelta := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stDelta | exact GlobalTheory.CompanionTheory.RgFl.stDelta | (intros; apply GlobalTheory.CompanionTheory.RgFl.stDelta <;> assumption)
end _root_.GlobalTheory.T
