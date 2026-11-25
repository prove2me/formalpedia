-- Prove2me | solution 1 for GlobalTheory.T.TorusStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:33.439082+00:00
-- url     : https://prove2.me/submissions/80ed04ad-e0a3-44bb-b45f-14d38669c921

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FrameTorus_stTor


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
theorem _root_.solution : StTor := by
  first | exact @GlobalTheory.CompanionTheory.FrameTorus.stTor | exact GlobalTheory.CompanionTheory.FrameTorus.stTor | (intros; apply GlobalTheory.CompanionTheory.FrameTorus.stTor <;> assumption)
end _root_.GlobalTheory.T
