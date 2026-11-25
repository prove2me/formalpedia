-- Prove2me | solution 1 for GlobalTheory.T.decomposition_of_frame_witt_torus
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:43.869336+00:00
-- url     : https://prove2.me/submissions/296ceba0-9dd6-418a-9da9-46e345ebe477

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorus
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_DecompositionOfFrameWittTorusStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FlDecomp_stDecomp_of_frame_witt_tor


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
theorem _root_.solution : StFrame → StWitt → StTor → StDecomp := by
  first | exact @GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | exact GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor | (intros; apply GlobalTheory.CompanionTheory.FlDecomp.stDecomp_of_frame_witt_tor <;> assumption)
end _root_.GlobalTheory.T
