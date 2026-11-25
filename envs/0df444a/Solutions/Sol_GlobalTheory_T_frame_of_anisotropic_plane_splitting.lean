-- Prove2me | solution 1 for GlobalTheory.T.frame_of_anisotropic_plane_splitting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:17:52.117458+00:00
-- url     : https://prove2.me/submissions/bdbaa719-1327-4abb-b97b-e92cb363111d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplitting
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FrameOfAnisotropicPlaneSplittingStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermFrame_stFrame_of


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
theorem _root_.solution : StAniso → StPlane → StSplit → StFrame := by
  first | exact @GlobalTheory.CompanionTheory.HermFrame.stFrame_of | exact GlobalTheory.CompanionTheory.HermFrame.stFrame_of | (intros; apply GlobalTheory.CompanionTheory.HermFrame.stFrame_of <;> assumption)
end _root_.GlobalTheory.T
