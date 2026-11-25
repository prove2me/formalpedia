-- Prove2me | solution 1 for GlobalTheory.T.CartanDecompositionGL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:01.926538+00:00
-- url     : https://prove2.me/submissions/0df6a1c0-1059-49ca-ad6b-012ca3018cb9

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGL
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CartanDecompositionGLStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_CartGL_stCartanGL


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
theorem _root_.solution : StCartanGL := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.stCartanGL | exact GlobalTheory.CompanionTheory.CartGL.stCartanGL | (intros; apply GlobalTheory.CompanionTheory.CartGL.stCartanGL <;> assumption)
end _root_.GlobalTheory.T
