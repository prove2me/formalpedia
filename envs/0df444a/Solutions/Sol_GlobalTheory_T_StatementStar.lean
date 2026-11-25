-- Prove2me | solution 1 for GlobalTheory.T.StatementStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:29.134641+00:00
-- url     : https://prove2.me/submissions/dace4ebc-da3c-4d32-913d-b33e01e7ba61

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStarStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_stStar


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
theorem _root_.solution : StStar := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | exact GlobalTheory.CompanionTheory.RgFl.StarPf.stStar | (intros; apply GlobalTheory.CompanionTheory.RgFl.StarPf.stStar <;> assumption)
end _root_.GlobalTheory.T
