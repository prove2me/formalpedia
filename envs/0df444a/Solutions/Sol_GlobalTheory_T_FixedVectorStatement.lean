-- Prove2me | solution 1 for GlobalTheory.T.FixedVectorStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T18:16:15.332831+00:00
-- url     : https://prove2.me/submissions/7cd41602-2fe3-495d-8d7b-5b2c0fd5a291

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FixedVectorStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_FixedVectorStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_stFixVec


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
theorem _root_.solution : StFixVec := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stFixVec | exact GlobalTheory.CompanionTheory.RgFl.stFixVec | (intros; apply GlobalTheory.CompanionTheory.RgFl.stFixVec <;> assumption)
end _root_.GlobalTheory.T
