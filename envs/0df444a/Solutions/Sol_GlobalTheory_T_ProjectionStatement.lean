-- Prove2me | solution 1 for GlobalTheory.T.ProjectionStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:12.966979+00:00
-- url     : https://prove2.me/submissions/2a792f0d-b5dc-4cdd-97f5-27c31a26ed1f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ProjectionStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ProjectionStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_FixedProj_stProj


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
theorem _root_.solution : StProj := by
  first | exact @GlobalTheory.CompanionTheory.FixedProj.stProj | exact GlobalTheory.CompanionTheory.FixedProj.stProj | (intros; apply GlobalTheory.CompanionTheory.FixedProj.stProj <;> assumption)
end _root_.GlobalTheory.T
