-- Prove2me | solution 1 for GlobalTheory.T.ModularityStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:13:01.447444+00:00
-- url     : https://prove2.me/submissions/990dc40b-52b2-4c97-af3c-8ada390718a3

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ModularityStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCoinv_stMod


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
theorem _root_.solution : StMod := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCoinv.stMod | exact GlobalTheory.CompanionTheory.HeckeCoinv.stMod | (intros; apply GlobalTheory.CompanionTheory.HeckeCoinv.stMod <;> assumption)
end _root_.GlobalTheory.T
