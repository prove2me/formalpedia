-- Prove2me | solution 1 for GlobalTheory.T.StatementCommutative
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:24.604313+00:00
-- url     : https://prove2.me/submissions/73723d5c-f08c-4c0c-9e02-8680cc908450

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutative
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementCommutativeStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Bernstein_stComm


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
theorem _root_.solution : StComm := by
  first | exact @GlobalTheory.CompanionTheory.Bernstein.stComm | exact GlobalTheory.CompanionTheory.Bernstein.stComm | (intros; apply GlobalTheory.CompanionTheory.Bernstein.stComm <;> assumption)
end _root_.GlobalTheory.T
