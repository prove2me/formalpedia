-- Prove2me | solution 1 for GlobalTheory.T.simple_of_commutative_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:24:09.725957+00:00
-- url     : https://prove2.me/submissions/4d0c502d-bed5-40e2-9ac0-575177399d1d

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SimpleOfCommutativeStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SimpleOfCommutativeStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_stSimple_of_stComm


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
theorem _root_.solution : StComm → StSimple := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | exact GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm | (intros; apply GlobalTheory.CompanionTheory.RgFl.stSimple_of_stComm <;> assumption)
end _root_.GlobalTheory.T
