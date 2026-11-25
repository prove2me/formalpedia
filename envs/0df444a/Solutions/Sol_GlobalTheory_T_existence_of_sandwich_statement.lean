-- Prove2me | solution 1 for GlobalTheory.T.existence_of_sandwich_statement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:16:43.989006+00:00
-- url     : https://prove2.me/submissions/01b678b9-0155-4d79-af4c-22d8d5d30d7a

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_ExistenceOfSandwichStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_MaxLat_stExists_of_stSandwich


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
theorem _root_.solution : StSandwich → StExists := by
  first | exact @GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | exact GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich | (intros; apply GlobalTheory.CompanionTheory.RgFl.MaxLat.stExists_of_stSandwich <;> assumption)
end _root_.GlobalTheory.T
