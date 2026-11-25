-- Prove2me | solution 1 for GlobalTheory.T.SandwichStatement
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T18:15:19.706928+00:00
-- url     : https://prove2.me/submissions/536678f1-4424-419d-9a5e-2da89a5f7cee

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SandwichStatement
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_SandwichStatementStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_Lattice_stSandwich


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
theorem _root_.solution : StSandwich := by
  first | exact @GlobalTheory.CompanionTheory.Lattice.stSandwich | exact GlobalTheory.CompanionTheory.Lattice.stSandwich | (intros; apply GlobalTheory.CompanionTheory.Lattice.stSandwich <;> assumption)
end _root_.GlobalTheory.T
