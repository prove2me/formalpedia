-- Prove2me | solution 1 for GlobalTheory.T.anisotropic_of_hensel_and_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:12:18.593585+00:00
-- url     : https://prove2.me/submissions/ea71094c-051e-4602-9af6-e9208f0d0de6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwichStatement
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_aniso


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
theorem _root_.solution : StHensel → StSandwich → StAniso := by
  first | exact @GlobalTheory.CompanionTheory.HermAniso.aniso | exact GlobalTheory.CompanionTheory.HermAniso.aniso | (intros; apply GlobalTheory.CompanionTheory.HermAniso.aniso <;> assumption)
end _root_.GlobalTheory.T
