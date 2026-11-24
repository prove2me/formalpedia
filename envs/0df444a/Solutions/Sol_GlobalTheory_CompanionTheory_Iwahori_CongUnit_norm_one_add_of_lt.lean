-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.CongUnit.norm_one_add_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:39:23.644395+00:00
-- url     : https://prove2.me/submissions/1270a8a4-558c-4d1a-b9dd-8d975b0c1cdd

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CongruenceEndomorphismInverseExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori GlobalTheory.CompanionTheory.Iwahori.CongUnit
variable {L V : Type} [NontriviallyNormedField L] [IsUltrametricDist L] [AddCommGroup V]
  [Module L V]
namespace GlobalTheory.CompanionTheory.Iwahori.CongUnit
theorem _root_.solution {t : L} (ht : ‖t‖ < 1) : ‖1 + t‖ = 1 := by
  have hne : ‖(1 : L)‖ ≠ ‖t‖ := by rw [norm_one]; exact ht.ne'
  rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, norm_one]
  exact max_eq_left ht.le
end GlobalTheory.CompanionTheory.Iwahori.CongUnit
