-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.q_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:54:06.482797+00:00
-- url     : https://prove2.me/submissions/99f7692d-9c97-4c8f-a559-383bea870def

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich
import Theorems.Thm_GlobalTheory_CompanionTheory_HermAniso_add_left

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.FlB
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermAniso
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermAniso
theorem _root_.solution (hh : IsHerm s h) (x y : V) :
    h (x + y) (x + y) = h x x + h y y + (h x y + h y x) := by
  rw [add_left hh, hh.1, hh.1]; ring
end GlobalTheory.CompanionTheory.HermAniso
