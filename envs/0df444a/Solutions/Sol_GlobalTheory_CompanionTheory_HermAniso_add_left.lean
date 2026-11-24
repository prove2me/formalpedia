-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermAniso.add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:38:09.028883+00:00
-- url     : https://prove2.me/submissions/d26bbb54-4c89-4ed0-9455-6bcc9dd8af75

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_AnisotropicOfHenselAndSandwich

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
theorem _root_.solution (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  have h1 := hh.2.2.1
  rw [h1 z (x + y), hh.1, map_add, h1 z x, h1 z y]
end GlobalTheory.CompanionTheory.HermAniso
