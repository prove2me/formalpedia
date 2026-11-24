-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.herm_add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:17.463517+00:00
-- url     : https://prove2.me/submissions/dab43dce-a839-4b02-88a9-669a54ec9a00

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PairingOfSandwichStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HermLat
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}
namespace GlobalTheory.CompanionTheory.HermLat
theorem _root_.solution (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  rw [hh.2.2.1 z (x + y), hh.1, map_add, ← hh.2.2.1, ← hh.2.2.1]
end GlobalTheory.CompanionTheory.HermLat
