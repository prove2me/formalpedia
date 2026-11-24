-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.HermLat.herm_smul_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:38:18.295642+00:00
-- url     : https://prove2.me/submissions/7b551237-11bf-4a78-9ec3-d278205bd903

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
theorem _root_.solution (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  rw [hh.2.2.1 y (a • x), hh.2.1, map_mul, ← hh.2.2.1]
end GlobalTheory.CompanionTheory.HermLat
