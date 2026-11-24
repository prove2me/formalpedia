-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.FrameTorus.add_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:36:03.680043+00:00
-- url     : https://prove2.me/submissions/44126142-a22e-4881-add1-d190a335581e

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TorusStatement

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrameTorus
variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
namespace GlobalTheory.CompanionTheory.FrameTorus
theorem _root_.solution {s : L →+* L} {h : V → V → L} (hH : IsHerm s h) (x x' y : V) :
    h (x + x') y = h x y + h x' y := by
  rw [hH.2.2.1 y (x + x'), hH.1, map_add, ← hH.2.2.1, ← hH.2.2.1]
end GlobalTheory.CompanionTheory.FrameTorus
