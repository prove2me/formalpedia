-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.h_sub_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:35.123906+00:00
-- url     : https://prove2.me/submissions/fd6175c3-1c4d-4eb3-bedd-d8f4f0418e8b

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_sub_right

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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Iwahori
variable {L V : Type} [NontriviallyNormedField L] [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L} {δ : L} {l : ℕ} {e f : Fin l → V} {W : Submodule L V}
namespace GlobalTheory.CompanionTheory.Iwahori
theorem _root_.solution (hh : IsHerm s h) (x x' y : V) : h (x - x') y = h x y - h x' y := by
  rw [hh.2.2.1 y (x - x'), h_sub_right hh, map_sub, ← hh.2.2.1 y x, ← hh.2.2.1 y x']
end GlobalTheory.CompanionTheory.Iwahori
