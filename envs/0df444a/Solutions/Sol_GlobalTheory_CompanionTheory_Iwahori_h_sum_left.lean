-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.h_sum_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:48:36.06219+00:00
-- url     : https://prove2.me/submissions/fceff0df-2464-432a-a3cd-1af425ddece2

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_zero_left

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
theorem _root_.solution (hh : IsHerm s h) {ι : Type} (A : Finset ι) (v : ι → V) (y : V) :
    h (∑ m ∈ A, v m) y = ∑ m ∈ A, h (v m) y :=
  map_sum (⟨⟨fun x => h x y, h_zero_left hh y⟩, fun x x' => h_add_left hh x x' y⟩ : V →+ L) v A
end GlobalTheory.CompanionTheory.Iwahori
