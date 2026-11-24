-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.piece_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:08:18.103814+00:00
-- url     : https://prove2.me/submissions/1c9fcc53-18ea-4f37-a2c0-6a4f73098c31

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_hLin_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_sub_right
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_add_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_sum_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_sub_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_adj
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_adj

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
theorem _root_.solution (hs : IsInv s) (hh : IsHerm s h) (i : Idx l) (x y : V) :
    h (piece hh δ e f i x) y = h x (piece hh δ e f (rev i) y) := by
  rcases i with _ | i | i
  · have hx := map_sum (hLin hh x) (fun m => projE hh δ e f m y + projF hh δ e f m y) Finset.univ
    simp only [hLin_apply] at hx
    simp only [piece, rev, LinearMap.sub_apply, Module.End.one_apply, LinearMap.sum_apply,
      LinearMap.add_apply, h_sub_left hh, h_sub_right hh, h_sum_left hh, hx, h_add_left hh, hh.1,
      projE_adj hs hh, projF_adj hs hh]
    congr 1
    exact Finset.sum_congr rfl fun m _ => add_comm _ _
  · exact projE_adj hs hh i x y
  · exact projF_adj hs hh i x y
end GlobalTheory.CompanionTheory.Iwahori
