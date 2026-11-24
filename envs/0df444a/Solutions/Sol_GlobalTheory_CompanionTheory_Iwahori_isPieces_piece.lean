-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.isPieces_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:29.772915+00:00
-- url     : https://prove2.me/submissions/c8dbc676-2b71-4e2d-969b-ada3b1327ac8

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_e
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_f
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_w
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_end_ext

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
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) :
    IsPieces (piece hh δ e f) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw, LinearMap.zero_apply]
      split_ifs with h1 h2 <;> simp_all [piece_w hh hF _ hw]
  · intro i
    refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, piece_e hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_e hh hδ hF]
    · simp only [Module.End.mul_apply, piece_f hh hδ hF]
      split_ifs with h1 <;> simp_all [piece_f hh hδ hF]
    · simp only [Module.End.mul_apply, piece_w hh hF _ hw]
      split_ifs with h1 <;> simp_all [piece_w hh hF _ hw]
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp [LinearMap.sum_apply, piece_e hh hδ hF]
    · simp [LinearMap.sum_apply, piece_f hh hδ hF]
    · simp [LinearMap.sum_apply, piece_w hh hF _ hw]
end GlobalTheory.CompanionTheory.Iwahori
