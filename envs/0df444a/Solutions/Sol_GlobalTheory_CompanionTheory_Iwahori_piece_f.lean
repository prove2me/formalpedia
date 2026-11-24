-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.piece_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:02:34.27449+00:00
-- url     : https://prove2.me/submissions/9ec066e5-ab6e-4e47-95f6-1d48227e3f11

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_f
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_f

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
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) (j : Fin l) :
    piece hh δ e f i (f j) = if i = some (Sum.inr j) then f j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_f hh hF, projF_f hh hδ hF]
  · simp [piece, projE_f hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projF_f hh hδ hF]
    · simp [piece, projF_f hh hδ hF, hij, Ne.symm hij]
end GlobalTheory.CompanionTheory.Iwahori
