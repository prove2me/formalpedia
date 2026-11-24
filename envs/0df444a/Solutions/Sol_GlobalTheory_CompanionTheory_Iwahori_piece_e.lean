-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.piece_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:13:56.041808+00:00
-- url     : https://prove2.me/submissions/b5a6fb32-cbb6-4f2d-bf6d-2b8d5975eacc

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_e
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_e

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
    piece hh δ e f i (e j) = if i = some (Sum.inl j) then e j else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_e hh hδ hF, projF_e hh hF]
  · by_cases hij : j = i
    · subst hij; simp [piece, projE_e hh hδ hF]
    · simp [piece, projE_e hh hδ hF, hij, Ne.symm hij]
  · simp [piece, projF_e hh hF]
end GlobalTheory.CompanionTheory.Iwahori
