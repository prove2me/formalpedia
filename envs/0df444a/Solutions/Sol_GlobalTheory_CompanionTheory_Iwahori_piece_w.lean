-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.piece_w
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:58:58.663559+00:00
-- url     : https://prove2.me/submissions/5e0c7578-3d27-45a8-a4b0-64eef83f54d7

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_w
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_w

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
theorem _root_.solution (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i : Idx l) {w : V} (hw : w ∈ W) :
    piece hh δ e f i w = if i = none then w else 0 := by
  rcases i with _ | i | i
  · simp [piece, LinearMap.sum_apply, projE_w hh hF _ hw, projF_w hh hF _ hw]
  · simp [piece, projE_w hh hF _ hw]
  · simp [piece, projF_w hh hF _ hw]
end GlobalTheory.CompanionTheory.Iwahori
