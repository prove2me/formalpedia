-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.projE_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:56:31.313936+00:00
-- url     : https://prove2.me/submissions/197ec284-9367-4e75-9016-9ae6f8f2a0c9

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_s_ne
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_f_e

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
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i j : Fin l) :
    projE hh δ e f i (e j) = if j = i then e i else 0 := by
  rw [projE_apply, h_f_e hh hF]
  split_ifs
  · simp [s_ne hδ]
  · simp
end GlobalTheory.CompanionTheory.Iwahori
