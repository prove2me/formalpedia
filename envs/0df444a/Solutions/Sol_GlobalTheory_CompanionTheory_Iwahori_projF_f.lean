-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.projF_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:47.106417+00:00
-- url     : https://prove2.me/submissions/3937d865-4c7e-4263-a8b3-4eec90c15b30

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_apply

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
    projF hh δ e f i (f j) = if j = i then f i else 0 := by
  rw [projF_apply, hF.2.2.1 i j]
  by_cases hij : j = i
  · subst hij; simp [hδ]
  · simp [hij, Ne.symm hij]
end GlobalTheory.CompanionTheory.Iwahori
