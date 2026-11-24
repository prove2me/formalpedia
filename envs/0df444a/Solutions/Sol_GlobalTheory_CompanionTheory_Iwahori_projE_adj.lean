-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.projE_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:51:06.357168+00:00
-- url     : https://prove2.me/submissions/5686af87-030e-4501-8a87-f94e90d110d6

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projE_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_projF_apply
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_smul_left

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
theorem _root_.solution (hs : IsInv s) (hh : IsHerm s h) (i : Fin l) (x y : V) :
    h (projE hh δ e f i x) y = h x (projF hh δ e f i y) := by
  rw [projE_apply, projF_apply, h_smul_left hh, hh.2.1, map_mul, map_inv₀, hs.1, ← hh.2.2.1 (f i) x]
  ring
end GlobalTheory.CompanionTheory.Iwahori
