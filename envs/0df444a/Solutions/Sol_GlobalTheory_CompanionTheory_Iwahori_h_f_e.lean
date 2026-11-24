-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.h_f_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:41:00.216315+00:00
-- url     : https://prove2.me/submissions/9bdc5cf0-5620-4d5a-b893-ce081b54c3ed

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece

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
theorem _root_.solution (hh : IsHerm s h) (hF : IsFrame h δ e f W) (i j : Fin l) :
    h (f i) (e j) = if j = i then s δ else 0 := by
  rw [hh.2.2.1 (e j) (f i), hF.2.2.1 j i]
  split_ifs <;> simp
end GlobalTheory.CompanionTheory.Iwahori
