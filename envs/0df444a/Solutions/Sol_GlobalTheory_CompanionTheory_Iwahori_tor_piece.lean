-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.tor_piece
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:31.439722+00:00
-- url     : https://prove2.me/submissions/bbd6ada6-fcc0-4556-af61-771aecd5c277

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
theorem _root_.solution (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) {u : Fin l → L}
    {t : V ≃ₗ[L] V} (ht : IsTor s e f W u t) (i : Idx l) :
    (t.toLinearMap : Module.End L V) * piece hh δ e f i = tau s u i • piece hh δ e f i ∧
      piece hh δ e f i * (t.toLinearMap : Module.End L V) = tau s u i • piece hh δ e f i := by
  obtain ⟨t1, t2, t3⟩ := ht
  constructor
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_e hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t1]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_f hh hδ hF, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t2]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, piece_w hh hF _ hw, LinearEquiv.coe_coe]
      split_ifs with h1
      · subst h1; simp [tau, t3 w hw]
      · simp
  · refine end_ext hF (fun m => ?_) (fun m => ?_) (fun w hw => ?_)
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t1, map_smul,
        piece_e hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t2, map_smul,
        piece_f hh hδ hF]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
    · simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, t3 w hw,
        piece_w hh hF _ hw]
      split_ifs with h1
      · subst h1; simp [tau]
      · simp
end GlobalTheory.CompanionTheory.Iwahori
