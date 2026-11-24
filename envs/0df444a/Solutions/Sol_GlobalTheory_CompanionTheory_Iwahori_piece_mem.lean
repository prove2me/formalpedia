-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.piece_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:29:30.675509+00:00
-- url     : https://prove2.me/submissions/8862486e-d117-478e-9a43-122968857c04

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_e
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_f
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_w
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_lat_smul
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_e_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_f_mem

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
theorem _root_.solution {Λ : AddSubgroup V} (hΛ : IsLat L Λ) (hA : IsAdapted h e f W (fun _ => 1) Λ)
    (hh : IsHerm s h) (hδ : δ ≠ 0) (hF : IsFrame h δ e f W) (i : Idx l) {x : V} (hx : x ∈ Λ) :
    piece hh δ e f i x ∈ Λ := by
  obtain ⟨a, b, w, hw, rfl⟩ := hF.2.2.2.2.2 x
  obtain ⟨ha, hb, hww⟩ := (hA a b w hw).1 hx
  rcases i with _ | i | i
  · have : piece hh δ e f none (∑ i, a i • e i + ∑ i, b i • f i + w) = w := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    have := (hA 0 0 w hw).2 ⟨fun i => by simp, fun i => by simp, hww⟩
    simpa using this
  · have : piece hh δ e f (some (Sum.inl i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = a i • e i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using ha i) (e_mem hA hh i)
  · have : piece hh δ e f (some (Sum.inr i)) (∑ i, a i • e i + ∑ i, b i • f i + w) = b i • f i := by
      simp [map_add, map_sum, piece_e hh hδ hF, piece_f hh hδ hF, piece_w hh hF _ hw]
    rw [this]
    exact lat_smul hΛ (by simpa using hb i) (f_mem hA hh i)
end GlobalTheory.CompanionTheory.Iwahori
