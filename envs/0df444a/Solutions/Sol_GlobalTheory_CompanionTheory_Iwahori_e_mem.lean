-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.e_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:39:31.153319+00:00
-- url     : https://prove2.me/submissions/dd02b6a1-d905-4d09-b0db-74a517637614

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_zero_right

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
theorem _root_.solution {Λ : AddSubgroup V} (hA : IsAdapted h e f W (fun _ => 1) Λ) (hh : IsHerm s h) (j : Fin l) :
    e j ∈ Λ := by
  have := (hA (Pi.single j 1) 0 0 W.zero_mem).2 ⟨fun i => by
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij], fun i => by simp, by simp [h_zero_right hh]⟩
  simpa [Pi.single_apply, ite_smul] using this
end GlobalTheory.CompanionTheory.Iwahori
