-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.tau_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:40:51.130798+00:00
-- url     : https://prove2.me/submissions/ca0f2830-41af-47e2-a59d-9d19e9195591

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
theorem _root_.solution (hs : IsInv s) {u : Fin l → L} (hu0 : ∀ i, u i ≠ 0) (hm : Monotone fun i => ‖u i‖)
    (h1 : ∀ i, ‖u i‖ ≤ 1) (i j : Idx l) (hij : wt i ≤ wt j) : ‖tau s u i‖ ≤ ‖tau s u j‖ := by
  have hinv : ∀ m, 1 ≤ ‖(s (u m))⁻¹‖ := fun m => by
    rw [norm_inv, hs.2.1]
    exact (one_le_inv₀ (norm_pos_iff.2 (hu0 m))).2 (h1 m)
  rcases i with _ | i | i <;> rcases j with _ | j | j <;> simp only [wt] at hij <;> simp only [tau]
  · simp
  · have := j.2; omega
  · simpa using hinv j
  · simpa using h1 i
  · have hij' : i ≤ j := by rw [Fin.le_def]; exact hij
    exact hm hij'
  · exact (h1 i).trans (hinv j)
  · have := i.2; omega
  · have := i.2; have := j.2; omega
  · rw [norm_inv, norm_inv, hs.2.1, hs.2.1]
    refine inv_anti₀ (norm_pos_iff.2 (hu0 j)) (hm ?_)
    have := i.2; have := j.2
    rw [Fin.le_def]; omega
end GlobalTheory.CompanionTheory.Iwahori
