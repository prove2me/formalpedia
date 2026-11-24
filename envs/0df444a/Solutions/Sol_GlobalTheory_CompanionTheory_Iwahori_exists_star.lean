-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Iwahori.exists_star
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:38:45.166723+00:00
-- url     : https://prove2.me/submissions/b24b0182-4383-4c34-95b8-08303a9d3968

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_StSandwich
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsCongIdealTwoTorsion
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_IsPiecesPiece
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_zero_right
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_eq_of_pair
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_h_zero_left
import Theorems.Thm_GlobalTheory_CompanionTheory_Iwahori_piece_adj

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
theorem _root_.solution (hs : IsInv s) (hh : IsHerm s h)
    (hadj : ∀ g : Module.End L V, ∃ g' : Module.End L V, ∀ x y, h (g x) y = h x (g' y)) :
    ∃ st : Module.End L V → Module.End L V, (∀ g x y, h (g x) y = h x (st g y)) ∧
      (∀ a b, st (a * b) = st b * st a) ∧ st 1 = 1 ∧ st 0 = 0 ∧
      ∀ i : Idx l, st (piece hh δ e f i) = piece hh δ e f (rev i) := by
  choose st hst using hadj
  refine ⟨st, hst, fun a b => ?_, ?_, ?_, fun i => ?_⟩
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, Module.End.mul_apply, Module.End.mul_apply, ← hst, ← hst]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; rfl
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst]; simp [h_zero_left hh, h_zero_right hh]
  · ext y
    refine eq_of_pair hh fun x => ?_
    rw [← hst, piece_adj hs hh]
end GlobalTheory.CompanionTheory.Iwahori
