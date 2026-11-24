-- Prove2me | solution 1 for GlobalTheory.SmoothDescent.exists_fg_subset_range_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:16:03.426355+00:00
-- url     : https://prove2.me/submissions/0e7406c9-ff8f-4f41-ba0a-5d51a3f716b2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Theorems.Thm_GlobalTheory_SmoothDescent_range_incl_mono
import Theorems.Thm_GlobalTheory_SmoothDescent_exists_fg_mem_range_incl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SmoothDescent
open TensorProduct
variable {A R B₁ C₁ : Type} [CommRing A] [CommRing R] [CommRing B₁] [CommRing C₁] [Algebra A R]
  [Algebra A B₁] [Algebra A C₁]
namespace GlobalTheory.SmoothDescent
theorem _root_.solution (t : Finset (R ⊗[A] C₁)) :
    ∃ S : Subalgebra A R, S.FG ∧ (t : Set (R ⊗[A] C₁)) ⊆ (incl C₁ S).range := by
  classical
  refine Finset.induction_on t ⟨⊥, Subalgebra.fg_bot, by simp⟩ ?_
  intro a t _ ih
  obtain ⟨S, hS, hSt⟩ := ih
  obtain ⟨T, hT, haT⟩ := exists_fg_mem_range_incl (C₁ := C₁) a
  refine ⟨S ⊔ T, hS.sup hT, ?_⟩
  rw [Finset.coe_insert, Set.insert_subset_iff]
  exact ⟨range_incl_mono le_sup_right haT,
    hSt.trans (SetLike.coe_subset_coe.mpr (range_incl_mono le_sup_left))⟩
end GlobalTheory.SmoothDescent
