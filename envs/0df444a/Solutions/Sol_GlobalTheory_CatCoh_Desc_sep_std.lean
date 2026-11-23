-- Prove2me | solution 1 for GlobalTheory.CatCoh.Desc.sep_std
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:20.923802+00:00
-- url     : https://prove2.me/submissions/97ddbde9-13b2-447a-a1d7-abea1abd62ab

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Theorems.Thm_GlobalTheory_CatCoh_Desc_IsSec_kill
import Theorems.Thm_GlobalTheory_CatCoh_Desc_exists_partition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory Filter
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc
universe v u w
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ CommAlgCat.{0} R)
variable {F} (H : HasLoc F) {T : C} {ι : Type} [Fintype ι] {b : ι → F.obj T}
  (hb : Ideal.span (Set.range b) = ⊤)
include H hb
namespace GlobalTheory.CatCoh.Desc
theorem _root_.solution : Sep F fun S (u : T ⟶ S) ↦ ∃ i, IsUnit (mp F u (b i)) := by
  intro x hx
  obtain ⟨M, hM⟩ := (eventually_all.2 fun l ↦ IsSec.kill H (P := fun _ _ ↦ True) (b := 1)
    (by simp) (b l) (s := fun S u ↦ mp F u x) (fun _ _ _ _ _ ↦ mp_comp F _ _ _)
    fun S u _ h ↦ hx S u ⟨l, h⟩).exists
  obtain ⟨r, hr⟩ := exists_partition hb M
  rw [← mp_id F T x, ← one_mul (mp F _ x), ← hr T (𝟙 T), Finset.sum_mul]
  exact Finset.sum_eq_zero fun l _ ↦ by rw [mul_assoc, hM l T _ trivial, mul_zero]
end GlobalTheory.CatCoh.Desc
