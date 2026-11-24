-- Prove2me | solution 1 for GlobalTheory.LaurentConst.quot_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:44.53008+00:00
-- url     : https://prove2.me/submissions/bdf1d3bb-c23b-43fb-a65f-95aeff354b95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_comp_quot
import Theorems.Thm_GlobalTheory_LaurentConst_quot_eq_iff
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open GlobalTheory GlobalTheory.LaurentConst
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}} {B : Over S} [GrpObj B] {W Z : Scheme.{0}}
namespace GlobalTheory.LaurentConst
theorem _root_.solution {D A : Type} [CommRing D] [CommRing A] (f : Spec (.of D) ⟶ B.left)
    (α β : D →+* A) (h) (H : ∀ (C : Type) [CommRing C] [IsReduced C] (ρ : A →+* C),
      ρ.comp α = ρ.comp β) (z : Spec (.of A)) :
    quot (Spec.map (CommRingCat.ofHom α) ≫ f) (Spec.map (CommRingCat.ofHom β) ≫ f) h z =
      ((Spec.map (CommRingCat.ofHom α) ≫ f) ≫ B.hom ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left) z := by
  have hz : z.asIdeal.IsPrime := z.isPrime
  let j : Spec (.of (A ⧸ z.asIdeal)) ⟶ Spec (.of A) :=
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk z.asIdeal))
  obtain ⟨w, hw⟩ : z ∈ Set.range j := ⟨(⊥ : PrimeSpectrum (A ⧸ z.asIdeal)), by
    apply PrimeSpectrum.ext
    exact Ideal.mk_ker⟩
  rw [← hw, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, comp_quot,
    (quot_eq_iff _ _ _).2, Category.assoc]
  simp only [j, ← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, H]
end GlobalTheory.LaurentConst
