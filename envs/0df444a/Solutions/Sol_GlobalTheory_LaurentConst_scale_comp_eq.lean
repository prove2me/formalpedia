-- Prove2me | solution 1 for GlobalTheory.LaurentConst.scale_comp_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:29:24.027274+00:00
-- url     : https://prove2.me/submissions/8a064607-4919-44cf-a545-14747ae74f75

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Theorems.Thm_GlobalTheory_LaurentConst_atZero_const
import Theorems.Thm_GlobalTheory_LaurentConst_atInf_const
import Theorems.Thm_GlobalTheory_LaurentConst_scaleP_C
import Theorems.Thm_GlobalTheory_LaurentConst_scaleL_coe
import Theorems.Thm_GlobalTheory_LaurentConst_scale_single_zero
import Theorems.Thm_GlobalTheory_LaurentConst_atZero_scale
import Theorems.Thm_GlobalTheory_LaurentConst_atInf_scale
import Theorems.Thm_GlobalTheory_LaurentConst_constantCoeff_scaleP
import Theorems.Thm_GlobalTheory_LaurentConst_comp_scale
import Theorems.Thm_GlobalTheory_LaurentConst_comp_scaleP
import Theorems.Thm_GlobalTheory_LaurentConst_comp_quot
import Theorems.Thm_GlobalTheory_LaurentConst_quot_eq_iff
import Theorems.Thm_GlobalTheory_LaurentConst_quot_congr
import Theorems.Thm_GlobalTheory_LaurentConst_quot_apply
import Theorems.Thm_GlobalTheory_LaurentConst_eq_const_of_affine
import Theorems.Thm_GlobalTheory_LaurentConst_exists_extension
import Theorems.Thm_GlobalTheory_LaurentConst_specMap_comp
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
theorem _root_.solution [UniversallyClosed B.hom] {L R : Type} [Field L] [CommRing R]
    (s : Spec (.of L) ⟶ S) (f : Spec (.of (AddMonoidAlgebra L ℤ)) ⟶ B.left)
    (hf : f ≫ B.hom = Spec.map (CommRingCat.ofHom (algebraMap L _)) ≫ s)
    (r : L →+* R) (t : Rˣ) (ht : IsNilpotent ((t : R) - 1)) :
    Spec.map (CommRingCat.ofHom (scale r t)) ≫ f = Spec.map (CommRingCat.ofHom (scale r 1)) ≫ f := by
  have ht' : IsNilpotent (((t⁻¹ : Rˣ) : R) - 1) := by
    have : ((t⁻¹ : Rˣ) : R) - 1 = -(t⁻¹ : Rˣ) * ((t : R) - 1) := by
      rw [mul_sub, neg_mul, Units.inv_mul]; ring
    rw [this]
    exact (Commute.all _ _).isNilpotent_mul_left ht
  obtain ⟨f₀, e₀, p₀⟩ := exists_extension B.hom s (Spec.map (CommRingCat.ofHom (atZero L)) ≫ f) (by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ atZero_const c)
  obtain ⟨f₁, e₁, p₁⟩ := exists_extension B.hom s (Spec.map (CommRingCat.ofHom (atInf L)) ≫ f) (by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ atInf_const c)
  have hs : ∀ u : Rˣ, (Spec.map (CommRingCat.ofHom (scale r u)) ≫ f) ≫ B.hom =
      Spec.map (CommRingCat.ofHom ((algebraMap R _).comp r)) ≫ s := fun u ↦ by
    rw [Category.assoc, hf, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ scale_single_zero r u c
  have hP : ∀ (u : Rˣ) (y : Spec (.of (PowerSeries L)) ⟶ B.left),
      y ≫ B.hom = Spec.map (CommRingCat.ofHom PowerSeries.C) ≫ s →
      (Spec.map (CommRingCat.ofHom (scaleP r u)) ≫ y) ≫ B.hom =
        Spec.map (CommRingCat.ofHom (PowerSeries.C.comp r)) ≫ s := fun u y hy ↦ by
    rw [Category.assoc, hy, specMap_comp]
    congr 3
    exact RingHom.ext fun c ↦ scaleP_C r u c
  have hL : ∀ u : Rˣ, (HahnSeries.ofPowerSeries ℤ R).comp (scaleP r u) =
      (scaleL r u).comp (HahnSeries.ofPowerSeries ℤ L) :=
    fun u ↦ RingHom.ext fun p ↦ (scaleL_coe r u p).symm
  let e : Spec (.of L) ⟶ B.left := s ≫ (η[B] : 𝟙_ (Over S) ⟶ B).left
  obtain ⟨_, ⟨U, hU, rfl⟩, hx, -⟩ := B.left.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (e default)) isOpen_univ
  have hin : ∀ {D A : Type} [CommRing D] [CommRing A] (y : Spec (.of D) ⟶ B.left)
      (α β : D →+* A) (h) (c : L →+* A), (∀ (C : Type) [CommRing C] [IsReduced C] (ρ : A →+* C),
      ρ.comp α = ρ.comp β) → (Spec.map (CommRingCat.ofHom α) ≫ y) ≫ B.hom =
        Spec.map (CommRingCat.ofHom c) ≫ s →
      Set.range (quot (Spec.map (CommRingCat.ofHom α) ≫ y)
        (Spec.map (CommRingCat.ofHom β) ≫ y) h) ⊆ U := by
    rintro D A _ _ y α β h c H hc _ ⟨z, rfl⟩
    rw [quot_apply y α β h H, ← Category.assoc, hc, Category.assoc, Scheme.Hom.comp_apply,
      Subsingleton.elim (Spec.map (CommRingCat.ofHom c) z) default]
    exact hx
  have key := eq_const_of_affine hU
    (quot _ _ ((hs 1).trans (hs t).symm)) (quot _ _ ((hP 1 f₀ p₀).trans (hP t f₀ p₀).symm))
    (quot _ _ ((hP 1 f₁ p₁).trans (hP t⁻¹ f₁ p₁).symm))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scale r ht ρ) (hs t))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scaleP r ht ρ) (hP t f₀ p₀))
    (hin _ _ _ _ _ (fun _ _ _ ρ ↦ comp_scaleP r ht' ρ) (hP t⁻¹ f₁ p₁))
    (by
      rw [comp_quot, comp_quot]
      refine quot_congr _ _ ?_ ?_ <;>
        rw [specMap_comp, specMap_comp, atZero_scale, hL, ← specMap_comp, ← specMap_comp, e₀])
    (by
      rw [comp_quot, comp_quot]
      refine quot_congr _ _ ?_ ?_
      · rw [specMap_comp, specMap_comp, atInf_scale, hL, ← specMap_comp, ← specMap_comp, e₁]
      · rw [specMap_comp, specMap_comp, atInf_scale, hL, inv_one, ← specMap_comp, ← specMap_comp,
          e₁])
  rw [comp_quot _ _ _ ((hP 1 f₀ p₀).trans (hP t f₀ p₀).symm), (quot_eq_iff
    (_ ≫ Spec.map (CommRingCat.ofHom (scaleP r t)) ≫ f₀) _ _).2 (by
    rw [specMap_comp, specMap_comp, constantCoeff_scaleP, constantCoeff_scaleP])] at key
  refine (quot_eq_iff _ _ ((hs 1).trans (hs t).symm)).1 (key.trans ?_)
  simp only [Category.assoc]
  rw [reassoc_of% (hs t), reassoc_of% (hP t f₀ p₀), specMap_comp, specMap_comp]
  congr 3
end GlobalTheory.LaurentConst
