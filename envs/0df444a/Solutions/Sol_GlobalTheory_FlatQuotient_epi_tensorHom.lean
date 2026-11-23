-- Prove2me | solution 1 for GlobalTheory.FlatQuotient.epi_tensorHom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:33.48945+00:00
-- url     : https://prove2.me/submissions/2950475f-e1cd-41ea-8980-efee1e02b068

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
import Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory
namespace FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerRight_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (f : X ⟶ Y) (Z : Over S) (hf : P f.left) :
    P (f ▷ Z).left := by
  have e1 : (f ▷ Z).left ≫ pullback.snd Y.hom Z.hom = pullback.snd X.hom Z.hom := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have e2 : (f ▷ Z).left ≫ pullback.fst Y.hom Z.hom = pullback.fst X.hom Z.hom ≫ f.left := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have houter : IsPullback ((f ▷ Z).left ≫ pullback.snd Y.hom Z.hom) (pullback.fst X.hom Z.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact (IsPullback.of_hasPullback X.hom Z.hom).flip
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Y.hom Z.hom).flip).flip hf
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry in
open scoped CategoryTheory.Obj in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
private lemma whiskerLeft_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (Z : Over S) (f : X ⟶ Y) (hf : P f.left) :
    P (Z ◁ f).left := by
  have e1 : (Z ◁ f).left ≫ pullback.fst Z.hom Y.hom = pullback.fst Z.hom X.hom := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have e2 : (Z ◁ f).left ≫ pullback.snd Z.hom Y.hom = pullback.snd Z.hom X.hom ≫ f.left := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have houter : IsPullback ((Z ◁ f).left ≫ pullback.fst Z.hom Y.hom) (pullback.snd Z.hom X.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact IsPullback.of_hasPullback Z.hom X.hom
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Z.hom Y.hom)).flip hf
end FlatQuotient
end GlobalTheory
end

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}
namespace GlobalTheory.FlatQuotient
namespace _root_.GlobalTheory.FlatQuotient
theorem _root_.solution {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hf' : Surjective f.left] [hg : Flat g.left] [hg' : Surjective g.left] :
    Epi (f ⊗ₘ g) := by
  have h₁ : Flat (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Flat f X' hf
  have h₂ : Surjective (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Surjective f X' hf'
  have h₃ : Flat (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Flat Y g hg
  have h₄ : Surjective (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Surjective Y g hg'
  have e₁ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (f ▷ X')
  have e₂ := _root_.GlobalTheory.FlatQuotient.epi_of_flat_surjective (Y ◁ g)
  rw [MonoidalCategory.tensorHom_def]
  exact epi_comp _ _
end _root_.GlobalTheory.FlatQuotient
end GlobalTheory.FlatQuotient
