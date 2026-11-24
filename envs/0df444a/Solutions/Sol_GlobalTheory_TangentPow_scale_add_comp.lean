-- Prove2me | solution 1 for GlobalTheory.TangentPow.scale_add_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:56:52.864614+00:00
-- url     : https://prove2.me/submissions/f8bc27f6-2f6a-4580-8a8e-f9909fae561f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FormallyUnramifiedOfTangentMapInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_EqOneOfPowEqOneOfCompEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_PowEqScaleAndExistsUniqueTorsion
import Theorems.Thm_GlobalTheory_TangentPow_ofTwo_toTwo
import Theorems.Thm_GlobalTheory_TangentPow_scale_zero_comp
import Theorems.Thm_GlobalTheory_TangentCrit_hom_ext_of_ker_inf
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
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.TangentPow
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]
variable {G : Over (Spec (CommRingCat.of O))} [GrpObj G] {y : specO O (DualNumber R) ⟶ G}
namespace GlobalTheory.TangentPow
theorem _root_.solution (hy : ptMap (TrivSqZeroExt.fstHom O R R) ≫ y = 1) (a b : R) :
    scale O (a + b) ≫ y = (scale O a ≫ y) * (scale O b ≫ y) := by
  let i₁ := LinearMap.inl R R R
  let i₂ := LinearMap.inr R R R
  have key : toTwo O (i₁ + i₂) ≫ y = (toTwo O i₁ ≫ y) * (toTwo O i₂ ≫ y) := by
    ext1
    refine GlobalTheory.TangentCrit.hom_ext_of_ker_inf
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom)
      (CommRingCat.ofHom (TrivSqZeroExt.map (LinearMap.snd R R R)).toRingHom) ?_ ?_ ?_ ?_
    · refine (PrimeSpectrum.isHomeomorph_comap (TrivSqZeroExt.map (LinearMap.fst R R R)).toRingHom
        (fun x => ⟨1, one_pos, TrivSqZeroExt.map i₁ x, by ext <;> simp [i₁]⟩)
        fun d hd => ?_).surjective
      have h : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst hd
      exact ⟨2, by ext1 <;> simp [pow_two, h]⟩
    · intro d h₁ h₂
      have h₃ : d.fst = 0 := by simpa using congrArg TrivSqZeroExt.fst h₁
      have h₄ : d.snd.1 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₁
      have h₅ : d.snd.2 = 0 := by simpa using congrArg TrivSqZeroExt.snd h₂
      exact TrivSqZeroExt.ext h₃ (Prod.ext h₄ h₅)
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.fst R R R) ≫ _ = ofTwo O (LinearMap.fst R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.fst R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.fst R R R (i₁ 1) = 1 := rfl
      have e₃ : LinearMap.fst R R R (i₂ 1) = 0 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.mul_one]
    · refine congrArg Over.Hom.left
        (?_ : ofTwo O (LinearMap.snd R R R) ≫ _ = ofTwo O (LinearMap.snd R R R) ≫ _)
      rw [comp_mul]
      simp only [← Category.assoc, ofTwo_toTwo]
      have e₁ : LinearMap.snd R R R ((i₁ + i₂) 1) = 1 := by simp [i₁, i₂]
      have e₂ : LinearMap.snd R R R (i₁ 1) = 0 := rfl
      have e₃ : LinearMap.snd R R R (i₂ 1) = 1 := rfl
      rw [e₁, e₂, e₃, scale_zero_comp hy, _root_.one_mul]
  let l := a • LinearMap.fst R R R + b • LinearMap.snd R R R
  have := congrArg (ofTwo O l ≫ ·) key
  simp only [comp_mul, ← Category.assoc, ofTwo_toTwo] at this
  have e₁ : l ((i₁ + i₂) 1) = a + b := by simp [l, i₁, i₂]
  have e₂ : l (i₁ 1) = a := by simp [l, i₁]
  have e₃ : l (i₂ 1) = b := by simp [l, i₂]
  rwa [e₁, e₂, e₃] at this
end GlobalTheory.TangentPow
