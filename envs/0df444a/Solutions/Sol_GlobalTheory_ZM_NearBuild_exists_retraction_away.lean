-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.exists_retraction_away
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:34.498822+00:00
-- url     : https://prove2.me/submissions/f95c9b50-d15c-476c-9d8e-83d5fbde096e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRetractionNearOfUniquePoint
import Theorems.Thm_GlobalTheory_ZM_NearBuild_Den_loc
import Theorems.Thm_GlobalTheory_ZM_NearBuild_FibData_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory.ZM.NearBuild
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
namespace GlobalTheory.ZM.NearBuild
theorem _root_.solution (R B : Type) [CommRing R] [CommRing B] [Algebra R B]
    (hinj : Function.Injective (algebraMap R B)) (f : R)
    (hf : ∀ b : B, ∃ a : R, algebraMap R B a = algebraMap R B f * b) :
    ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f := by
  choose a ha using hf
  set g : Localization.Away f := IsLocalization.Away.invSelf f with hg
  have hfg : loc f f * g = 1 := IsLocalization.Away.mul_invSelf f
  have ha_zero : a 0 = 0 := hinj (by simp only [ha, MulZeroClass.mul_zero, map_zero])
  have ha_one : a 1 = f := hinj (by simp only [ha, _root_.mul_one])
  have ha_add : ∀ b c, a (b + c) = a b + a c := fun b c => hinj (by simp only [ha, map_add]; ring)
  have ha_mul : ∀ b c, f * a (b * c) = a b * a c := fun b c => hinj (by simp only [ha, map_mul]; ring)
  have ha_alg : ∀ c, a (algebraMap R B c) = f * c := fun c => hinj (by simp only [ha, map_mul])
  have h_one : loc f (a 1) * g = 1 := by rw [ha_one, hfg]
  have h_mul : ∀ b c, loc f (a (b * c)) * g = loc f (a b) * g * (loc f (a c) * g) := by
    intro b c
    have h := congrArg (loc f) (ha_mul b c)
    rw [map_mul, map_mul] at h
    linear_combination (-(loc f (a (b * c)) * g)) * hfg + g * g * h
  have h_zero : loc f (a 0) * g = 0 := by rw [ha_zero, map_zero, MulZeroClass.zero_mul]
  have h_add : ∀ b c, loc f (a (b + c)) * g = loc f (a b) * g + loc f (a c) * g := by
    intro b c
    rw [ha_add, map_add, add_mul]
  let r : B →+* Localization.Away f :=
    { toFun := fun b => loc f (a b) * g
      map_one' := h_one
      map_mul' := h_mul
      map_zero' := h_zero
      map_add' := h_add }
  refine ⟨r, ?_⟩
  · ext c
    show loc f (a (algebraMap R B c)) * g = loc f c
    rw [ha_alg, map_mul]
    linear_combination (loc f c) * hfg
end GlobalTheory.ZM.NearBuild
