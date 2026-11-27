-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.exists_retraction_near_of_unique_point
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:36:32.397295+00:00
-- url     : https://prove2.me/submissions/ba6c493d-093b-4980-a49d-8422f13cba61

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_AlgebraMapSurjectiveOfUnramifiedOfUniquePoint
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsRetractionNearOfUniquePoint
import Theorems.Thm_GlobalTheory_ZM_NearBuild_exists_smul_mem_range_of_unique_point
import Theorems.Thm_GlobalTheory_ZM_NearBuild_exists_retraction_away
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
theorem _root_.solution :
    ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Module.Finite R B] [Algebra.FormallyUnramified R B] (P : Set (Ideal R)), DenseP P → (∀ q ∈ P, ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (x : R →+* K), RingHom.ker x = q ∧ ∃! y : B →+* K, y.comp (algebraMap R B) = x) → ∀ q₀ ∈ P, ∃ f : R, f ∉ q₀ ∧ ∃ r : B →+* Localization.Away f, r.comp (algebraMap R B) = loc f ∧ ∀ (T : Type) [CommRing T] (x : Localization.Away f →+* T) (y : B →+* T), y.comp (algebraMap R B) = x.comp (loc f) → y = x.comp r := by
  intro R B _ _ _ _ _ P hD hP q₀ hq₀
  obtain ⟨K, _, _, x, hker, y, hy, hu⟩ := hP q₀ hq₀
  obtain ⟨f, hfk, hfB⟩ := exists_smul_mem_range_of_unique_point R B K x y hy hu
  have hinj : Function.Injective (algebraMap R B) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    refine hD a fun p hp _ => ?_
    obtain ⟨K', _, _, x', hker', y', hy', -⟩ := hP p hp
    rw [← hker', RingHom.mem_ker, ← hy', RingHom.comp_apply, ha, map_zero]
  obtain ⟨r, hr⟩ := exists_retraction_away R B hinj f hfB
  refine ⟨f, hker ▸ hfk, r, hr, fun T _ x' y' hxy => ?_⟩
  ext b
  obtain ⟨a, ha⟩ := hfB b
  have h1 : y' (algebraMap R B a) = x' (loc f a) := RingHom.congr_fun hxy a
  have h2 : y' (algebraMap R B f) = x' (loc f f) := RingHom.congr_fun hxy f
  have h3 : loc f a = loc f f * r b := by
    rw [← RingHom.congr_fun hr a, ← RingHom.congr_fun hr f, RingHom.comp_apply, RingHom.comp_apply, ha, map_mul]
  have hU : IsUnit (x' (loc f f)) := (IsLocalization.Away.algebraMap_isUnit f).map x'
  apply hU.mul_left_cancel
  rw [RingHom.comp_apply, ← map_mul, ← h3, ← h1, ha, map_mul, h2]
end GlobalTheory.ZM.NearBuild
