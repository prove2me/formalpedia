-- Prove2me | solution 1 for GlobalTheory.DenseFibreIso.exists_away_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:28:55.69543+00:00
-- url     : https://prove2.me/submissions/89adca84-64d1-440c-9aa7-da7b898a8291

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsAwaySurjective
import Theorems.Thm_GlobalTheory_DenseFibreIso_exists_smul_eq_zero
import Theorems.Thm_GlobalTheory_DenseFibreIso_subsingleton_of_isUnit
import Theorems.Thm_GlobalTheory_DenseFibreIso_surjective_iff

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
open GlobalTheory GlobalTheory.DenseFibreIso
variable {A : Type} [CommRing A]
variable {B : Type} [CommRing B] [Algebra A B]
namespace GlobalTheory.DenseFibreIso
theorem _root_.solution [Module.Finite A B] (A' : Type) [CommRing A'] [Algebra A A']
    (h : Function.Surjective (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] B))
    (m : PrimeSpectrum A') :
    ∃ a : A, algebraMap A A' a ∉ m.asIdeal ∧ Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom :
        Localization.Away a →+* Localization.Away a ⊗[A] B) := by
  rw [surjective_iff] at h
  obtain ⟨a, ha, ha'⟩ :=
    exists_smul_eq_zero (A := A) (N := B ⧸ LinearMap.range (Algebra.linearMap A B)) A' m
  exact ⟨a, ha, (surjective_iff _).2
    (subsingleton_of_isUnit ha' _ (IsLocalization.Away.algebraMap_isUnit a))⟩
end GlobalTheory.DenseFibreIso
