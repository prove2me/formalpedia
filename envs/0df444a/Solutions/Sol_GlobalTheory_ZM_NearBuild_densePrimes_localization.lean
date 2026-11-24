-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.densePrimes_localization
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:31:51.192977+00:00
-- url     : https://prove2.me/submissions/08f4ad7b-6fcc-43e4-9cb5-7538df8bde1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Theorems.Thm_GlobalTheory_ZM_NearBuild_isPrime_of_mem
import Theorems.Thm_GlobalTheory_ZM_NearBuild_exists_mem_loc

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
noncomputable section
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.NearBuild
variable {o : Type} [CommRing o] {g N' : ℕ} {J : Type} {R R' : Type} [CommRing R] [CommRing R']
variable (b : TBase o (N' ^ 2)) (Mat : J → Matrix (Fin (2 * g)) (Fin (2 * g)) ℤ) (κ : ℕ)
  (β : o →+* R) (v : Ix g (N' ^ 2) → R)
variable {b Mat κ β v}
namespace GlobalTheory.ZM.NearBuild
theorem _root_.solution (h : DenseP (objPrimes b Mat κ β v)) (f : R) :
    DenseP (objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a))) := by
  intro g hg
  obtain ⟨⟨a, c⟩, hc⟩ := IsLocalization.surj (Submonoid.powers f) g
  have hfa : f * a = 0 := by
    apply h
    intro p hp _
    by_cases hfp : f ∈ p
    · exact p.mul_mem_right a hfp
    · obtain ⟨q₁, hq₁, hcomap⟩ := exists_mem_loc hp hfp
      have hgq : g ∈ q₁ := hg q₁ hq₁ (isPrime_of_mem hq₁)
      have haq : algebraMap R (Localization.Away f) a ∈ q₁ := by
        rw [← hc]
        exact q₁.mul_mem_right _ hgq
      have : a ∈ p := by
        rw [← hcomap]
        exact haq
      exact p.mul_mem_left f this
  have hloc : algebraMap R (Localization.Away f) a = 0 := by
    have h1 := congrArg (algebraMap R (Localization.Away f)) hfa
    rw [map_mul, map_zero] at h1
    exact (IsLocalization.Away.algebraMap_isUnit f).mul_right_eq_zero.1 h1
  have hcu : IsUnit (algebraMap R (Localization.Away f) (c : R)) :=
    IsLocalization.map_units (Localization.Away f) c
  simp only at hc
  rw [hloc] at hc
  exact hcu.mul_left_eq_zero.1 hc
end GlobalTheory.ZM.NearBuild
