-- Prove2me | solution 1 for GlobalTheory.ZM.NearBuild.exists_mem_loc
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:28:23.607198+00:00
-- url     : https://prove2.me/submissions/20500278-fe34-4445-b47d-272870971240

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DenseOfDenseP
import Theorems.Thm_GlobalTheory_ZM_NearBuild_good_comp
import Theorems.Thm_GlobalTheory_ZM_NearBuild_mem_objPrimes

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
theorem _root_.solution {q : Ideal R} (h : q ∈ objPrimes b Mat κ β v) {f : R} (hf : f ∉ q) :
    ∃ q₁ ∈ objPrimes b Mat κ ((loc f).comp β) (fun a => loc f (v a)), q₁.comap (loc f) = q := by
  obtain ⟨K, hF, hA, x, s, t, hk, hg⟩ := mem_objPrimes.1 h
  have hu : IsUnit (x f) := by
    refine isUnit_iff_ne_zero.2 fun h0 => hf ?_
    rw [← hk]
    exact h0
  let y : Localization.Away f →+* K := IsLocalization.Away.lift f hu
  have hy : y.comp (loc f) = x := IsLocalization.Away.lift_comp f hu
  refine ⟨RingHom.ker y, mem_objPrimes.2 ⟨K, hF, hA, y, s, t, rfl, ?_⟩, ?_⟩
  · rw [good_comp, hy]
    exact hg
  · rw [RingHom.comap_ker, hy, hk]
end GlobalTheory.ZM.NearBuild
