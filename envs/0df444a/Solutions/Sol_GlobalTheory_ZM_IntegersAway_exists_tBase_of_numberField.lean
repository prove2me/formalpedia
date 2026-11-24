-- Prove2me | solution 1 for GlobalTheory.ZM.IntegersAway.exists_tBase_of_numberField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:29:10.016251+00:00
-- url     : https://prove2.me/submissions/8e86f5cd-3d64-4c79-b94b-630c8435886d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsGaloisCover
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsPrimitiveRootMapOfNatCastNeZero
import Theorems.Thm_GlobalTheory_ZM_IntegersAway_isPrimitiveRoot_map_of_natCast_ne_zero
import Theorems.Thm_GlobalTheory_ZM_exists_arBase_away


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
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZM.IntegersAway
namespace GlobalTheory.ZM.IntegersAway
theorem _root_.solution {F : Type} [Field F] [NumberField F] (φ : F →+* ℂ) {k : ℕ} (hk : 0 < k)
    {z r : F} (hz : IsPrimitiveRoot z k) (hr : IsIntegral ℤ r) :
    ∃ (o : Type) (_ : CommRing o) (b : TBase o k) (em : o →+* ℂ) (ρ : o) (_ : Algebra o F), ArBase em ∧
      IsFractionRing o F ∧ (∀ x, φ (algebraMap o F x) = em x) ∧ algebraMap o F ρ = r ∧
      algebraMap o F (b.ζ : o) = z := by
  obtain ⟨em, hem, hcomp⟩ := exists_arBase_away φ hk.ne'
  have hn' : (k : 𝓞 F) ≠ 0 := by exact_mod_cast hk.ne'
  have hM : Submonoid.powers (k : 𝓞 F) ≤ nonZeroDivisors (𝓞 F) := powers_le_nonZeroDivisors_of_noZeroDivisors hn'
  let o := Localization.Away (k : 𝓞 F)
  have hu : IsUnit (algebraMap (𝓞 F) F (k : 𝓞 F)) := by simpa using hk.ne'
  let j : o →+* F := IsLocalization.Away.lift (k : 𝓞 F) hu
  have hj : ∀ x, j (algebraMap (𝓞 F) o x) = algebraMap (𝓞 F) F x := IsLocalization.Away.lift_eq _ hu
  let alg : Algebra o F := j.toAlgebra
  have : IsScalarTower (𝓞 F) o F := IsScalarTower.of_algebraMap_eq fun x => (hj x).symm
  let z₀ : 𝓞 F := ⟨z, hz.isIntegral hk⟩
  have hz₀ : IsPrimitiveRoot z₀ k :=
    IsPrimitiveRoot.of_map_of_injective (f := algebraMap (𝓞 F) F) hz RingOfIntegers.coe_injective
  have hko : IsUnit (k : o) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := o) (k : 𝓞 F)
  have hzu : IsUnit (algebraMap (𝓞 F) o z₀) := (hz₀.isUnit hk.ne').map _
  refine ⟨o, inferInstance, ⟨hzu.unit, hko, fun K _ β => ?_⟩, em, algebraMap (𝓞 F) o ⟨r, hr⟩, alg, hem,
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (Submonoid.powers (k : 𝓞 F)) o F, ?_, hj _, hj _⟩
  · refine isPrimitiveRoot_map_of_natCast_ne_zero hk hz₀ (β.comp (algebraMap (𝓞 F) o)) ?_
    simpa using (hko.map β).ne_zero
  · have : φ.comp j = em := by
      refine IsLocalization.ringHom_ext (Submonoid.powers (k : 𝓞 F)) ?_
      rw [hcomp]
      ext x
      simp [hj]
    exact fun x => DFunLike.congr_fun this x
end GlobalTheory.ZM.IntegersAway
