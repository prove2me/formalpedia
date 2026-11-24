-- Prove2me | solution 1 for GlobalTheory.UnitLemma.UnrExt.val_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:01:46.628926+00:00
-- url     : https://prove2.me/submissions/424a720b-3f39-4148-9155-a67ce27f6bee

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_IsPrecompleteOfBasis
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsUnramifiedOddDegreeQuadraticLocalExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.UnitLemma Polynomial IsLocalRing
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.UnrExt
namespace GlobalTheory.UnitLemma.UnrExt
theorem _root_.solution {O W E L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [Field E] [Field L] [Algebra O E] [IsFractionRing O E] [Algebra W L]
    [IsFractionRing W L] (j : O →+* W) (hj : ∀ ϖ : O, Irreducible ϖ → Irreducible (j ϖ)) (φ : E →+* L)
    (hφ : ∀ x, φ (algebraMap O E x) = algebraMap W L (j x)) (x : E) : val W (φ x) = val O x := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have h1 : ∀ a : O, (IsDiscreteValuationRing.maximalIdeal W).valuation L (φ (algebraMap O E a)) =
      (IsDiscreteValuationRing.maximalIdeal O).valuation E (algebraMap O E a) := fun a => by
    rw [hφ, IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap,
      IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    have e1 := IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (IsDiscreteValuationRing.maximalIdeal O) hϖ.ne_zero hϖ.maximalIdeal_eq
    have e2 := IsDedekindDomain.HeightOneSpectrum.intValuation_singleton
      (IsDiscreteValuationRing.maximalIdeal W) (hj ϖ hϖ).ne_zero (hj ϖ hϖ).maximalIdeal_eq
    have e3 : (IsDiscreteValuationRing.maximalIdeal O).intValuation (u : O) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h u.isUnit
    have e4 : (IsDiscreteValuationRing.maximalIdeal W).intValuation (j u) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.intValuation_eq_one_iff.2 fun h => h (u.isUnit.map j)
    simp only [map_mul, map_pow, e1, e2, e3, e4]
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := O) x
  unfold val
  rw [map_div₀, map_div₀, map_div₀, h1, h1]
end GlobalTheory.UnitLemma.UnrExt
