-- Prove2me | solution 1 for ModularCurve.XOneP.comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/b9b6dd34-324c-5513-a82c-322dfa53ee9f

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_X1Diamond
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry AlgebraicCurve.TwoChartIntegralModel

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (ϖ : A) (hϖ : IsLocalRing.maximalIdeal A = Ideal.span {ϖ})

    (d : ℕ) (hd : d.Coprime (M * p))
    (θ : ↥K ≃ₐ[L] ↥K)
    (hθ : ∀ (x : ↥K) (x' : ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))),
      (x : LaurentSeries L) = (x' : LaurentSeries L) →
        ((θ x : ↥K) : LaurentSeries L) =
          ((ModularCurve.baseChangeAut L (ModularCurve.diamondAut (M * p) d) x' :
            ↥(ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))) : LaurentSeries L))

    (ρ : ↥(chartAlgFin A (↥K) j) →+* ↥(chartAlgFin A (↥K) j))
    (hρ : ∀ x, ((ρ x : ↥(chartAlgFin A (↥K) j)) : ↥K) = θ x) (hsurj : Function.Surjective ρ) :
    ∀ 𝔓 ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes, 𝔓.comap ρ ∈ (Ideal.span {algebraMap A ↥(chartAlgFin A (↥K) j) ϖ}).minimalPrimes := by
  classical
  set R := ↥(chartAlgFin A (↥K) j)
  set ϖ' : R := algebraMap A R ϖ with hϖ'

  have hinj : Function.Injective ρ := by
    intro a b hab
    apply Subtype.ext
    apply θ.injective
    rw [← hρ a, ← hρ b, hab]

  have hfix : ρ ϖ' = ϖ' := by
    apply Subtype.ext
    rw [hρ]
    show θ ((algebraMap A R ϖ : R) : ↥K) = ((algebraMap A R ϖ : R) : ↥K)
    have : ((algebraMap A R ϖ : R) : ↥K) = algebraMap L ↥K (algebraMap A L ϖ) := by
      rw [← IsScalarTower.algebraMap_apply A L ↥K]
      rfl
    rw [this, AlgEquiv.commutes]

  have hI : (Ideal.span {ϖ'}).comap ρ = Ideal.span {ϖ'} := by
    apply le_antisymm
    · intro x hx
      rw [Ideal.mem_comap, Ideal.mem_span_singleton'] at hx
      obtain ⟨c, hc⟩ := hx
      obtain ⟨c', rfl⟩ := hsurj c
      rw [Ideal.mem_span_singleton']
      refine ⟨c', hinj ?_⟩
      rw [map_mul, hfix, hc]
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, hfix]
      exact Ideal.subset_span rfl
  intro 𝔓 h𝔓
  have h := Ideal.comap_minimalPrimes_eq_of_surjective hsurj (Ideal.span {ϖ'})
  rw [hI] at h
  rw [h]
  exact ⟨𝔓, h𝔓, rfl⟩

end S_ModularCurve_XOneP_comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_comap_mem_minimalPrimes_span_of_surjective_of_apply_eq_diamondAut_chartAlgFin_x1_mul (solution)
