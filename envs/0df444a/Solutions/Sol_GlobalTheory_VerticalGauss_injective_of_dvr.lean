-- Prove2me | solution 1 for GlobalTheory.VerticalGauss.injective_of_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:14:55.123498+00:00
-- url     : https://prove2.me/submissions/8ce8609e-f9df-418e-bea8-f6c089d87356

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_AlgebraMapOLInjective
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_NormOrderStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_AlgAll
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_FiniteVerticalGaussValuations

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.VerticalGauss
open IsLocalRing IsDedekindDomain
namespace GlobalTheory.VerticalGauss
theorem _root_.solution {R Ω : Type} [CommRing R] [IsDomain R] [Field Ω] (φ : R →+* Ω)
    (P : Ideal R) [P.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime P)]
    (hker : ∀ r, φ r = 0 → r ∈ P) (a : R) (ha : a ∈ P) (ha0 : φ a ≠ 0) :
    Function.Injective φ := by
  have hu : ∀ y : P.primeCompl, IsUnit (φ y) := fun y =>
    isUnit_iff_ne_zero.2 fun h => y.2 (hker _ h)
  let ψ : Localization.AtPrime P →+* Ω := IsLocalization.lift (M := P.primeCompl) hu
  have hψ : ∀ r, ψ (algebraMap R _ r) = φ r := fun r => IsLocalization.lift_eq hu r
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  have hϖ0 : ψ ϖ ≠ 0 := by
    intro h
    have hm : algebraMap R (Localization.AtPrime P) a ∈ maximalIdeal (Localization.AtPrime P) :=
      (IsLocalization.AtPrime.to_map_mem_maximal_iff _ P a).2 ha
    rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hm
    obtain ⟨c, hc⟩ := hm
    apply ha0
    rw [← hψ, hc, map_mul, h, zero_mul]
  rw [injective_iff_map_eq_zero]
  intro r hr
  by_contra hr0
  have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
    P.primeCompl_le_nonZeroDivisors
  have hr1 : algebraMap R (Localization.AtPrime P) r ≠ 0 := (map_ne_zero_iff _ hinj).2 hr0
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr1 hϖ
  rw [← hψ, hn, map_mul, map_pow] at hr
  exact mul_ne_zero (u.isUnit.map ψ).ne_zero (pow_ne_zero _ hϖ0) hr
end GlobalTheory.VerticalGauss
