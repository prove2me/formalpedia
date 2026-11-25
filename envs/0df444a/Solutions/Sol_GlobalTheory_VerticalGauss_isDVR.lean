-- Prove2me | solution 1 for GlobalTheory.VerticalGauss.isDVR
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:40:18.159556+00:00
-- url     : https://prove2.me/submissions/dfed44e8-5386-4b39-adb6-6aea510f9d88

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
theorem _root_.solution {K : Type} [Field K] [NumberField K] (σ : Type) [Finite σ]
    (la : HeightOneSpectrum (𝓞 K)) :
    IsDiscreteValuationRing (Localization.AtPrime (extPrime σ la)) := by
  classical
  set P := extPrime σ la
  set Ol := Localization.AtPrime la.asIdeal
  have : IsDiscreteValuationRing Ol :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) la.ne_bot Ol
  have hC : ∀ y : la.asIdeal.primeCompl,
      IsUnit ((algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp
        (MvPolynomial.C) (y : 𝓞 K)) := by
    intro y
    apply IsLocalization.map_units (M := P.primeCompl) (Localization.AtPrime P)
      ⟨MvPolynomial.C (y : 𝓞 K), _⟩
    intro hy
    apply y.2
    have := (MvPolynomial.mem_map_C_iff (I := la.asIdeal) (f := MvPolynomial.C (y : 𝓞 K))).mp hy 0
    simpa using this
  let φ : Ol →+* Localization.AtPrime P := IsLocalization.lift (M := la.asIdeal.primeCompl) hC
  have hφ : φ.comp (algebraMap (𝓞 K) Ol) =
      (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)).comp MvPolynomial.C :=
    IsLocalization.lift_comp hC
  have hmax : maximalIdeal (Localization.AtPrime P) = (maximalIdeal Ol).map φ := by
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Localization.AtPrime.map_eq_maximalIdeal,
      Ideal.map_map, hφ, ← Ideal.map_map]
    rfl
  have : IsNoetherianRing (Localization.AtPrime P) :=
    IsLocalization.isNoetherianRing P.primeCompl _ inferInstance
  have hnf : ¬ IsField (Localization.AtPrime P) := by
    rw [isField_iff_maximalIdeal_eq, ← Localization.AtPrime.map_eq_maximalIdeal]
    intro h
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot la.ne_bot
    have hm : (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) (MvPolynomial.C a) ∈
        P.map (algebraMap (MvPolynomial σ (𝓞 K)) (Localization.AtPrime P)) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ ha)
    rw [h, Ideal.mem_bot] at hm
    have hinj := IsLocalization.injective (Localization.AtPrime P) (M := P.primeCompl)
      P.primeCompl_le_nonZeroDivisors
    apply ha0
    have := hinj (hm.trans (map_zero _).symm)
    simpa using this
  refine ((IsDiscreteValuationRing.TFAE (Localization.AtPrime P) hnf).out 0 4).mpr ?_
  rw [hmax]
  obtain ⟨g, hg⟩ := (IsPrincipalIdealRing.principal (maximalIdeal Ol))
  rw [hg]
  refine ⟨⟨φ g, ?_⟩⟩
  change Ideal.map φ (Ideal.span {g}) = Ideal.span {φ g}
  rw [Ideal.map_span, Set.image_singleton]
end GlobalTheory.VerticalGauss
