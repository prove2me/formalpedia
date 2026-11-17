-- Prove2me | solution 1 for N25.GlobalKummer.division_quotient_class_zero
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T19:09:10.771734+00:00
-- url     : https://prove2.me/submissions/d3e1ef71-a00c-4d3a-84e5-eb75d77de0c7

import Mathlib
import Theorems.Thm_N25_GlobalKummer_quotientDivisionCocycle_levelS
import Definitions.Def_N25_GlobalKummerQuotient
import Definitions.Def_N25_GlobalKummerRamification
import Definitions.Def_N25_LocalKummerKernel
import Definitions.Def_N25_KummerFactorization
import Definitions.Def_N25_LocalKummerEquivariance
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Theorems.Thm_ModularCurve_reductionQExpModL_gammaH_smul_eq_self_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_eq_zero_of_reductionQExpModL_gammaH_eq_zero_of_nsmul_eq_zero
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_finiteDimensional_forall_mem_fixingSubgroup_smul_eq_place_laurentBaseChange
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_groupCohomology_exists_isUnramifiedOutside_forall_apply_eq_one_of_smooth
import Theorems.Thm_N25_GlobalKummer_cyclotomic_cocycle_kummer
import Definitions.Def_N25_GlobalKummerSequence
import Definitions.Def_GroupCohomology_Kummer
import Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_isMulCocycle1_of_level
import Theorems.Thm_N25_GlobalKummer_cyclotomic_coboundary_of_valuations
import Theorems.Thm_N25_GlobalKummer_radical_fixed_of_cocycle_zero
import Theorems.Thm_N25_GlobalKummer_local_kummer_coordinates
import Definitions.Def_N25_LocalFiniteFlatClasses
import Theorems.Thm_N25_GlobalKummer_quotient_zero_on_inertia
import Theorems.Thm_N25_GlobalKummer_quotient_zero_on_five_inertia
import Definitions.Def_N25_LocalKummerOperators
import Definitions.Def_N25_LocalKummerCharacter
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_cyclotomicCharacter_eq
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_padicIntegers_localGaloisToGlobal_eq
import Theorems.Thm_ExtCitation_cycloChar_primeLocalToGlobal_eq_one_of_mem_inertia
import Theorems.Thm_ExtCitation_exists_isFrobeniusAt_apply_primeLocalToGlobal
import Theorems.Thm_ValuationSubring_cycloChar_eq_unitOfCoprime_of_isFrobeniusAt
import Theorems.Thm_ExtCitation_liesOverPrime_primeLocalPlace
import Definitions.Def_N25_LocalFiveArithmetic
import Theorems.Thm_N25_GlobalKummer_divisionCocycle_isFiniteFlat_of_ordinary
import Definitions.Def_N25_OrdinaryKummerFiniteFlat
import Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_map_of_surjective
import Definitions.Def_GroupCohomology_CocycleExtensionAction
import Definitions.Def_GroupCohomology_FiniteFlatCocycle
import Theorems.Thm_HopfAlgebra_exists_finiteFlat_padicInt_withConv_equiv_subquotient
import Theorems.Thm_groupCohomology_IsFiniteFlatCocycle_valuation_dvd_of_multiplicative_coordinates
import Theorems.Thm_HopfAlgebra_exists_units_forall_inertia_apply_eq_of_inertiaCyclotomic_submonoid_padicInt
import Theorems.Thm_PadicAlgCl_exists_mem_inertiaSubgroupIn_apply_ne_of_forall_pow_eq_of_not_dvd_valuation
import Theorems.Thm_ValuationSubring_dvd_padicValRat_of_inertia_fixed_radical
import Theorems.Thm_ValuationSubring_isDiscreteValuationRing_comap_fixedField_inertiaSubgroupIn
import Theorems.Thm_ValuationSubring_valuation_ratCast_eq_zpow_padicValRat
import Theorems.Thm_N25_n5Surj
import Definitions.Def_N25_LocalFiveCondition
import Definitions.Def_N25_RatPointModel
import Definitions.Def_N25_LocalCarrier
import Theorems.Thm_AlgebraicGeometry_Scheme_exists_specMap_fixedField_comp_eq_of_forall_comp_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_and_flat_schemeNsmul
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_coe_nsmul_eq_comp_schemeNsmul
import Theorems.Thm_AlgebraicGeometry_existsUnique_section_comp_eq_of_isFinite_of_isAlgClosed
import Definitions.Def_N25_LocalFiveIntegralPoints
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Theorems.Thm_HenselianLocalRing_of_isAdicComplete_maximalIdeal
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_schemeHomOverComp_eq_and_nsmul_eq_of_henselianLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_smoothOfRelativeDimension_of_smooth_of_isLocalRing

set_option autoImplicit false

noncomputable section

namespace N25.GlobalKummer

local instance quotientVanishingPrimeSeventyOne_sdb5021 : Fact (Nat.Prime 71) := ⟨by decide⟩

local instance quotientVanishingPrimeFive_sdb5021 : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The multiplicative image of the actual global division class vanishes:
its Kummer parameter has valuation divisible by 71 at every rational prime. -/
theorem _root_.solution
    (hPhi : PhiFiveZero) (K2 : K2Rows) (hN71 : OrdinaryKummerFiniteFlat)
    (P : ↥M) (Q : J) (hQ : piEnd Q = (P : J)) :
    groupCohomology.H1π cyclotomicRep (quotientDivisionCocycle hPhi K2 P Q hQ) = 0 := by
  let c := quotientDivisionCocycle hPhi K2 P Q hQ
  obtain ⟨e, a, α, he, hα, hc⟩ := cyclotomic_cocycle_kummer c
    (quotientDivisionCocycle_levelS hPhi K2 P Q hQ).isLevelConstant₁
  apply (cyclotomic_coboundary_of_valuations c e he a α hα hc ?_).2
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hp71 : p = 71
  · subst p
    let r := localGaloisToGlobal 71
    let cg := divisionCocycle hPhi P Q hQ
    let d : groupCohomology.cocycles₁ (localKernelRep hPhi) :=
      ⟨fun σ => cg (r σ), by
        apply (groupCohomology.mem_cocycles₁_iff _).mpr
        intro σ τ
        change cg (r (σ * τ)) = (vRep hPhi).ρ (r σ) (cg (r τ)) + cg (r σ)
        rw [map_mul]
        exact (groupCohomology.mem_cocycles₁_iff _).mp cg.property (r σ) (r τ)⟩
    let f : groupCohomology.cocycles₁ localCyclotomicRep :=
      ⟨fun σ => c (r σ), by
        apply (groupCohomology.mem_cocycles₁_iff _).mpr
        intro σ τ
        change c (r (σ * τ)) = cyclotomicRep.ρ (r σ) (c (r τ)) + c (r σ)
        rw [map_mul]
        exact (groupCohomology.mem_cocycles₁_iff _).mp c.property (r σ) (r τ)⟩
    have hd := divisionCocycle_isFiniteFlat_of_ordinary hPhi hN71 P Q hQ
    have hf := groupCohomology.IsFiniteFlatCocycle.map_of_surjective 71
      (localKernelRep hPhi).ρ localCyclotomicRep.ρ d f
      (kernelQuotient hPhi K2).hom.toLinearMap K2.q_surjective
      (fun σ v => Rep.hom_comm_apply (kernelQuotient hPhi K2) (r σ) v)
      (fun _ => rfl) hd
    obtain ⟨μ, hμinj, hμzero, hμadd, hμroot, hμact, hγ, hKummer⟩ :=
      local_kummer_coordinates c e he a α hα hc
    have hv := groupCohomology.IsFiniteFlatCocycle.valuation_dvd_of_multiplicative_coordinates
      71 (by decide) localCyclotomicRep.ρ f hf μ hμinj hμzero hμadd hμroot hμact
      (algebraMap ℚ ℚ_[71] (a : ℚ)) (padicEmbedding 71 (α : AlgebraicClosure ℚ)) hγ hKummer
    change (71 : ℤ) ∣ Padic.valuation ((a : ℚ) : ℚ_[71]) at hv
    rw [Padic.valuation_ratCast] at hv
    exact hv
  · let A := ExtCitation.primeLocalPlace (⟨p, hp⟩ : Nat.Primes)
    have hA : A.LiesOverPrime p := ExtCitation.liesOverPrime_primeLocalPlace ⟨p, hp⟩
    apply ValuationSubring.dvd_padicValRat_of_inertia_fixed_radical A p hA 71 a α hα.symm
    intro σ hσ
    apply radical_fixed_of_cocycle_zero c e α hc σ
    by_cases hp5 : p = 5
    · subst p
      exact quotient_zero_on_five_inertia hPhi K2 n5Surj P Q hQ σ hσ
    · exact quotient_zero_on_inertia hPhi K2 P Q hQ hp5 hp71 A hA σ hσ

end N25.GlobalKummer
