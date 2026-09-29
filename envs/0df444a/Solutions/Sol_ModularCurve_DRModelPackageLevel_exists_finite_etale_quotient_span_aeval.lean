-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.exists_finite_etale_quotient_span_aeval
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/b33f08f2-2cde-5b22-94b2-4e7426511ca6

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_forall_finite_quotient_span_aeval_and_finrank_le
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
import Theorems.Thm_ModularCurve_DRModelPackageLevel_modularUnitSeries_mem_chartAlgFin_mul
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isReduced_chartAlgFin_quotient_span_natCast
import Theorems.Thm_ModularCurve_exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_valuationSubring_pair_of_not_dvd
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd
import Theorems.Thm_Algebra_exists_etale_localizationAway_of_forall_isEtaleAt
import Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
import Theorems.Thm_GaloisRep_ratLocalizedAt_maximalIdeal_eq_span_natCast
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isPrincipalIdealRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_irreducible_natCast_ratLocalizedAt
import Theorems.Thm_GaloisRep_mem_ratLocalizedAt_iff
import Theorems.Thm_GaloisRep_isLocalization_ratLocalizedAt
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval
p2m_attr_erase "instance" "AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve NeronModelInfra GoodReductionJacobian
open AlgebraicGeometry.RelPicard
open ModularCurve ModularCurve.IgusaScheme ModularCurve.DRLevel
p2m_open_scoped "Polynomial AlgebraicGeometry.Polynomial"
p2m_open "Polynomial AlgebraicGeometry.Polynomial IsLocalRing"

noncomputable section

namespace N2Body

section TwoPrimes

variable {A : Type*} [CommRing A] {Pu Pz : Ideal A} [Pu.IsPrime] [Pz.IsPrime] {π x : A}

private theorem mem_span_of_mul_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x))
    (hxu : x ∉ Pu) {y : A} (h : x * y ∈ Ideal.span {π}) : y ∈ Ideal.span {π} := by
  rw [← hinf] at h ⊢
  refine ⟨(Ideal.IsPrime.mem_or_mem ‹Pu.IsPrime› h.1).resolve_left hxu, ?_⟩
  have h2 : Ideal.Quotient.mk Pz x * Ideal.Quotient.mk Pz y = 0 := by
    rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]; exact h.2
  show y ∈ Pz
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  exact (hxz.mul_right_eq_zero).1 h2

private theorem le_span_sup_span (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    Pu ≤ Ideal.span {π} ⊔ Ideal.span {x} := by
  intro y hy
  obtain ⟨w, hw⟩ := hxz.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hz : x * z - 1 ∈ Pz := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_mul, hw, map_one, sub_self]
  have hprod : (x * z - 1) * y ∈ Ideal.span {π} := by
    rw [← hinf]
    exact ⟨Pu.mul_mem_left _ hy, Pz.mul_mem_right _ hz⟩
  have : y = x * (z * y) - (x * z - 1) * y := by ring
  rw [this]
  exact Ideal.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.2 ⟨z * y, by ring⟩))
    (Ideal.mem_sup_left hprod)

private theorem pi_mem (hinf : Pu ⊓ Pz = Ideal.span {π}) : π ∈ Pu :=
  (hinf.symm ▸ Ideal.mem_span_singleton_self π : π ∈ Pu ⊓ Pz).1

private theorem span_sup_span_eq (hinf : Pu ⊓ Pz = Ideal.span {π}) (hxz : IsUnit (Ideal.Quotient.mk Pz x)) :
    Ideal.span {π} ⊔ Ideal.span {x} = Pu ⊔ Ideal.span {x} :=
  le_antisymm (sup_le_sup_right ((Ideal.span_singleton_le_iff_mem _).2 (pi_mem hinf)) _)
    (sup_le (le_span_sup_span hinf hxz) le_sup_right)

end TwoPrimes

section IntTransport

private theorem formallyUnramified_int_congr {X : Type*} [CommRing X] (i₁ i₂ : Algebra ℤ X)
    (h : @Algebra.FormallyUnramified ℤ X _ _ i₁) : @Algebra.FormallyUnramified ℤ X _ _ i₂ := by
  have := Subsingleton.elim i₁ i₂; subst this; exact h

private theorem formallyUnramified_int_of_ringEquiv {X Y : Type*} [CommRing X] [CommRing Y] {iX : Algebra ℤ X}
    {iY : Algebra ℤ Y} (e : X ≃+* Y) (h : @Algebra.FormallyUnramified ℤ X _ _ iX) :
    @Algebra.FormallyUnramified ℤ Y _ _ iY := by
  have h' : @Algebra.FormallyUnramified ℤ X _ _ (Ring.toIntAlgebra X) := formallyUnramified_int_congr _ _ h
  refine formallyUnramified_int_congr (Ring.toIntAlgebra Y) iY ?_
  exact @Algebra.FormallyUnramified.of_equiv ℤ _ X Y _ (Ring.toIntAlgebra X) _ (Ring.toIntAlgebra Y) h'
    (@AlgEquiv.ofRingEquiv ℤ X Y _ _ _ (Ring.toIntAlgebra X) (Ring.toIntAlgebra Y) e (fun n => by simp))

private def algEquivOfRingEquiv' {R₀ : Type*} [CommRing R₀] {X Y : Type*} [CommRing X] [CommRing Y] [Algebra R₀ X] [Algebra R₀ Y]
    (f : X ≃+* Y) (h : ∀ r, f (algebraMap R₀ X r) = algebraMap R₀ Y r) : X ≃ₐ[R₀] Y :=
  AlgEquiv.ofRingEquiv (f := f) h

end IntTransport

section Transfer

variable {R₀ : Type*} [CommRing R₀] {A : Type*} [CommRing A] [Algebra R₀ A]

private theorem etale_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Algebra.Etale R₀ (A ⧸ I)] : Algebra.Etale R₀ (A ⧸ J) :=
  Algebra.Etale.of_equiv (Ideal.quotientEquivAlg I J f h)

private theorem finite_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Module.Finite R₀ (A ⧸ I)] : Module.Finite R₀ (A ⧸ J) :=
  Module.Finite.equiv (Ideal.quotientEquivAlg I J f h).toLinearEquiv

private theorem free_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A))
    [Module.Free R₀ (A ⧸ I)] : Module.Free R₀ (A ⧸ J) :=
  Module.Free.of_equiv (Ideal.quotientEquivAlg I J f h).toLinearEquiv

private theorem finrank_quotient_of_algEquiv (I J : Ideal A) (f : A ≃ₐ[R₀] A) (h : J = I.map (f : A →+* A)) :
    Module.finrank R₀ (A ⧸ J) = Module.finrank R₀ (A ⧸ I) :=
  (LinearEquiv.finrank_eq (Ideal.quotientEquivAlg I J f h).toLinearEquiv).symm

private def fibreQuotEquiv (𝔪 : Ideal R₀) (I K : Ideal A) (hK : 𝔪.map (algebraMap R₀ A) ⊔ I = K) :
    ((A ⧸ I) ⧸ 𝔪.map (algebraMap R₀ (A ⧸ I))) ≃+* A ⧸ K :=
  (Ideal.quotEquivOfEq (by rw [Ideal.map_map, ← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_eq])).trans
    ((DoubleQuot.quotQuotEquivQuotSup I (𝔪.map (algebraMap R₀ A))).trans (Ideal.quotEquivOfEq (by rw [sup_comm, hK])))

private theorem formallyUnramified_fibre (𝔪 : Ideal R₀) (I K : Ideal A) (hK : 𝔪.map (algebraMap R₀ A) ⊔ I = K)
    (h : Algebra.FormallyUnramified ℤ (A ⧸ K)) :
    Algebra.FormallyUnramified ℤ ((A ⧸ I) ⧸ 𝔪.map (algebraMap R₀ (A ⧸ I))) :=
  formallyUnramified_int_of_ringEquiv (fibreQuotEquiv 𝔪 I K hK).symm h

end Transfer

section EtaleUnit

private theorem etale_of_etale_localizationAway_of_isUnit {R₀ S : Type*} [CommRing R₀] [CommRing S] [Algebra R₀ S]
    (c : R₀) (hc : IsUnit c)
    (het : letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R₀ S c))) :
    Algebra.Etale R₀ S := by
  letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
  haveI := het
  haveI : Algebra.Etale R₀ (Localization.Away c) :=
    ⟨Algebra.FormallyEtale.of_isLocalization (M := Submonoid.powers c), IsLocalization.Away.finitePresentation c⟩
  haveI : IsScalarTower R₀ (Localization.Away c) (Localization.Away (algebraMap R₀ S c)) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [RingHom.algebraMap_toAlgebra, Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_comp,
      ← IsScalarTower.algebraMap_eq]
  haveI : Algebra.Etale R₀ (Localization.Away (algebraMap R₀ S c)) :=
    Algebra.Etale.comp R₀ (Localization.Away c) _
  let eS : S ≃ₐ[S] Localization.Away (algebraMap R₀ S c) :=
    IsLocalization.atUnits S (Submonoid.powers (algebraMap R₀ S c))
      (by rintro _ ⟨n, rfl⟩; exact (hc.map _).pow n)
  exact Algebra.Etale.of_equiv (eS.symm.restrictScalars R₀)

end EtaleUnit

section EtaleLocal

universe u

private theorem exists_etale_localizationAway_of_forall_isUnramifiedAt
    {R₀ S : Type u} [CommRing R₀] [IsDomain R₀] [CommRing S] [Algebra R₀ S]
    [Module.Finite R₀ S] [Algebra.FinitePresentation R₀ S] [Module.Flat R₀ S]
    (hgen : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.comap (algebraMap R₀ S) = ⊥ → Algebra.IsUnramifiedAt R₀ 𝔮)
    (𝔪 : Ideal R₀) [𝔪.IsPrime]
    (hfib : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], 𝔮.comap (algebraMap R₀ S) = 𝔪 → Algebra.IsUnramifiedAt R₀ 𝔮) :
    ∃ c : R₀, c ≠ 0 ∧ c ∉ 𝔪 ∧
      letI := (Localization.awayMap (algebraMap R₀ S) c).toAlgebra
      Algebra.Etale (Localization.Away c) (Localization.Away (algebraMap R₀ S c)) := by
  classical
  obtain ⟨c, hc0, hcT, het⟩ := Algebra.exists_etale_localizationAway_of_forall_isEtaleAt (R := R₀) (S := S)
    (fun 𝔮 h𝔮P h𝔮 => by
      haveI := h𝔮P
      haveI : Algebra.IsUnramifiedAt R₀ 𝔮 := hgen 𝔮 h𝔮
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔮)
    {𝔪}
    (fun Pm hPm => by rw [Finset.mem_singleton] at hPm; subst hPm; infer_instance)
    (fun Pm hPm 𝔮 h𝔮P h𝔮 => by
      rw [Finset.mem_singleton] at hPm
      subst hPm
      haveI := h𝔮P
      haveI : Algebra.IsUnramifiedAt R₀ 𝔮 := hfib 𝔮 h𝔮
      exact Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat 𝔮)
  exact ⟨c, hc0, hcT _ (Finset.mem_singleton_self _), het⟩

end EtaleLocal

section FibreUnram

private theorem isLocalHom_of_field {K L : Type*} [Field K] [CommRing L] [Nontrivial L] (f : K →+* L) : IsLocalHom f :=
  ⟨fun a ha => by
    rcases eq_or_ne a 0 with rfl | h
    · rw [map_zero] at ha; exact (not_isUnit_zero ha).elim
    · exact isUnit_iff_ne_zero.2 h⟩

universe u
variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Algebra.EssFiniteType ℤ R]

set_option maxHeartbeats 3200000 in

private theorem isUnramifiedAt_of_fibre (p : ℕ) [Fact p.Prime] (𝔭 : Ideal R) [𝔭.IsMaximal] (hp : (p : R) ∈ 𝔭)
    (hκ : PerfectField 𝔭.ResidueField)
    (hF : Algebra.FormallyUnramified ℤ (S ⧸ 𝔭.map (algebraMap R S)))
    (q : Ideal S) [q.IsPrime] [q.LiesOver 𝔭] : Algebra.IsUnramifiedAt R q := by
  classical
  letI := Localization.AtPrime.algebraOfLiesOver 𝔭 q
  have hess : Algebra.EssFiniteType R S := inferInstance
  rw [Algebra.isUnramifiedAt_iff_map_eq R 𝔭 q]
  constructor
  · haveI := hκ
    haveI : Module.Finite 𝔭.ResidueField q.ResidueField := inferInstance
    exact Algebra.IsAlgebraic.isSeparable_of_perfectField
  · set I : Ideal S := 𝔭.map (algebraMap R S) with hI
    have hJI : 𝔭.map (algebraMap R (Localization.AtPrime q)) = I.map (algebraMap S (Localization.AtPrime q)) := by
      rw [hI, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
    rw [hJI]
    set J : Ideal (Localization.AtPrime q) := I.map (algebraMap S (Localization.AtPrime q)) with hJ
    haveI : (maximalIdeal (Localization.AtPrime q)).LiesOver 𝔭 := Ideal.LiesOver.trans _ q 𝔭
    have hJle : J ≤ maximalIdeal (Localization.AtPrime q) := by
      rw [← hJI, Ideal.map_le_iff_le_comap]
      exact le_of_eq (Ideal.LiesOver.over (p := 𝔭) (P := maximalIdeal (Localization.AtPrime q)))
    have hJtop : J ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJle
    haveI : Nontrivial (Localization.AtPrime q ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJtop
    haveI : IsLocalRing (Localization.AtPrime q ⧸ J) := .of_surjective' _ Ideal.Quotient.mk_surjective
    haveI : Algebra.FormallyUnramified (S ⧸ I) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_isLocalization (Algebra.algebraMapSubmonoid (S ⧸ I) q.primeCompl)
    have hT1 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := S ⧸ I) (A := Localization.AtPrime q ⧸ J)
      (Subsingleton.elim _ _)
    haveI := hT1
    haveI : Algebra.FormallyUnramified ℤ (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.comp ℤ (S ⧸ I) _
    have hpJ : (p : Localization.AtPrime q ⧸ J) = 0 := by
      rw [← map_natCast (algebraMap S (Localization.AtPrime q ⧸ J)), ← map_natCast (algebraMap R S),
        IsScalarTower.algebraMap_apply S (Localization.AtPrime q) (Localization.AtPrime q ⧸ J),
        Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, hJ]
      exact Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hp)
    haveI : CharP (Localization.AtPrime q ⧸ J) p := by
      have hdvd : ringChar (Localization.AtPrime q ⧸ J) ∣ p := (ringChar.spec _ p).1 hpJ
      rcases (Nat.dvd_prime Fact.out).1 hdvd with h1 | hp'
      · exact absurd h1 (CharP.ringChar_ne_one)
      · exact hp' ▸ ringChar.charP _
    letI : Algebra (ZMod p) (Localization.AtPrime q ⧸ J) := ZMod.algebra _ p
    haveI : IsLocalHom (algebraMap (ZMod p) (Localization.AtPrime q ⧸ J)) := isLocalHom_of_field _
    have hT2 := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ZMod p) (A := Localization.AtPrime q ⧸ J)
      (Subsingleton.elim _ _)
    haveI := hT2
    haveI : Algebra.FormallyUnramified (ZMod p) (Localization.AtPrime q ⧸ J) :=
      Algebra.FormallyUnramified.of_restrictScalars ℤ (ZMod p) _
    haveI : Algebra.EssFiniteType ℤ (Localization.AtPrime q ⧸ J) := by
      have : Algebra.EssFiniteType ℤ S := Algebra.EssFiniteType.comp ℤ R S
      have : Algebra.EssFiniteType ℤ (Localization.AtPrime q) := Algebra.EssFiniteType.comp ℤ S _
      exact Algebra.EssFiniteType.comp ℤ (Localization.AtPrime q) _
    haveI : Algebra.EssFiniteType (ZMod p) (Localization.AtPrime q ⧸ J) := Algebra.EssFiniteType.of_comp ℤ (ZMod p) _
    have hmax : maximalIdeal (Localization.AtPrime q ⧸ J) = ⊥ := by
      rw [← Algebra.FormallyUnramified.map_maximalIdeal (R := ZMod p) (S := Localization.AtPrime q ⧸ J),
        IsLocalRing.maximalIdeal_eq_bot (R := ZMod p), Ideal.map_bot]
    refine le_antisymm hJle ?_
    have hne : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≠ ⊤ := by
      rw [Ne, Ideal.map_eq_top_iff_of_ker_le (Ideal.Quotient.mk J) (by rw [Ideal.mk_ker]; exact hJle)
        (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)]
      exact (maximalIdeal.isMaximal _).ne_top
    have hle : (maximalIdeal (Localization.AtPrime q)).map (Ideal.Quotient.mk J) ≤ ⊥ :=
      hmax ▸ IsLocalRing.le_maximalIdeal hne
    intro z hz
    have hz' : Ideal.Quotient.mk J z ∈ (⊥ : Ideal (Localization.AtPrime q ⧸ J)) := hle (Ideal.mem_map_of_mem _ hz)
    rw [Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hz'
    exact hz'

end FibreUnram

section GenUnramS

variable {R : Type} [CommRing R] [IsDomain R] [CharZero R] [Algebra R ℚ] [IsFractionRing R ℚ]
variable {A : Type} [CommRing A] [IsDomain A] [Algebra R A]

private theorem dvd_of_irreducible_of_rootS {k K : Type*} [Field k] [Field K] [Algebra k K] {q r : k[X]}
    (hq : Irreducible q) {β : K} (hqβ : aeval β q = 0) (hrβ : aeval β r = 0) : q ∣ r := by
  have hmin : minpoly k β ∣ q := minpoly.dvd k β hqβ
  have hint : IsIntegral k β := ⟨q * C q.leadingCoeff⁻¹, by
    refine ⟨?_, ?_⟩
    · rw [Monic, leadingCoeff_mul, leadingCoeff_C, mul_inv_cancel₀ (leadingCoeff_ne_zero.2 hq.ne_zero)]
    · rw [eval₂_mul, ← aeval_def, hqβ, zero_mul]⟩
  exact ((minpoly.irreducible hint).associated_of_dvd hq hmin).symm.dvd.trans (minpoly.dvd k β hrβ)

private theorem aeval_notMem_of_not_dvdS (v : A) (g c₀ : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (hndvd : ¬ g ∣ c₀) (P : Ideal A) [P.IsPrime]
    (hP : P.comap (algebraMap R A) = ⊥) (hgP : aeval v g ∈ P) : aeval v c₀ ∉ P := by
  intro hc
  let L := FractionRing (A ⧸ P)
  haveI : CharZero (A ⧸ P) := by
    refine charZero_of_inj_zero (fun n hn => ?_)
    have h1 : algebraMap R A n ∈ P := by
      rw [map_natCast, ← Ideal.Quotient.eq_zero_iff_mem, map_natCast]; exact hn
    have h2 : (n : R) ∈ P.comap (algebraMap R A) := h1
    rw [hP, Ideal.mem_bot] at h2
    exact_mod_cast h2
  haveI : CharZero L := charZero_of_injective_algebraMap (IsFractionRing.injective (A ⧸ P) L)
  letI : Algebra ℚ L := DivisionRing.toRatAlgebra
  let β : L := algebraMap (A ⧸ P) L (Ideal.Quotient.mk P v)
  have hroot : ∀ f : ℤ[X], aeval v f ∈ P → aeval β (f.map (Int.castRingHom ℚ)) = 0 := by
    intro f hf
    have hT := IsScalarTower.of_algebraMap_eq' (R := ℤ) (S := ℚ) (A := L) (Subsingleton.elim _ _)
    haveI := hT
    have e1 : aeval β (f.map (Int.castRingHom ℚ)) = aeval β f := by
      rw [show Int.castRingHom ℚ = algebraMap ℤ ℚ from rfl, aeval_map_algebraMap]
    have e2 : aeval β f = algebraMap (A ⧸ P) L (aeval (Ideal.Quotient.mk P v) f) := aeval_algebraMap_apply L _ f
    have e3 : aeval (Ideal.Quotient.mk P v) f = Ideal.Quotient.mk P (aeval v f) := by
      rw [← Ideal.Quotient.algebraMap_eq, aeval_algebraMap_apply]
    rw [e1, e2, e3, Ideal.Quotient.eq_zero_iff_mem.2 hf, map_zero]
  have hdvd : g.map (Int.castRingHom ℚ) ∣ c₀.map (Int.castRingHom ℚ) :=
    dvd_of_irreducible_of_rootS hirr (hroot g hgP) (hroot c₀ hc)
  rw [Polynomial.map_dvd_map (Int.castRingHom ℚ) (Int.castRingHom ℚ).injective_int hg] at hdvd
  exact hndvd hdvd

private theorem formallyUnramified_of_surjectiveS {R' X Y : Type*} [CommRing R'] [CommRing X] [CommRing Y] [Algebra R' X]
    [Algebra R' Y] (f : X →+* Y) (hf : Function.Surjective f) (hcomm : f.comp (algebraMap R' X) = algebraMap R' Y)
    [Algebra.FormallyUnramified R' X] : Algebra.FormallyUnramified R' Y :=
  Algebra.FormallyUnramified.of_surjective ({ f with commutes' := fun r => RingHom.congr_fun hcomm r } : X →ₐ[R'] Y) hf

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

private theorem isUnramifiedAt_of_comap_eq_botS (v : A) (g c₀ : ℤ[X]) (hg : g.Monic)
    (hirr : Irreducible (g.map (Int.castRingHom ℚ))) (hndvd : ¬ g ∣ c₀)
    (hunr : letI : Algebra R[X] A := (aeval (R := R) v).toRingHom.toAlgebra
      ∀ (P : Ideal A) [P.IsPrime], P.comap (algebraMap R A) = ⊥ → aeval v c₀ ∉ P → Algebra.IsUnramifiedAt R[X] P)
    (S : Type) [CommRing S] [Algebra A S] [Algebra R S] [IsScalarTower R A S]
    (hsurj : Function.Surjective (algebraMap A S)) (hgS : algebraMap A S (aeval v g) = 0)
    (q : Ideal S) [q.IsPrime] (hq : q.comap (algebraMap R S) = ⊥) :
    Algebra.IsUnramifiedAt R q := by
  classical
  letI iRX : Algebra R[X] A := (aeval (R := R) v).toRingHom.toAlgebra
  letI iRXS : Algebra R[X] S := ((algebraMap A S).comp (algebraMap R[X] A)).toAlgebra
  haveI : IsScalarTower R[X] A S := IsScalarTower.of_algebraMap_eq' rfl
  let B := S
  let f : A →+* S := algebraMap A S
  let P : Ideal A := q.comap f
  haveI : P.IsPrime := Ideal.comap_isPrime f q

  have hPR : P.comap (algebraMap R A) = ⊥ := by
    refine le_bot_iff.1 (fun r hr => ?_)
    rw [Ideal.mem_comap, Ideal.mem_comap] at hr
    have h1 : f (algebraMap R A r) = algebraMap R B r := (IsScalarTower.algebraMap_apply R A S r).symm
    rw [h1, ← Ideal.mem_comap, hq] at hr
    exact hr

  have hgP : aeval v g ∈ P := by
    show f (aeval v g) ∈ q
    have : f (aeval v g) = 0 := hgS
    rw [this]; exact q.zero_mem

  have hcP : aeval v c₀ ∉ P := aeval_notMem_of_not_dvdS (R := R) v g c₀ hg hirr hndvd P hPR hgP
  have hUP : Algebra.IsUnramifiedAt R[X] P := hunr P hPR hcP

  have hPq : P = q.comap f := rfl
  let ψ : Localization.AtPrime P →+* Localization.AtPrime q := Localization.localRingHom P q f hPq
  have hψ : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨s, t⟩, hz⟩ := IsLocalization.surj q.primeCompl z
    obtain ⟨a, rfl⟩ := hsurj s
    obtain ⟨b, hb⟩ := hsurj (t : B)
    have hbP : b ∉ P := by
      intro h
      apply t.2
      show (t : B) ∈ q
      rw [← hb]; exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime P) a (⟨b, hbP⟩ : P.primeCompl), ?_⟩
    rw [Localization.localRingHom_mk', eq_comm, IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk]
    simp only at hz
    show z * algebraMap B (Localization.AtPrime q) (f b) = algebraMap B (Localization.AtPrime q) (f a)
    rw [show f b = (t : B) from hb]
    exact hz

  have halgS : algebraMap R[X] (Localization.AtPrime q) =
      (algebraMap B (Localization.AtPrime q)).comp (f.comp (algebraMap R[X] A)) := by
    rw [IsScalarTower.algebraMap_eq R[X] B (Localization.AtPrime q), IsScalarTower.algebraMap_eq R[X] A B]
  have hC : ∀ r : R, algebraMap R[X] (Localization.AtPrime q) (C r) = algebraMap R (Localization.AtPrime q) r := by
    intro r
    rw [halgS, RingHom.comp_apply, RingHom.comp_apply, IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)]
    show algebraMap B _ (f ((aeval (R := R) v).toRingHom (C r))) = algebraMap B _ (algebraMap R B r)
    rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, aeval_C]
    congr 1
    exact (IsScalarTower.algebraMap_apply R A S r).symm
  have hcomm : ψ.comp (algebraMap R[X] (Localization.AtPrime P)) = algebraMap R[X] (Localization.AtPrime q) := by
    rw [halgS, IsScalarTower.algebraMap_eq R[X] A (Localization.AtPrime P)]
    refine RingHom.ext (fun r => ?_)
    simp only [RingHom.comp_apply]
    exact Localization.localRingHom_to_map P q f hPq _
  haveI hU1 : Algebra.FormallyUnramified R[X] (Localization.AtPrime q) :=
    formallyUnramified_of_surjectiveS ψ hψ hcomm

  have hunitR : ∀ y : nonZeroDivisors R, IsUnit (algebraMap R (Localization.AtPrime q) y) := by
    intro y
    have hy : (y : R) ≠ 0 := nonZeroDivisors.coe_ne_zero y
    rw [IsScalarTower.algebraMap_apply R B (Localization.AtPrime q)]
    refine IsLocalization.map_units (Localization.AtPrime q) (⟨_, ?_⟩ : q.primeCompl)
    intro hmem
    have : (y : R) ∈ q.comap (algebraMap R B) := hmem
    rw [hq, Ideal.mem_bot] at this
    exact hy this
  let i : ℚ →+* Localization.AtPrime q := IsLocalization.lift (M := nonZeroDivisors R) hunitR
  have hi : i.comp (algebraMap R ℚ) = algebraMap R (Localization.AtPrime q) :=
    IsLocalization.lift_comp (M := nonZeroDivisors R) hunitR
  let gQ : ℚ[X] := g.map (Int.castRingHom ℚ)
  haveI : Fact (Irreducible gQ) := ⟨hirr⟩
  let x : Localization.AtPrime q := algebraMap R[X] (Localization.AtPrime q) X
  have hgx : eval₂ i x gQ = 0 := by

    let Φ : ℤ[X] →+* Localization.AtPrime q := eval₂RingHom (i.comp (Int.castRingHom ℚ)) x
    let Ψ : ℤ[X] →+* Localization.AtPrime q := (algebraMap R[X] (Localization.AtPrime q)).comp (mapRingHom (Int.castRingHom R))
    have hΦΨ : Φ = Ψ := by
      refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      show eval₂ (i.comp (Int.castRingHom ℚ)) x X = algebraMap R[X] (Localization.AtPrime q) (Polynomial.map (Int.castRingHom R) X)
      rw [eval₂_X, Polynomial.map_X]
    have e1 : eval₂ i x gQ = Φ g := by
      show eval₂ i x (g.map (Int.castRingHom ℚ)) = eval₂ (i.comp (Int.castRingHom ℚ)) x g
      rw [Polynomial.eval₂_map]
    rw [e1, hΦΨ]
    show algebraMap R[X] (Localization.AtPrime q) (g.map (Int.castRingHom R)) = 0
    rw [halgS, RingHom.comp_apply, RingHom.comp_apply]
    have hgA : algebraMap R[X] A (g.map (Int.castRingHom R)) = aeval v g := by
      show (aeval (R := R) v).toRingHom (g.map (Int.castRingHom R)) = aeval v g
      rw [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, show Int.castRingHom R = algebraMap ℤ R from rfl,
        aeval_map_algebraMap]
    rw [hgA, show f (aeval v g) = 0 from hgS, map_zero]
  let K := AdjoinRoot gQ
  let φK : K →+* Localization.AtPrime q := AdjoinRoot.lift i x hgx
  letI : Algebra K (Localization.AtPrime q) := φK.toAlgebra
  letI algRK : Algebra R[X] K := ((AdjoinRoot.mk gQ).comp (mapRingHom (algebraMap R ℚ))).toAlgebra
  have hTK : IsScalarTower R[X] K (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    refine Polynomial.ringHom_ext (fun r => ?_) ?_
    · show algebraMap R[X] (Localization.AtPrime q) (C r) = φK ((AdjoinRoot.mk gQ) (mapRingHom (algebraMap R ℚ) (C r)))
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C, AdjoinRoot.mk_C, AdjoinRoot.lift_of, hC]
      exact (RingHom.congr_fun hi r).symm
    · show x = φK ((AdjoinRoot.mk gQ) (mapRingHom (algebraMap R ℚ) X))
      rw [Polynomial.coe_mapRingHom, Polynomial.map_X, AdjoinRoot.mk_X, AdjoinRoot.lift_root]
  haveI := hTK
  haveI hU2 : Algebra.FormallyUnramified K (Localization.AtPrime q) :=
    Algebra.FormallyUnramified.of_restrictScalars R[X] K _

  haveI : Module.Finite ℚ K := (AdjoinRoot.powerBasis hirr.ne_zero).finite
  haveI : Algebra.IsSeparable ℚ K := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI hU3 : Algebra.FormallyUnramified ℚ K := Algebra.FormallyUnramified.of_isSeparable ℚ K
  haveI hU4 : Algebra.FormallyUnramified R ℚ := Algebra.FormallyUnramified.of_isLocalization (M := nonZeroDivisors R)
  haveI hU5 : Algebra.FormallyUnramified R K := Algebra.FormallyUnramified.comp R ℚ K
  have hT2 : IsScalarTower R K (Localization.AtPrime q) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    rw [IsScalarTower.algebraMap_eq R ℚ K]
    refine RingHom.ext (fun r => ?_)
    show algebraMap R (Localization.AtPrime q) r = φK (AdjoinRoot.of gQ (algebraMap R ℚ r))
    rw [AdjoinRoot.lift_of]
    exact (RingHom.congr_fun hi r).symm
  haveI := hT2
  exact Algebra.FormallyUnramified.comp R K _

end GenUnramS

section Laurent

variable {k : Type*} [Field k]

private theorem order_pow_eq (z : LaurentSeries k) (hz : z ≠ 0) : ∀ n : ℕ, z ^ n ≠ 0 ∧ (z ^ n).order = n * z.order
  | 0 => by simp
  | n + 1 => by
    obtain ⟨hn, hon⟩ := order_pow_eq z hz n
    refine ⟨mul_ne_zero hn hz, ?_⟩
    rw [pow_succ, HahnSeries.order_mul hn hz, hon]
    push_cast
    ring

private theorem aeval_ne_zero_of_order_neg {z : LaurentSeries k} (hz : z ≠ 0) (hneg : z.order < 0)
    (g : k[X]) (hg : g.Monic) (hD : 0 < g.natDegree) : aeval z g ≠ 0 := by
  classical
  obtain ⟨hzD, hoD⟩ := order_pow_eq z hz g.natDegree

  have key : ∀ i : ℕ, (algebraMap k (LaurentSeries k) (g.coeff i) * z ^ i).coeff (g.natDegree * z.order) =
      g.coeff i * (z ^ i).coeff (g.natDegree * z.order) := by
    intro i
    rw [HahnSeries.algebraMap_apply', show algebraMap k (PowerSeries k) (g.coeff i) = PowerSeries.C (g.coeff i) from rfl,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_apply, HahnSeries.coeff_single_zero_mul]

  have hcoeff : (aeval z g).coeff (g.natDegree * z.order) = (z ^ g.natDegree).coeff (g.natDegree * z.order) := by
    rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum, Finset.sum_range_succ, key, Finset.sum_eq_zero ?hlow, zero_add,
      show g.coeff g.natDegree = 1 from hg, one_mul]
    intro i hi
    rw [Finset.mem_range] at hi
    rw [key]
    obtain ⟨hzi, hoi⟩ := order_pow_eq z hz i
    have hlt : (g.natDegree : ℤ) * z.order < (z ^ i).order := by
      rw [hoi]
      have : (i : ℤ) < g.natDegree := by exact_mod_cast hi
      nlinarith
    rw [HahnSeries.coeff_eq_zero_of_lt_order hlt, mul_zero]
  have hne : (z ^ g.natDegree).coeff (g.natDegree * z.order) ≠ 0 := by
    rw [← hoD]; exact (HahnSeries.coeff_order_eq_zero.not.2 hzD)
  intro h
  rw [h, HahnSeries.coeff_zero] at hcoeff
  exact hne hcoeff.symm

private theorem order_eq_of_coeff {z : LaurentSeries k} {m : ℤ} (h1 : z.coeff m ≠ 0) (h2 : ∀ n < m, z.coeff n = 0) :
    z.order = m := by
  have hz : z ≠ 0 := HahnSeries.ne_zero_of_coeff_ne_zero h1
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero h1) ?_
  by_contra hlt
  push_neg at hlt
  exact (HahnSeries.coeff_order_eq_zero.not.2 hz) (h2 _ hlt)

end Laurent

section Base

variable (q : ℕ) [Fact q.Prime]

private theorem isLocalRing_R : IsLocalRing (R q) := GaloisRep.ratLocalizedAt.isLocalRing Fact.out

omit [Fact q.Prime] in
private theorem isDomain_R : IsDomain (R q) := inferInstance

omit [Fact q.Prime] in
private theorem isPrincipalIdealRing_R : IsPrincipalIdealRing (R q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q

private theorem isDiscreteValuationRing_R : IsDiscreteValuationRing (R q) :=
  GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

omit [Fact q.Prime] in
private theorem isFractionRing_R : IsFractionRing (R q) ℚ := GaloisRep.isFractionRing_ratLocalizedAt q

private theorem irreducible_natCast_R : Irreducible ((q : ℕ) : R q) := GaloisRep.irreducible_natCast_ratLocalizedAt q Fact.out

private theorem natCast_ne_zero_R : ((q : ℕ) : R q) ≠ 0 := (irreducible_natCast_R q).ne_zero

private theorem not_isUnit_natCast_R : ¬ IsUnit ((q : ℕ) : R q) := (irreducible_natCast_R q).not_isUnit

private theorem natCast_mem_maximalIdeal_R [IsLocalRing (R q)] : ((q : ℕ) : R q) ∈ IsLocalRing.maximalIdeal (R q) :=
  (IsLocalRing.mem_maximalIdeal _).mpr (not_isUnit_natCast_R q)

private theorem maximalIdeal_R [IsLocalRing (R q)] : IsLocalRing.maximalIdeal (R q) = Ideal.span {((q : ℕ) : R q)} :=
  GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q Fact.out

private theorem mem_maximalIdeal_R_iff [IsLocalRing (R q)] (x : R q) :
    x ∈ IsLocalRing.maximalIdeal (R q) ↔ ((q : ℕ) : R q) ∣ x := by
  rw [maximalIdeal_R, Ideal.mem_span_singleton]

omit [Fact q.Prime] in
private theorem eq_bot_or_eq_maximalIdeal [IsLocalRing (R q)] (𝔭 : Ideal (R q)) [𝔭.IsPrime] :
    𝔭 = ⊥ ∨ 𝔭 = IsLocalRing.maximalIdeal (R q) := by
  haveI := isPrincipalIdealRing_R q
  by_cases h : 𝔭 = ⊥
  · exact Or.inl h
  · exact Or.inr (IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal h))

omit [Fact q.Prime] in
private theorem comap_eq_bot_or_eq_maximalIdeal [IsLocalRing (R q)] {S : Type*} [CommRing S] [Algebra (R q) S]
    (𝔮 : Ideal S) [𝔮.IsPrime] :
    𝔮.comap (algebraMap (R q) S) = ⊥ ∨ 𝔮.comap (algebraMap (R q) S) = IsLocalRing.maximalIdeal (R q) :=
  eq_bot_or_eq_maximalIdeal q _

private theorem exists_int_sub_mem_span (x : R q) : ∃ n : ℤ, x - (n : R q) ∈ Ideal.span {((q : ℕ) : R q)} := by
  have hq : (q : ℕ).Prime := Fact.out
  have hden : ¬ q ∣ (x : ℚ).den := (GaloisRep.mem_ratLocalizedAt_iff hq (x : ℚ)).mp x.2
  have hden' : ¬ ((q : ℤ) ∣ ((x : ℚ).den : ℤ)) := by exact_mod_cast hden
  obtain ⟨c, t, hct⟩ := (Prime.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hq)).mpr hden'

  refine ⟨(x : ℚ).num * t, ?_⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨x * (c : R q), Subtype.ext ?_⟩
  have hnum : (x : ℚ) * ((x : ℚ).den : ℚ) = (x : ℚ).num := Rat.mul_den_eq_num (x : ℚ)
  have hct' : (c : ℚ) * (q : ℚ) + (t : ℚ) * ((x : ℚ).den : ℚ) = 1 := by exact_mod_cast hct
  push_cast

  have : (x : ℚ) - ((x : ℚ).num : ℚ) * (t : ℚ) = (x : ℚ) * ((c : ℚ) * (q : ℚ) + (t : ℚ) * ((x : ℚ).den : ℚ)) - ((x : ℚ).num : ℚ) * (t : ℚ) := by
    rw [hct', mul_one]
  rw [this, mul_add, ← mul_assoc (x : ℚ) (t : ℚ), mul_comm (x : ℚ) (t : ℚ), mul_assoc (t : ℚ), hnum]
  ring

private theorem intCast_quotient_surjective (I : Ideal (R q)) (hI : Ideal.span {((q : ℕ) : R q)} ≤ I) :
    Function.Surjective (fun n : ℤ => (Ideal.Quotient.mk I (n : R q))) := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨n, hn⟩ := exists_int_sub_mem_span q x
  refine ⟨n, ?_⟩
  rw [eq_comm, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact hI hn

private theorem finite_quotient_maximalIdeal_R [IsLocalRing (R q)] : Finite (R q ⧸ IsLocalRing.maximalIdeal (R q)) := by
  have hq : (q : ℕ).Prime := Fact.out
  haveI : NeZero q := ⟨hq.ne_zero⟩

  have hsurj := intCast_quotient_surjective q (IsLocalRing.maximalIdeal (R q)) (le_of_eq (maximalIdeal_R q).symm)
  let f : ZMod q → R q ⧸ IsLocalRing.maximalIdeal (R q) := fun a => Ideal.Quotient.mk _ ((a.val : ℤ) : R q)
  refine Finite.of_surjective f fun y => ?_
  obtain ⟨n, rfl⟩ := hsurj y
  refine ⟨(n : ZMod q), ?_⟩
  show Ideal.Quotient.mk _ ((((n : ZMod q).val : ℤ) : R q)) = Ideal.Quotient.mk _ (n : R q)
  rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, mem_maximalIdeal_R_iff]
  have hdvd : (q : ℤ) ∣ ((n : ZMod q).val : ℤ) - n := by
    rw [ZMod.val_intCast, Int.emod_def]
    exact ⟨-(n / q), by ring⟩
  obtain ⟨d, hd⟩ := hdvd
  refine ⟨(d : R q), ?_⟩
  have := congrArg (fun z : ℤ => (z : R q)) hd
  push_cast at this
  exact this

private theorem finite_residueField_R [IsLocalRing (R q)] : Finite (IsLocalRing.ResidueField (R q)) :=
  finite_quotient_maximalIdeal_R q

private theorem perfectField_residueField_R [IsLocalRing (R q)] : PerfectField (IsLocalRing.ResidueField (R q)) :=
  haveI := finite_residueField_R q
  PerfectField.ofFinite

private theorem finite_ideal_residueField_R [IsLocalRing (R q)] : Finite (IsLocalRing.maximalIdeal (R q)).ResidueField :=
  haveI := finite_quotient_maximalIdeal_R q
  Finite.of_surjective _ (Ideal.bijective_algebraMap_quotient_residueField (IsLocalRing.maximalIdeal (R q))).2

private theorem perfectField_residue [IsLocalRing (R q)] : PerfectField (IsLocalRing.maximalIdeal (R q)).ResidueField :=
  haveI := finite_ideal_residueField_R q
  PerfectField.ofFinite

omit [Fact q.Prime] in

private theorem eq_zero_of_pow_natCast_smul_eq_zero (M : Type*) [AddCommGroup M] [Module (R q) M]
    (h : ∀ m : M, ((q : ℕ) : R q) • m = 0 → m = 0) : ∀ (n : ℕ) (m : M), ((q : ℕ) : R q) ^ n • m = 0 → m = 0
  | 0, m, hm => by simpa using hm
  | n + 1, m, hm => by
    apply eq_zero_of_pow_natCast_smul_eq_zero M h n
    apply h
    rw [smul_smul, ← pow_succ']
    exact hm

private theorem isTorsionFree_of_natCast_torsionFree (M : Type*) [AddCommGroup M] [Module (R q) M]
    (h : ∀ m : M, ((q : ℕ) : R q) • m = 0 → m = 0) : Module.IsTorsionFree (R q) M := by
  haveI := isDiscreteValuationRing_R q
  refine Module.IsTorsionFree.of_smul_eq_zero fun r m hrm => ?_
  by_cases hr : r = 0
  · exact Or.inl hr
  right
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hr (irreducible_natCast_R q)
  have hqn : ((q : ℕ) : R q) ^ n • m = 0 := by
    have := congrArg (fun z => ((u⁻¹ : (R q)ˣ) : R q) • z) hrm
    simpa [smul_smul, ← mul_assoc] using this
  exact eq_zero_of_pow_natCast_smul_eq_zero q M h n m hqn

private theorem flat_of_natCast_smul_torsionFree (M : Type*) [AddCommGroup M] [Module (R q) M]
    (h : ∀ m : M, ((q : ℕ) : R q) • m = 0 → m = 0) : Module.Flat (R q) M := by
  haveI := isPrincipalIdealRing_R q
  haveI := isTorsionFree_of_natCast_torsionFree q M h
  infer_instance

private theorem flat_of_natCast_torsionFree (S : Type*) [CommRing S] [Algebra (R q) S]
    (h : ∀ s : S, ((q : ℕ) : S) * s = 0 → s = 0) : Module.Flat (R q) S := by
  refine flat_of_natCast_smul_torsionFree q S fun s hs => h s ?_
  rwa [Algebra.smul_def, map_natCast] at hs

omit [Fact q.Prime] in
private theorem charP_quotient_of_natCast_mem (hq : q.Prime) {A : Type*} [CommRing A] (I : Ideal A) (hI : I ≠ ⊤)
    (h : ((q : ℕ) : A) ∈ I) : CharP (A ⧸ I) q := by
  haveI : Nontrivial (A ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  refine (CharP.charP_iff_prime_eq_zero hq).mpr ?_
  rw [← map_natCast (Ideal.Quotient.mk I), Ideal.Quotient.eq_zero_iff_mem]
  exact h

end Base

section Main

variable (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀)

set_option quotPrecheck false in
local notation "𝔸" => ↥(IgusaScheme.chartAlgFin (N₀ * q) q)
set_option quotPrecheck false in
local notation "𝔽" => ↥(modularFunctionFieldFull (N₀ * q))
set_option quotPrecheck false in
set_option hygiene false in
local notation "𝔹" => (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g})

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in
private theorem main (𝔓 : DRModelPackageLevel N₀ q hqN)
    (u : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hu : ((u : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q) :
    ∃ (avoid : (ZMod q)[X]) (_ : avoid ≠ 0) (c₀ : ℤ[X]) (_ : c₀ ≠ 0) (K : ℕ),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod q))) →
        IsCoprime (g.map (Int.castRingHom (ZMod q))) avoid → ¬ g ∣ c₀ →
          Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g}) ∧
          Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g}) ∧
          Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g}) ∧
          1 ≤ Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g}) ∧
          Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval u g}) ≤ K * g.natDegree := by
  classical
  have hqP : q.Prime := Fact.out
  haveI : NeZero q := ⟨hqP.ne_zero⟩
  haveI : IsLocalRing (R q) := GaloisRep.ratLocalizedAt.isLocalRing hqP
  haveI : IsPrincipalIdealRing (R q) := GaloisRep.isPrincipalIdealRing_ratLocalizedAt q
  have hmax : maximalIdeal (R q) = Ideal.span {((q : ℕ) : R q)} :=
    GaloisRep.ratLocalizedAt.maximalIdeal_eq_span_natCast q hqP
  have hqR : ((q : ℕ) : R q) ∈ maximalIdeal (R q) := by rw [hmax]; exact Ideal.mem_span_singleton_self _

  obtain ⟨W, hW₀, hW₁, hne, habove, hcomplete⟩ :=
    ModularCurve.exists_valuationSubring_pair_modularFunctionFieldFull_mul_of_not_dvd N₀ q hqN
  obtain ⟨P, hPmem, hPprime, hPne, hmin⟩ :=
    ModularCurve.DRModelPackageLevel.exists_minimalPrimes_chartAlgFin_span_eq_pair_of_valuationSubring_pair
      N₀ q hqN W hW₀ hW₁ hne habove hcomplete
  haveI := hPprime 0
  haveI := hPprime 1

  have hmemq : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) := by
    have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
      apply IntermediateField.adjoin.mono
      rintro x ⟨d, hd, hdq, rfl⟩
      exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
    exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
  have huF : (u : ↥(modularFunctionFieldFull (N₀ * q))) = ⟨modularUnitSeries q, hmemq⟩ := Subtype.ext hu
  obtain ⟨⟨xu, hxu0, hxu⟩, -, ⟨huW0, huinvW0⟩, ⟨hu'W1, -⟩⟩ :=
    ModularCurve.modularUnitSeries_mem_valuationSubring_pair_of_not_dvd N₀ q hqN hmemq (W 0) (W 1) hW₀ hW₁
  rw [← huF] at huW0 huinvW0 hu'W1
  have hq1 : ∀ i, (W i).valuation ((q : ℕ) : 𝔽) < 1 := fun i => (ValuationSubring.mem_nonunits_iff _).mp (habove i).1
  have hqA : ∀ i, ((q : ℕ) : 𝔸) ∈ P i := fun i =>
    (hPmem i _).2 (by simpa using (habove i).1)
  have huF0 : (u : 𝔽) ≠ 0 := by
    intro h
    apply ModularCurve.modularUnitSeries_ne_zero q
    rw [← hu, h]
    rfl

  have hu0 : u ∉ P 0 := by
    intro h
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp ((hPmem 0 u).mp h)
    have hle : (W 0).valuation (u : 𝔽)⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr huinvW0
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact huF0)] at hle
    exact not_lt.mpr hle hlt
  have hu1 : u ∈ P 1 := by
    refine (hPmem 1 u).mpr ((ValuationSubring.mem_nonunits_iff _).mpr ?_)
    have hq0 : ((q : ℕ) : 𝔽) ≠ 0 := by exact_mod_cast hqP.ne_zero
    have hfac : (u : 𝔽) = ((u : 𝔽) * (((q : ℕ) : 𝔽) ^ 12)⁻¹) * ((q : ℕ) : 𝔽) ^ 12 := by
      rw [inv_mul_cancel_right₀ (pow_ne_zero _ hq0)]
    rw [hfac, map_mul, map_pow]
    have h1 : (W 1).valuation ((u : 𝔽) * (((q : ℕ) : 𝔽) ^ 12)⁻¹) ≤ 1 := ((W 1).valuation_le_one_iff _).mpr hu'W1
    calc (W 1).valuation ((u : 𝔽) * (((q : ℕ) : 𝔽) ^ 12)⁻¹) * (W 1).valuation ((q : ℕ) : 𝔽) ^ 12
        ≤ 1 * (W 1).valuation ((q : ℕ) : 𝔽) ^ 12 := mul_le_mul_left h1 _
      _ = (W 1).valuation ((q : ℕ) : 𝔽) ^ 12 := one_mul _
      _ < 1 := pow_lt_one₀ zero_le' (hq1 1) (by norm_num)

  have hinf : P 0 ⊓ P 1 = Ideal.span {((q : ℕ) : 𝔸)} := by
    have hrad : (Ideal.span {((q : ℕ) : 𝔸)}).IsRadical :=
      (Ideal.isRadical_iff_quotient_reduced _).2
        (ModularCurve.DRModelPackageLevel.isReduced_chartAlgFin_quotient_span_natCast N₀ q hqN 𝔓)
    have h : sInf (Ideal.span {((q : ℕ) : 𝔸)}).minimalPrimes = (Ideal.span {((q : ℕ) : 𝔸)}).radical :=
      Ideal.sInf_minimalPrimes
    rw [hmin, hrad.radical] at h
    simpa [sInf_insert] using h
  have hP0min : P 0 ∈ (Ideal.span {((q : ℕ) : 𝔸)}).minimalPrimes := by rw [hmin]; exact Set.mem_insert _ _

  obtain ⟨avoid₆, havoid₆, hC6⟩ :=
    ModularCurve.DRModelPackageLevel.exists_avoid_forall_formallyUnramified_quotient_quotient_span_aeval
      N₀ q hqN 𝔓 u hu (P 0) hP0min hu0
  obtain ⟨c₀, hc₀0, hunr⟩ :=
    ModularCurve.DRModelPackageLevel.exists_forall_isUnramifiedAt_polynomial_of_aeval_notMem N₀ q hqN u (Or.inl hu)
  obtain ⟨K, hC1⟩ :=
    ModularCurve.DRModelPackageLevel.exists_forall_finite_quotient_span_aeval_and_finrank_le N₀ q hqN u (Or.inl hu)
  refine ⟨Polynomial.X * avoid₆, mul_ne_zero Polynomial.X_ne_zero havoid₆, c₀, hc₀0, K, fun g hg hD hirr hcop hndvd => ?_⟩

  have hcopX : IsCoprime (g.map (Int.castRingHom (ZMod q))) Polynomial.X := hcop.of_mul_right_left
  have hcop6 : IsCoprime (g.map (Int.castRingHom (ZMod q))) avoid₆ := hcop.of_mul_right_right
  have hg0bar : (g.map (Int.castRingHom (ZMod q))).coeff 0 ≠ 0 := fun h =>
    Polynomial.not_isUnit_X (hcopX.isUnit_of_dvd' (Polynomial.X_dvd_iff.2 h) dvd_rfl)
  have hg0p : ¬ (q : ℤ) ∣ g.coeff 0 := by
    intro h; apply hg0bar
    rw [coeff_map, eq_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact h
  haveI : PerfectField (ZMod q) := PerfectField.ofFinite
  have hsep : (g.map (Int.castRingHom (ZMod q))).Separable := PerfectField.separable_of_irreducible hirr
  have hDbar : 0 < (g.map (Int.castRingHom (ZMod q))).natDegree := by rw [hg.natDegree_map]; exact hD

  obtain ⟨hfin, hrank⟩ := hC1 g hg hg0p
  haveI := hfin

  have hcharP1 : CharP (𝔸 ⧸ P 1) q := by
    haveI : Nontrivial (𝔸 ⧸ P 1) := Ideal.Quotient.nontrivial_iff.2 (hPprime 1).ne_top
    have hp0 : ((q : ℕ) : 𝔸 ⧸ P 1) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk (P 1)), Ideal.Quotient.eq_zero_iff_mem]; exact hqA 1
    have hdvd : ringChar (𝔸 ⧸ P 1) ∣ q := (ringChar.spec _ q).1 hp0
    rcases (Nat.dvd_prime hqP).1 hdvd with h1 | hp'
    · exact absurd h1 CharP.ringChar_ne_one
    · have := ringChar.charP (𝔸 ⧸ P 1); rwa [hp'] at this
  have hxz : IsUnit (Ideal.Quotient.mk (P 1) (aeval u g)) := by
    have h1 : Ideal.Quotient.mk (P 1) (aeval u g) = Ideal.Quotient.mk (P 1) (algebraMap ℤ 𝔸 (g.coeff 0)) := by
      rw [← Ideal.Quotient.algebraMap_eq, ← aeval_algebraMap_apply, Ideal.Quotient.algebraMap_eq,
        Ideal.Quotient.eq_zero_iff_mem.2 hu1, aeval_def, eval₂_at_zero]
      exact RingHom.congr_fun (Subsingleton.elim (algebraMap ℤ (𝔸 ⧸ P 1)) ((Ideal.Quotient.mk (P 1)).comp (algebraMap ℤ 𝔸))) _
    rw [h1]
    haveI := hcharP1
    have h2 : Ideal.Quotient.mk (P 1) (algebraMap ℤ 𝔸 (g.coeff 0)) = ZMod.castHom (dvd_refl q) (𝔸 ⧸ P 1) (g.coeff 0 : ZMod q) := by
      rw [map_intCast]
      exact RingHom.congr_fun (Subsingleton.elim ((Ideal.Quotient.mk (P 1)).comp (algebraMap ℤ 𝔸)) (Int.castRingHom _)) _
    rw [h2]
    refine IsUnit.map _ (isUnit_iff_ne_zero.2 ?_)
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]; exact hg0p

  have haev : ∀ {S T : Type} [CommRing S] [CommRing T] [Algebra ℤ S] [Algebra ℤ T] (φ : S →+* T) (y : S) (p : ℤ[X]),
      φ (aeval y p) = aeval (φ y) p := by
    intro S T _ _ _ _ φ y p
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
    congr 1
    exact RingHom.ext_int _ _
  have hcm : ∀ {S : Type} [CommRing S] (f : ℤ →+* S) (y : LaurentSeries ℤ) (p : ℤ[X]),
      ModularCurve.coeffMap f (aeval y p) = aeval (ModularCurve.coeffMap f y) p :=
    fun f y p => haev (ModularCurve.coeffMap f) y p
  have hxu : aeval u g ∉ P 0 := by
    intro h
    have hnu := (hPmem 0 _).mp h
    set zq := ModularCurve.coeffMap (Int.castRingHom (ZMod q)) xu with hzq
    have hz0 : zq ≠ 0 := hxu0
    have hxcoeff : ∀ n : ℤ, ((xu.coeff n : ℤ) : ℚ) = (modularUnitSeries q).coeff n := by
      intro n; rw [hxu, ModularCurve.coeffMap_coeff]; rfl
    have hzord : zq.order = 1 - (q : ℤ) := by
      apply order_eq_of_coeff
      · rw [hzq, ModularCurve.coeffMap_coeff]
        have h1 : xu.coeff (1 - (q : ℤ)) = 1 := by
          have h2 := hxcoeff (1 - (q : ℤ))
          rw [ModularCurve.coeff_modularUnitSeries_self] at h2
          exact_mod_cast h2
        rw [h1, map_one]; exact one_ne_zero
      · intro n hn
        rw [hzq, ModularCurve.coeffMap_coeff]
        have h1 : xu.coeff n = 0 := by
          have h2 := hxcoeff n
          rw [ModularCurve.coeff_modularUnitSeries_of_lt q hn] at h2
          exact_mod_cast h2
        rw [h1, map_zero]
    have hzneg : zq.order < 0 := by rw [hzord]; have := hqP.two_le; omega
    have hgz : ModularCurve.coeffMap (Int.castRingHom (ZMod q)) (aeval xu g) ≠ 0 := by
      rw [hcm, ← hzq]
      have : aeval zq g = aeval zq (g.map (Int.castRingHom (ZMod q))) := by
        rw [aeval_def, aeval_def, Polynomial.eval₂_map]
        congr 1
        exact RingHom.ext_int _ _
      rw [this]
      exact aeval_ne_zero_of_order_neg hz0 hzneg _ (hg.map _) hDbar

    set w : 𝔽 := ((aeval u g : 𝔸) : 𝔽) with hw
    have hcoe : w = aeval (u : 𝔽) g := haev (IgusaScheme.chartAlgFin (N₀ * q) q).val.toRingHom u g
    have hexp : ((aeval (u : 𝔽) g : 𝔽) : LaurentSeries ℚ) = ModularCurve.coeffMap (Int.castRingHom ℚ) (aeval xu g) := by
      rw [hcm, ← hxu, ← hu]
      exact haev (modularFunctionFieldFull (N₀ * q)).toSubfield.subtype (u : 𝔽) g
    have hwL : (w : LaurentSeries ℚ) = ModularCurve.coeffMap (Int.castRingHom ℚ) (aeval xu g) := by rw [hcoe, hexp]
    have hw0 : w ≠ 0 := by
      intro h0
      apply hgz
      have h1 : ModularCurve.coeffMap (Int.castRingHom ℚ) (aeval xu g) = 0 := by rw [← hwL, h0]; rfl
      have h2 : aeval xu g = 0 := by
        ext n
        have h3 : (((aeval xu g).coeff n : ℤ) : ℚ) = 0 := by
          have h4 := congrArg (fun s : LaurentSeries ℚ => s.coeff n) h1
          simpa [ModularCurve.coeffMap_coeff] using h4
        rw [HahnSeries.coeff_zero]
        exact_mod_cast h3
      rw [h2, map_zero]
    have hwL0 : (w : LaurentSeries ℚ) ≠ 0 := fun h1 => hw0 (by exact_mod_cast h1)
    have hinvW : w⁻¹ ∈ W 0 := by
      rw [hW₀]
      refine ⟨1, aeval xu g, hgz, ?_⟩
      have hval : ((w⁻¹ : 𝔽) : LaurentSeries ℚ) = ((w : 𝔽) : LaurentSeries ℚ)⁻¹ := map_inv₀ (modularFunctionFieldFull (N₀ * q)).val w
      rw [map_one, hval, hwL, inv_mul_cancel₀ (hwL ▸ hwL0 :)]
    have hlt := (ValuationSubring.mem_nonunits_iff _).mp hnu
    have hle : (W 0).valuation w⁻¹ ≤ 1 := ((W 0).valuation_le_one_iff _).mpr hinvW
    rw [map_inv₀, inv_le_one₀ (by rw [Valuation.pos_iff]; exact hw0)] at hle
    exact not_lt.mpr hle hlt

  have hnzd : ∀ y : 𝔸, aeval u g * y ∈ Ideal.span {((q : ℕ) : 𝔸)} → y ∈ Ideal.span {((q : ℕ) : 𝔸)} :=
    fun y hy => mem_span_of_mul_mem hinf hxz hxu hy
  have htf : ∀ b : 𝔹, ((q : ℕ) : 𝔹) * b = 0 → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    rw [← map_natCast (Ideal.Quotient.mk _), ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at hb
    obtain ⟨y, hy⟩ := hb

    have hyq : y ∈ Ideal.span {((q : ℕ) : 𝔸)} := hnzd y (Ideal.mem_span_singleton.2 ⟨a, hy.symm⟩)
    obtain ⟨y', rfl⟩ := Ideal.mem_span_singleton.1 hyq
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
    refine ⟨y', ?_⟩
    have hqne : ((q : ℕ) : 𝔸) ≠ 0 := by
      intro h0
      have h1 := congrArg (fun x : 𝔸 => (x : 𝔽)) h0
      simp only [ZeroMemClass.coe_zero] at h1
      exact hqP.ne_zero (by exact_mod_cast h1)
    have : ((q : ℕ) : 𝔸) * a = ((q : ℕ) : 𝔸) * (aeval u g * y') := by
      rw [hy]; ring
    exact mul_left_cancel₀ hqne this
  haveI hflat : Module.Flat (R q) 𝔹 := flat_of_natCast_torsionFree q 𝔹 htf
  haveI hfree : Module.Free (R q) 𝔹 := Module.free_of_flat_of_isLocalRing

  have hirrZ : Irreducible g := hg.irreducible_of_irreducible_map (Int.castRingHom (ZMod q)) _ hirr
  have hirrQ : Irreducible (g.map (Int.castRingHom ℚ)) := (hg.irreducible_iff_irreducible_map_fraction_map).1 hirrZ
  haveI : IsFractionRing (R q) ℚ := isFractionRing_R q
  obtain ⟨hnt, hFU⟩ := hC6 g hDbar hsep hcop6
  have hIdeal : Ideal.span {((q : ℕ) : 𝔸)} ⊔ Ideal.span {aeval u g} = P 0 ⊔ Ideal.span {aeval u g} :=
    span_sup_span_eq hinf hxz
  have hK : (maximalIdeal (R q)).map (algebraMap (R q) 𝔸) ⊔ Ideal.span {aeval u g} = P 0 ⊔ Ideal.span {aeval u g} := by
    rw [hmax, Ideal.map_span, Set.image_singleton, map_natCast]; exact hIdeal
  have hF := formallyUnramified_fibre (maximalIdeal (R q)) (Ideal.span {aeval u g}) _ hK hFU
  haveI : (Ideal.span {(q : ℤ)}).IsPrime :=
    (Ideal.span_singleton_prime (by exact_mod_cast hqP.ne_zero)).2 (Nat.prime_iff_prime_int.1 hqP)
  haveI := GaloisRep.isLocalization_ratLocalizedAt hqP
  haveI : Algebra.EssFiniteType ℤ (R q) := Algebra.EssFiniteType.of_isLocalization (R q) (Ideal.span {(q : ℤ)}).primeCompl

  haveI : Algebra.FinitePresentation (R q) 𝔹 :=
    (Algebra.FinitePresentation.of_finiteType (R := R q) (A := 𝔹)).mp inferInstance
  obtain ⟨c, hc0, hcm, het⟩ := exists_etale_localizationAway_of_forall_isUnramifiedAt (R₀ := R q) (S := 𝔹)
    (fun 𝔮 _ h𝔮 => isUnramifiedAt_of_comap_eq_botS (R := R q) (A := 𝔸) u g c₀ hg hirrQ hndvd hunr 𝔹
      Ideal.Quotient.mk_surjective (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)) 𝔮 h𝔮)
    (maximalIdeal (R q))
    (fun 𝔮 h𝔮P h𝔮 => by
      haveI := h𝔮P
      haveI : 𝔮.LiesOver (maximalIdeal (R q)) := ⟨h𝔮.symm⟩
      exact isUnramifiedAt_of_fibre q (maximalIdeal (R q)) hqR (perfectField_residue q) hF 𝔮)
  have hcu : IsUnit c := by
    by_contra hc
    exact hcm ((IsLocalRing.mem_maximalIdeal c).2 hc)
  have hEt : Algebra.Etale (R q) 𝔹 := etale_of_etale_localizationAway_of_isUnit c hcu het

  haveI : Nontrivial 𝔹 :=
    (Ideal.Quotient.factor (le_sup_right : Ideal.span {aeval u g} ≤ P 0 ⊔ Ideal.span {aeval u g})).domain_nontrivial
  have hpos : 0 < Module.finrank (R q) 𝔹 := (Module.finrank_pos_iff_of_free (R q) 𝔹).2 inferInstance
  exact ⟨hfin, hEt, hfree, hpos, hrank⟩

end Main

end N2Body

open N2Body in
theorem solution
    (N₀ q : ℕ) [NeZero N₀] [Fact q.Prime] (hqN : ¬ q ∣ N₀) (𝔓 : DRModelPackageLevel N₀ q hqN)
    (v : ↥(IgusaScheme.chartAlgFin (N₀ * q) q))
    (hv : ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q ∨
      ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = (q : LaurentSeries ℚ) ^ 12 * (modularUnitSeries q)⁻¹) :
    ∃ (avoid : (ZMod q)[X]) (_ : avoid ≠ 0) (c₀ : ℤ[X]) (_ : c₀ ≠ 0) (K : ℕ),
      ∀ g : ℤ[X], g.Monic → 1 ≤ g.natDegree → Irreducible (g.map (Int.castRingHom (ZMod q))) →
        IsCoprime (g.map (Int.castRingHom (ZMod q))) avoid → ¬ g ∣ c₀ →
          Module.Finite (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Algebra.Etale (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.Free (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          1 ≤ Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ∧
          Module.finrank (R q) (↥(IgusaScheme.chartAlgFin (N₀ * q) q) ⧸ Ideal.span {Polynomial.aeval v g}) ≤ K * g.natDegree := by
  classical
  rcases hv with hv | hv
  · exact N2Body.main N₀ q hqN 𝔓 v hv
  · have hqP : q.Prime := Fact.out
    haveI : NeZero q := ⟨hqP.ne_zero⟩
    have hmemq : modularUnitSeries q ∈ modularFunctionFieldFull (N₀ * q) := by
      have hle : modularFunctionFieldFull q ≤ modularFunctionFieldFull (N₀ * q) := by
        apply IntermediateField.adjoin.mono
        rintro x ⟨d, hd, hdq, rfl⟩
        exact ⟨d, hd, hdq.trans (dvd_mul_left q N₀), rfl⟩
      exact hle (ModularCurve.modularUnitSeries_mem_modularFunctionFieldFull q)
    obtain ⟨hu₀A, -⟩ := ModularCurve.DRModelPackageLevel.modularUnitSeries_mem_chartAlgFin_mul N₀ q hqN hmemq
    let u₀ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q) := ⟨⟨modularUnitSeries q, hmemq⟩, hu₀A⟩
    have hu₀ : ((u₀ : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) = modularUnitSeries q := rfl

    have hθ : 𝔓.theta u₀ = v := by
      apply Subtype.ext
      apply Subtype.ext
      show (((𝔓.theta u₀ : ↥(IgusaScheme.chartAlgFin (N₀ * q) q)) : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ) =
        ((v : ↥(modularFunctionFieldFull (N₀ * q))) : LaurentSeries ℚ)
      rw [𝔓.theta_spec, hv]
      show ((atkinLehnerInvolutionFull N₀ q ⟨modularUnitSeries q, hmemq⟩ : ↥(modularFunctionFieldFull (N₀ * q))) :
          LaurentSeries ℚ) = _
      rw [ModularCurve.coe_atkinLehnerInvolutionFull_modularUnitSeries_of_not_dvd N₀ q hqN hmemq, ← HahnSeries.C_mul_eq_smul,
        map_pow, map_natCast]
    obtain ⟨avoid, havoid, c₀, hc₀, K, hmain⟩ := N2Body.main N₀ q hqN 𝔓 u₀ hu₀
    refine ⟨avoid, havoid, c₀, hc₀, K, fun g hg hD hirr hcop hndvd => ?_⟩
    obtain ⟨hfin, hEt, hfree, hpos, hrank⟩ := hmain g hg hD hirr hcop hndvd
    have hθg : 𝔓.theta (aeval u₀ g) = aeval v g := by
      rw [← hθ]
      show 𝔓.theta.toRingEquiv.toRingHom (aeval u₀ g) = aeval (𝔓.theta.toRingEquiv.toRingHom u₀) g
      rw [aeval_def, aeval_def, Polynomial.hom_eval₂]
      congr 1
      exact RingHom.ext_int _ _
    have hJ : Ideal.span {aeval v g} = (Ideal.span {aeval u₀ g}).map (𝔓.theta : _ →+* _) := by
      rw [Ideal.map_span, Set.image_singleton]
      exact congrArg (fun x => Ideal.span {x}) hθg.symm
    haveI := hfin; haveI := hEt; haveI := hfree
    have hrk := N2Body.finrank_quotient_of_algEquiv (R₀ := R q) (Ideal.span {aeval u₀ g}) (Ideal.span {aeval v g}) 𝔓.theta hJ
    refine ⟨N2Body.finite_quotient_of_algEquiv (R₀ := R q) (Ideal.span {aeval u₀ g}) (Ideal.span {aeval v g}) 𝔓.theta hJ,
      N2Body.etale_quotient_of_algEquiv (R₀ := R q) (Ideal.span {aeval u₀ g}) (Ideal.span {aeval v g}) 𝔓.theta hJ,
      N2Body.free_quotient_of_algEquiv (R₀ := R q) (Ideal.span {aeval u₀ g}) (Ideal.span {aeval v g}) 𝔓.theta hJ,
      ?_, ?_⟩
    · rw [hrk]; exact hpos
    · rw [hrk]; exact hrank

end

end S_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_exists_finite_etale_quotient_span_aeval (solution)
