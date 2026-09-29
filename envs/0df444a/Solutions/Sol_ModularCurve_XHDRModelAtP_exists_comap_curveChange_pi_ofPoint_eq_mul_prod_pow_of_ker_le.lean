-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0c4d716c-887c-5aea-a5d4-6bdb9d18d4b9

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_pi
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_flat_subschemeIota_mul_comp_of_isInvertible
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_ofPoint_of_range_subset
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_schemeHomOver_comp_one_frob_placeOfPoint_eq_of_comp_pi_eq_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
p2m_attr_erase "instance" "kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero"
p2m_attr_erase "simp" "RegularLocalRingQuotientAscent.dualNumberFst_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single"
p2m_attr_erase "simp" "ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel AlgebraicGeometry.RelPicard

open scoped MatrixGroups

namespace HPSplitTools

open AlgebraicGeometry

def IsSaturated {R : Type*} [CommRing R] (ϖ : R) (J : Ideal R) : Prop := ∀ f : R, ϖ * f ∈ J → f ∈ J

theorem IsSaturated.pow_mul_mem_iff {R : Type*} [CommRing R] {ϖ : R} {J : Ideal R} (hJ : IsSaturated ϖ J)
    (n : ℕ) (f : R) : ϖ ^ n * f ∈ J ↔ f ∈ J := by
  induction n with
  | zero => rw [pow_zero, one_mul]
  | succ n ih =>
    constructor
    · intro h
      rw [pow_succ, mul_comm (ϖ ^ n) ϖ, mul_assoc] at h
      exact ih.1 (hJ _ h)
    · intro h
      exact J.mul_mem_left _ h

theorem le_of_isSaturated_of_map_le {R : Type*} [CommRing R] (ϖ : R) {I J : Ideal R}
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away ϖ S]
    (hJ : IsSaturated ϖ J) (hIJ : I.map (algebraMap R S) ≤ J.map (algebraMap R S)) : I ≤ J := by
  intro f hf
  have hfS : algebraMap R S f ∈ J.map (algebraMap R S) := hIJ (Ideal.mem_map_of_mem _ hf)
  rw [IsLocalization.mem_map_algebraMap_iff (Submonoid.powers ϖ) S] at hfS
  obtain ⟨⟨⟨j, hj⟩, ⟨s, hs⟩⟩, h⟩ := hfS
  obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hs

  simp only at h
  rw [← map_mul] at h
  obtain ⟨⟨c, hc⟩, hc'⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers ϖ) S).1 h
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).1 hc
  simp only at hc'

  have hmem : ϖ ^ (k + m) * f ∈ J := by
    have : ϖ ^ (k + m) * f = ϖ ^ k * (f * ϖ ^ m) := by ring
    rw [this, hc']
    exact J.mul_mem_left _ hj
  exact (hJ.pow_mul_mem_iff (k + m) f).1 hmem

theorem eq_of_isSaturated_of_map_eq {R : Type*} [CommRing R] (ϖ : R) {I J : Ideal R}
    (S : Type*) [CommRing S] [Algebra R S] [IsLocalization.Away ϖ S]
    (hI : IsSaturated ϖ I) (hJ : IsSaturated ϖ J)
    (hIJ : I.map (algebraMap R S) = J.map (algebraMap R S)) : I = J :=
  le_antisymm (le_of_isSaturated_of_map_le ϖ S hJ hIJ.le) (le_of_isSaturated_of_map_le ϖ S hI hIJ.ge)

theorem isSaturated_iff_forall_mk_eq_zero {R : Type*} [CommRing R] (ϖ : R) (J : Ideal R) :
    IsSaturated ϖ J ↔ ∀ f : R, (Ideal.Quotient.mk J ϖ) * Ideal.Quotient.mk J f = 0 → Ideal.Quotient.mk J f = 0 := by
  simp only [IsSaturated, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]

theorem isSaturated_span_singleton_of_mem_nonZeroDivisors {R : Type*} [CommRing R] {ϖ g : R}
    (hϖ : ϖ ∈ nonZeroDivisors R)
    (hg : Ideal.Quotient.mk (Ideal.span {ϖ}) g ∈ nonZeroDivisors (R ⧸ Ideal.span ({ϖ} : Set R))) :
    IsSaturated ϖ (Ideal.span {g}) := by
  intro f hf
  obtain ⟨h, hh⟩ := Ideal.mem_span_singleton'.1 hf

  have h0 : Ideal.Quotient.mk (Ideal.span {ϖ}) h * Ideal.Quotient.mk (Ideal.span {ϖ}) g = 0 := by
    rw [← map_mul, hh, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self ϖ)
  have hh0 : Ideal.Quotient.mk (Ideal.span {ϖ}) h = 0 := by
    first
      | exact (mem_nonZeroDivisors_iff.mp hg).1 _ h0
      | exact (mem_nonZeroDivisors_iff.mp hg) _ h0
      | exact (mem_nonZeroDivisors_iff_right.mp hg) _ h0
  obtain ⟨h₁, hh₁⟩ := Ideal.mem_span_singleton'.1 ((Ideal.Quotient.eq_zero_iff_mem).1 hh0)

  have key : ϖ * f = ϖ * (h₁ * g) := by rw [← hh, ← hh₁]; ring
  have hf' : f = h₁ * g := by
    have := sub_eq_zero.2 key
    rw [← mul_sub] at this
    have h2 := (mem_nonZeroDivisors_iff_right.mp hϖ) _ (by rwa [mul_comm] at this)
    exact sub_eq_zero.1 h2
  rw [hf']
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self g)

theorem idealSheafData_eq_of_saturated {X : Scheme} {A : Type*} [CommRing A] (ϖ : A)
    (alg : ∀ U : X.affineOpens, A →+* Γ(X, U))
    {I J : X.IdealSheafData}
    (hI : ∀ U : X.affineOpens, IsSaturated (alg U ϖ) (I.ideal U))
    (hJ : ∀ U : X.affineOpens, IsSaturated (alg U ϖ) (J.ideal U))
    (hgen : ∀ U : X.affineOpens, (I.ideal U).map (algebraMap Γ(X, U) (Localization.Away (alg U ϖ))) =
      (J.ideal U).map (algebraMap Γ(X, U) (Localization.Away (alg U ϖ)))) : I = J := by
  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  exact eq_of_isSaturated_of_map_eq (alg U ϖ) (Localization.Away (alg U ϖ)) (hI U) (hJ U) (hgen U)

end HPSplitTools

namespace HPSplitTools

open scoped nonZeroDivisors

theorem valuation_natCast_eq_one_of_not_dvd (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [hp : Fact p.Prime]
    (hA : A.LiesOverPrime p) (n : ℕ) (hn : ¬ p ∣ n) : A.valuation ((n : AlgebraicClosure ℚ)) = 1 := by
  have hle : A.valuation ((n : AlgebraicClosure ℚ)) ≤ 1 := by
    simpa using A.valuation_le_one (n : A)
  refine le_antisymm hle (not_lt.1 fun hlt => ?_)

  have hcop : Nat.Coprime n p := (Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hn))
  have hp1 : A.valuation ((p : AlgebraicClosure ℚ)) < 1 := (A.mem_nonunits_iff).1 hA
  have hbez := Nat.gcd_eq_gcd_ab n p
  rw [Nat.Coprime.gcd_eq_one hcop] at hbez

  have h1 : (1 : AlgebraicClosure ℚ) = (n : AlgebraicClosure ℚ) * (Nat.gcdA n p : AlgebraicClosure ℚ) +
      (p : AlgebraicClosure ℚ) * (Nat.gcdB n p : AlgebraicClosure ℚ) := by
    have := congrArg (fun z : ℤ => (z : AlgebraicClosure ℚ)) hbez
    push_cast at this
    exact this
  have hva : A.valuation ((Nat.gcdA n p : AlgebraicClosure ℚ)) ≤ 1 := by
    simpa using A.valuation_le_one ((Nat.gcdA n p : ℤ) : A)
  have hvb : A.valuation ((Nat.gcdB n p : AlgebraicClosure ℚ)) ≤ 1 := by
    simpa using A.valuation_le_one ((Nat.gcdB n p : ℤ) : A)
  have : A.valuation (1 : AlgebraicClosure ℚ) < 1 := by
    rw [h1]
    refine lt_of_le_of_lt (Valuation.map_add _ _ _) (max_lt ?_ ?_)
    · rw [Valuation.map_mul]
      calc A.valuation (n : AlgebraicClosure ℚ) * A.valuation (Nat.gcdA n p : AlgebraicClosure ℚ)
          ≤ A.valuation (n : AlgebraicClosure ℚ) * 1 := mul_le_mul_right hva _
        _ < 1 := by rw [mul_one]; exact hlt
    · rw [Valuation.map_mul]
      calc A.valuation (p : AlgebraicClosure ℚ) * A.valuation (Nat.gcdB n p : AlgebraicClosure ℚ)
          ≤ A.valuation (p : AlgebraicClosure ℚ) * 1 := mul_le_mul_right hvb _
        _ < 1 := by rw [mul_one]; exact hp1
  rw [Valuation.map_one] at this
  exact lt_irrefl _ this

theorem away_natCast_of_liesOverPrime (A : ValuationSubring (AlgebraicClosure ℚ)) (p : ℕ) [hp : Fact p.Prime]
    (hA : A.LiesOverPrime p) : IsLocalization.Away ((p : ℕ) : A) (AlgebraicClosure ℚ) := by
  refine IsLocalization.Away.mk _ ?_ ?_ ?_
  · rw [map_natCast]
    exact isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 hp.out.ne_zero)
  · intro z

    have hz : IsIntegral ℚ z := ((AlgebraicClosure.isAlgebraic ℚ).isAlgebraic z).isIntegral
    obtain ⟨⟨m, hm⟩, hint⟩ := IsIntegral.exists_multiple_integral_of_isLocalization ℤ⁰ (Rₘ := ℚ) z hz
    have hm0 : m ≠ 0 := nonZeroDivisors.ne_zero hm

    change IsIntegral ℤ ((m : ℤ) • z) at hint
    rw [zsmul_eq_mul] at hint
    have hintA : IsIntegral A ((m : AlgebraicClosure ℚ) * z) := by
      obtain ⟨f, hf, hfz⟩ := hint
      refine ⟨f.map (Int.castRingHom A), hf.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      have hcomp : (algebraMap (↥A) (AlgebraicClosure ℚ)).comp (Int.castRingHom ↥A) = algebraMap ℤ (AlgebraicClosure ℚ) :=
        RingHom.ext_int _ _
      rw [hcomp]
      exact hfz
    obtain ⟨w, hw⟩ := IsIntegrallyClosed.isIntegral_iff.mp hintA

    obtain ⟨e, n', hn', hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Int.natAbs_ne_zero.2 hm0) p hp.out.ne_one
    have hn'0 : n' ≠ 0 := by rintro rfl; exact hm0 (Int.natAbs_eq_zero.1 (by simpa using hfac))

    have hvn : A.valuation ((n' : AlgebraicClosure ℚ)) = 1 := valuation_natCast_eq_one_of_not_dvd A p hA n' hn'
    have hn'mem : (n' : AlgebraicClosure ℚ) ∈ A := by simpa using (n' : A).2
    have hunit : IsUnit (⟨(n' : AlgebraicClosure ℚ), hn'mem⟩ : A) :=
      (A.valuation_eq_one_iff ⟨(n' : AlgebraicClosure ℚ), hn'mem⟩).2 hvn
    obtain ⟨un, hun⟩ := hunit

    set sgn : ℤ := Int.sign m with hsgn
    have hms : (m : AlgebraicClosure ℚ) = (sgn : AlgebraicClosure ℚ) * (p : AlgebraicClosure ℚ) ^ e * (n' : AlgebraicClosure ℚ) := by
      have : (m : ℤ) = sgn * (m.natAbs : ℤ) := (Int.sign_mul_natAbs m).symm
      rw [this, hfac]; push_cast; ring
    have hsu : (sgn : AlgebraicClosure ℚ) * (sgn : AlgebraicClosure ℚ) = 1 := by
      have : sgn * sgn = 1 := by
        rcases lt_or_gt_of_ne hm0 with h | h
        · simp [hsgn, Int.sign_eq_neg_one_of_neg h]
        · simp [hsgn, Int.sign_eq_one_of_pos h]
      exact_mod_cast this
    refine ⟨e, w * (sgn : A) * ((un⁻¹ : Aˣ) : A), ?_⟩

    have hn'K : (n' : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.2 hn'0
    have hinv : (((un⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) = ((n' : AlgebraicClosure ℚ))⁻¹ := by
      have h1 : (((un⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ) * (n' : AlgebraicClosure ℚ) = 1 := by
        have := congrArg (fun x : A => (x : AlgebraicClosure ℚ)) (un.inv_mul)
        beta_reduce at this
        rw [hun] at this
        simpa using this
      exact eq_inv_of_mul_eq_one_left h1
    simp only [map_natCast, map_mul, map_intCast]
    show z * (p : AlgebraicClosure ℚ) ^ e = (w : AlgebraicClosure ℚ) * (sgn : AlgebraicClosure ℚ) * (((un⁻¹ : Aˣ) : A) : AlgebraicClosure ℚ)
    rw [hinv]
    have hwz : (w : AlgebraicClosure ℚ) = (m : AlgebraicClosure ℚ) * z := hw
    rw [hwz, hms]
    field_simp
    ring_nf
    rw [show (sgn : AlgebraicClosure ℚ) ^ 2 = 1 by rw [sq, hsu]]
    ring
  · intro a b h
    exact ⟨0, by rw [pow_zero, one_mul, one_mul]; exact Subtype.ext h⟩

end HPSplitTools

set_option maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    [IsSeparated (toBase p (ΓM M H) hj)] [IsSeparated (toBase p (ΓN p M H hpM) hj)]

    (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
    (hu : Spec.map (CommRingCat.ofHom A.subtype) ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
    (husm : Set.range u.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
    (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
    (huκ₁ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
    (huκ₂ : uκ ≫ pullback.snd _ _ = 𝟙 _)
    (P : closedPoints (𝔛.Mfib A hA ρ hρ).C)
    (hP : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A)))
    (hP₀ : ∀ n : ↥(pullback (𝔛.comp A hA ρ hρ 0) (𝔛.comp A hA ρ hρ 1)),
      (𝔛.Mfib A hA ρ hρ).placeOfPoint P ≠ 𝔛.placeOn0 A hA ρ hρ n) :
    ∃ (k : ℕ) (u' : Fin k → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)) (e : Fin k → ℕ),

      (∀ j, 0 < e j) ∧ ∑ j, e j = p ∧

      (∀ j, ∃ y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _},
        Spec.map (CommRingCat.ofHom A.subtype) ≫ (u' j).1 = y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ∧ y' ≠ y) ∧
      (∀ j, (u' j).1 ≫ 𝔛.π.1 = u.1 ≫ 𝔛.π.1) ∧
      (∀ j, Set.range (u' j).1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj))) ∧
      (∀ j, ∃ uκ' : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ),
        uκ' ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (u' j).1 ∧
        uκ' ≫ pullback.snd _ _ = 𝟙 _ ∧
        ∃ P' : closedPoints (𝔛.Mfib A hA ρ hρ).C,
          (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 1).base P'.1 = uκ'.base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
          qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P') =
            (𝔛.Mfib A hA ρ hρ).placeOfPoint P) ∧

      (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2))).I.comap
          (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) =
        (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j) := by
  classical
  obtain ⟨k, u', e, hepos, hesum, hy', hπ', husm', huκ', hgenrk, hgenid⟩ :=
    ModularCurve.XHDRModelAtP.exists_sections_comap_genericFibre_ofPoint_pi_eq_mul_prod_pow p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ y u hu husm uκ huκ₁ huκ₂ P hP hP₀
  obtain ⟨hπfin, hπlfp, hπflat, hπrk⟩ := ModularCurve.XHDRModelAtP.isFinite_flat_finrank_pi p M H hpM hpM2 hHp hj 𝔛
  haveI := hπfin; haveI := hπlfp; haveI := hπflat
  refine ⟨k, u', e, hepos, hesum, hy', hπ', husm', huκ', ?_⟩

  set XA := pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) with hXA
  set IL := (RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2))).I.comap
          (curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ))) with hIL
  set IR := (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j) with hIR

  haveI hAway : IsLocalization.Away ((p : ℕ) : ↥A) (AlgebraicClosure ℚ) :=
    HPSplitTools.away_natCast_of_liesOverPrime A p hA
  have hφ : IsOpenImmersion (Spec.map (CommRingCat.ofHom A.subtype)) :=
    IsOpenImmersion.of_isLocalization (R := ↥A) (S := AlgebraicClosure ℚ) ((p : ℕ) : ↥A)
  have HGEN : Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρ) =
      Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ]
  set jbar := mapOnProdOver (toBase p (ΓM M H) hj) (g' := Spec.map (CommRingCat.ofHom ρ))
      (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (Spec.map (CommRingCat.ofHom A.subtype)) HGEN with hjbar
  have hsq := isPullback_mapOnProdOver (toBase p (ΓM M H) hj) (g' := Spec.map (CommRingCat.ofHom ρ))
      (g := Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))
      (Spec.map (CommRingCat.ofHom A.subtype)) HGEN
  haveI hjopen : IsOpenImmersion jbar := MorphismProperty.of_isPullback hsq.flip hφ

  have hφrange : Set.range (Spec.map (CommRingCat.ofHom A.subtype)).base =
      ((PrimeSpectrum.basicOpen ((p : ℕ) : ↥A)) : Set (PrimeSpectrum ↥A)) := by
    rw [← PrimeSpectrum.localization_away_comap_range (AlgebraicClosure ℚ) ((p : ℕ) : ↥A), Spec.map_base]
    rfl
  have hjrange : jbar.opensRange = XA.basicOpen ((p : ℕ) : Γ(XA, ⊤)) := by
    apply TopologicalSpace.Opens.ext
    rw [Scheme.Hom.coe_opensRange]

    have hr : Set.range jbar.base =
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))).base ⁻¹'
          Set.range (Spec.map (CommRingCat.ofHom A.subtype)).base := by
      have e1 : jbar = hsq.isoPullback.hom ≫ pullback.fst _ _ := (hsq.isoPullback_hom_fst).symm
      rw [← Scheme.Pullback.range_fst, e1]
      simp only [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp]
      rw [Set.range_comp, Set.range_eq_univ.2 ?_, Set.image_univ]
      exact (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hsq.isoPullback)).surjective
    rw [hr, hφrange]
    have e2 : XA.basicOpen ((p : ℕ) : Γ(XA, ⊤)) =
        (pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ))) ⁻¹ᵁ
          ((Spec (CommRingCat.of ↥A)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of ↥A)).inv ((p : ℕ) : ↥A))) := by
      rw [Scheme.preimage_basicOpen, map_natCast, ← Scheme.Hom.appTop, map_natCast]
      first
        | rfl
        | simp only [hXA]
    have e3 := AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of ↥A) ((p : ℕ) : ↥A)
    rw [e2, ← e3]
    rfl

  have hGEN : ∀ U : XA.affineOpens,
      IL.ideal (XA.affineBasicOpen ((p : ℕ) : Γ(XA, U))) = IR.ideal (XA.affineBasicOpen ((p : ℕ) : Γ(XA, U))) := by
    intro U
    set W := XA.affineBasicOpen ((p : ℕ) : Γ(XA, U)) with hW
    have hWle : (W : XA.Opens) ≤ jbar.opensRange := by
      rw [hjrange, hW]
      show XA.basicOpen ((p : ℕ) : Γ(XA, U)) ≤ XA.basicOpen ((p : ℕ) : Γ(XA, ⊤))
      have : ((p : ℕ) : Γ(XA, U)) = (XA.presheaf.map (homOfLE le_top).op).hom ((p : ℕ) : Γ(XA, ⊤)) := by
        rw [map_natCast]
      rw [this, Scheme.basicOpen_res]
      exact inf_le_right
    let W' : (pullback (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).affineOpens :=
      ⟨jbar ⁻¹ᵁ W, W.2.preimage_of_isOpenImmersion jbar hWle⟩
    have himg : jbar ''ᵁ (W' : (pullback (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).Opens) = W := by
      show jbar ''ᵁ jbar ⁻¹ᵁ (W : XA.Opens) = W
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.2 hWle]
    have hWeq : (⟨jbar ''ᵁ (W' : (pullback (toBase p (ΓM M H) hj)
        (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ))))).Opens),
        W'.2.image_of_isOpenImmersion jbar⟩ : XA.affineOpens) = W := Subtype.ext himg
    have h1 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion IL jbar W'
    have h2 := Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion IR jbar W'
    have h12 : (IL.comap jbar).ideal W' = (IR.comap jbar).ideal W' := by
      have := hgenid
      try simp only [← hIL, ← hIR, ← hjbar] at this
      rw [this]
    rw [h1, h2] at h12
    have h3 := Ideal.comap_injective_of_surjective _ (ConcreteCategory.bijective_of_isIso (jbar.appIso W').inv).surjective h12
    have key : ∀ V : XA.affineOpens, V = W → IL.ideal V = IR.ideal V → IL.ideal W = IR.ideal W := by
      rintro V rfl h; exact h
    exact key _ hWeq h3

  have hSR : ∀ U : XA.affineOpens, HPSplitTools.IsSaturated ((p : ℕ) : Γ(XA, U)) (IR.ideal U) := by
    set qA := pullback.snd (toBase p (ΓM M H) hj) (Spec.map (CommRingCat.ofHom ρ)) with hqA

    let PK : XA.IdealSheafData → Prop := fun K => K.IsInvertible ∧ Flat (K.subschemeι ≫ qA)
    have hsec : ∀ (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj)),
        Set.range s.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)) →
        PK (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) s.1 s.2).I := by
      intro s hs
      refine ⟨?_, ?_⟩
      · exact AlgebraicGeometry.RelEffCartierDiv.isInvertible_I_ofPoint_of_range_subset (toBase p (ΓM M H) hj)
          𝔛.smoothLocus (Spec.map (CommRingCat.ofHom ρ)) s.1 s.2 hs
      · haveI : IsIso ((RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) s.1 s.2).I.subschemeι ≫ qA) :=
          RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one _
        infer_instance
    have hmul : ∀ K L : XA.IdealSheafData, PK K → PK L → PK (K * L) := by
      rintro K L ⟨hKi, hKf⟩ ⟨hLi, hLf⟩
      haveI := hKf; haveI := hLf
      exact ⟨hKi.mul hLi, AlgebraicGeometry.Scheme.IdealSheafData.flat_subschemeIota_mul_comp_of_isInvertible qA K L hKi⟩
    have hpow : ∀ K : XA.IdealSheafData, PK K → ∀ n : ℕ, 0 < n → PK (K ^ n) := by
      intro K hK n hn
      induction n with
      | zero => exact absurd hn (lt_irrefl 0)
      | succ n ih =>
        rcases Nat.eq_zero_or_pos n with h0 | hpos
        · subst h0; simpa using hK
        · rw [pow_succ]; exact hmul _ _ (ih hpos) hK
    have hPIR : PK IR := by
      have hu0 := hsec u husm
      have step : ∀ (S : Finset (Fin k)), PK ((RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) u.1 u.2).I *
          ∏ j ∈ S, (RelEffCartierDiv.ofPoint (toBase p (ΓM M H) hj) (u' j).1 (u' j).2).I ^ (e j)) := by
        intro S
        induction S using Finset.induction_on with
        | empty => simpa using hu0
        | insert a S ha ih =>
          rw [Finset.prod_insert ha, mul_left_comm]
          exact hmul _ _ (hpow _ (hsec (u' a) (husm' a)) (e a) (hepos a)) ih
      simpa [hIR] using step Finset.univ

    obtain ⟨-, hRflat⟩ := hPIR
    intro U f hf
    set ιR := IR.subschemeι with hιR
    have hker : IR = ιR.ker := (Scheme.IdealSheafData.ker_subschemeι IR).symm
    rw [hker, Scheme.Hom.ker_apply, RingHom.mem_ker, map_mul, map_natCast] at hf
    rw [hker, Scheme.Hom.ker_apply, RingHom.mem_ker]
    set gR : IR.subscheme ⟶ Spec (CommRingCat.of ↥A) := ιR ≫ qA with hgR
    haveI hgRflat : Flat gR := hRflat
    let W : (IR.subscheme).affineOpens := ⟨ιR ⁻¹ᵁ U, U.2.preimage ιR⟩
    have hWflat : (gR.appLE ⊤ W le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) gR hgRflat ⟨⊤, isAffineOpen_top _⟩ W le_top
    have hpA : ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) ∈ nonZeroDivisors Γ(Spec (CommRingCat.of ↥A), ⊤) := by
      have eA := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).commRingCatIsoToRingEquiv
      haveI : IsDomain Γ(Spec (CommRingCat.of ↥A), ⊤) := MulEquiv.isDomain (↥A) eA.toMulEquiv
      refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
      have := congrArg eA h0
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this
    letI := (gR.appLE ⊤ W le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Spec (CommRingCat.of ↥A), ⊤) Γ(IR.subscheme, W) := hWflat
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(IR.subscheme, W)) hpA
    have key : ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) • (ιR.app U).hom f =
        ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) • (0 : Γ(IR.subscheme, W)) := by
      rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
      exact hf
    exact hreg key

  have hSL : ∀ U : XA.affineOpens, HPSplitTools.IsSaturated ((p : ℕ) : Γ(XA, U)) (IL.ideal U) := by
    intro U f hf
    set Dv := RelEffCartierDiv.ofPoint (toBase p (ΓN p M H hpM) hj) (u.1 ≫ 𝔛.π.1)
          ((Category.assoc _ _ _).trans ((congrArg (u.1 ≫ ·) 𝔛.π.2).trans u.2)) with hDv
    set πA := curveChange 𝔛.π.1 𝔛.π.2 (Spec.map (CommRingCat.ofHom ρ)) with hπA
    set ιL := pullback.fst πA Dv.I.subschemeι with hιL
    have hILdef : IL = ιL.ker := rfl
    rw [hILdef, Scheme.Hom.ker_apply, RingHom.mem_ker, map_mul, map_natCast] at hf
    rw [hILdef, Scheme.Hom.ker_apply, RingHom.mem_ker]

    haveI hπAflat : Flat πA :=
      MorphismProperty.pullback_map (P := @Flat) (f := toBase p (ΓM M H) hj) (g := Spec.map (CommRingCat.ofHom ρ))
        (f' := toBase p (ΓN p M H hpM) hj) (g' := Spec.map (CommRingCat.ofHom ρ)) (i₁ := 𝔛.π.1) (i₂ := 𝟙 _)
        hπflat inferInstance 𝔛.π.2.symm (Category.id_comp _).symm

    haveI : IsIso (Dv.I.subschemeι ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ρ))) :=
      RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one Dv
    set gZ : pullback πA Dv.I.subschemeι ⟶ Spec (CommRingCat.of ↥A) :=
      pullback.snd πA Dv.I.subschemeι ≫ (Dv.I.subschemeι ≫ pullback.snd (toBase p (ΓN p M H hpM) hj) (Spec.map (CommRingCat.ofHom ρ))) with hgZ
    haveI hgZflat : Flat gZ := inferInstance

    let W : (pullback πA Dv.I.subschemeι).affineOpens := ⟨ιL ⁻¹ᵁ U, U.2.preimage ιL⟩
    have hWflat : (gZ.appLE ⊤ W le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) gZ hgZflat ⟨⊤, isAffineOpen_top _⟩ W le_top

    have hpA : ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) ∈ nonZeroDivisors Γ(Spec (CommRingCat.of ↥A), ⊤) := by
      have eA := (Scheme.ΓSpecIso (CommRingCat.of ↥A)).commRingCatIsoToRingEquiv
      haveI : IsDomain Γ(Spec (CommRingCat.of ↥A), ⊤) := MulEquiv.isDomain (↥A) eA.toMulEquiv
      refine mem_nonZeroDivisors_of_ne_zero fun h0 => ?_
      have := congrArg eA h0
      rw [map_natCast, map_zero] at this
      exact (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero) this

    letI := (gZ.appLE ⊤ W le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Spec (CommRingCat.of ↥A), ⊤) Γ(pullback πA Dv.I.subschemeι, W) := hWflat
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(pullback πA Dv.I.subschemeι, W)) hpA
    have key : ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) • (ιL.app U).hom f = ((p : ℕ) : Γ(Spec (CommRingCat.of ↥A), ⊤)) • (0 : Γ(pullback πA Dv.I.subschemeι, W)) := by
      rw [smul_zero, Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_natCast]
      exact hf
    exact hreg key

  refine Scheme.IdealSheafData.ext (funext fun U => ?_)
  haveI := U.2.isLocalization_basicOpen ((p : ℕ) : Γ(XA, U))
  refine HPSplitTools.eq_of_isSaturated_of_map_eq ((p : ℕ) : Γ(XA, U)) Γ(XA, XA.basicOpen ((p : ℕ) : Γ(XA, U)))
    (hSL U) (hSR U) ?_
  show (IL.ideal U).map (XA.presheaf.map (homOfLE <| XA.basicOpen_le _).op).hom =
    (IR.ideal U).map (XA.presheaf.map (homOfLE <| XA.basicOpen_le _).op).hom
  rw [IL.map_ideal_basicOpen, IR.map_ideal_basicOpen]
  exact hGEN U

end S_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_comap_curveChange_pi_ofPoint_eq_mul_prod_pow_of_ker_le (solution)
