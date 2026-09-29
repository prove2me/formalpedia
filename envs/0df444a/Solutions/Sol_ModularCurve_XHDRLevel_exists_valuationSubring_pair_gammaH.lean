-- Prove2me | solution 1 for ModularCurve.XHDRLevel.exists_valuationSubring_pair_gammaH
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/0b23df7e-ee45-5a2f-a31f-b3aae12b727a

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_GaloisRep_RatLocalizedAtResidue
import Theorems.Thm_ModularCurve_XHDRLevel_exists_valuationSubring_gauss_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_XHDRLevel_comap_atkinLehner_valuationSubring_gauss_gammaH
import Theorems.Thm_ModularCurve_XHDRLevel_valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH
import Theorems.Thm_ModularCurve_exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring"

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups

open ModularCurve.XHDRLevel in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ))) :
    ∃ W₀ W₁ : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),

      (∀ i : Fin 2, (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i)) ∧
        ∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ (![W₀, W₁] i).nonunits) ∧

      (∀ i : Fin 2, ∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
        Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ (![W₀, W₁] i) ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ (![W₀, W₁] i)) ∧

      W₀ ≠ W₁ ∧

      (∀ V : ValuationSubring ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)),
        (∀ a : ↥(GaloisRep.ratLocalizedAt p), algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V) →
        (∀ a ∈ Ideal.span {((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p))}, algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) a ∈ V.nonunits) →
        (∀ Q : Polynomial ↥(GaloisRep.ratLocalizedAt p), Q.map (GaloisRep.ratLocalizedAtResidue p) ≠ 0 →
          Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q ∈ V ∧ (Polynomial.aeval (jAt (CohCarrier.GammaH M H) hj) Q)⁻¹ ∈ V) →
        V = W₀ ∨ V = W₁) ∧

      (∀ i : Fin 2, ∀ x : ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)), x ∈ (![W₀, W₁] i).nonunits →
        x * (algebraMap ↥(GaloisRep.ratLocalizedAt p) ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) ((p : ℕ) : ↥(GaloisRep.ratLocalizedAt p)))⁻¹ ∈ (![W₀, W₁] i)) := by
  obtain ⟨σ, hσ, -⟩ := ModularCurve.exists_ratAlgEquiv_atkinLehner_gammaH_qExpand_diamondAutHBar p M H hpM hpM2 hHp
  obtain ⟨W₀, hpin, h1, h1', h2, h6⟩ := exists_valuationSubring_gauss_qExpFunctionFieldC p (CohCarrier.GammaH M H) hj
  obtain ⟨⟨g1, g1'⟩, g2, g6, hne⟩ :=
    comap_atkinLehner_valuationSubring_gauss_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hpin
  refine ⟨W₀, W₀.comap σ.toAlgHom.toRingHom, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i
    · exact ⟨h1, h1'⟩
    · exact ⟨g1, g1'⟩
  · intro i
    fin_cases i
    · exact h2
    · exact g2
  · exact fun h => hne h.symm
  · intro V hV₁ hV₁' hV₂
    exact valuationSubring_eq_gauss_or_eq_comap_atkinLehner_gammaH p M H hpM hpM2 hHp hj σ hσ W₀ hpin V hV₁ hV₁' hV₂
  · intro i
    fin_cases i
    · exact h6
    · exact g6

end S_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH
end P2MW
export P2MW.S_ModularCurve_XHDRLevel_exists_valuationSubring_pair_gammaH (solution)
