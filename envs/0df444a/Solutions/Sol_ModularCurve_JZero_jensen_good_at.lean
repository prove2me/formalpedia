-- Prove2me | solution 1 for ModularCurve.JZero.jensen_good_at
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/4ec1c124-6ed4-53c6-b260-dca37de92daf

import Definitions.Def_AlgebraicCurve_ConstantReduction
import Definitions.Def_AlgebraicCurve_PlaceEvaluationAlgebra
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_ModularCurve_FinitePlaceLift
import Theorems.Thm_AlgebraicCurve_prox_eq_neg_log_iSup_sub_of_chart
import Theorems.Thm_AlgebraicCurve_prox_eq_zero_of_far_of_chart
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_ModularCurve_exists_constantReduction_chartData_of_isEmbBasis
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_jensen_good_at
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option maxHeartbeats 3200000

set_option autoImplicit false

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve IsLocalRing"

noncomputable section

namespace P2MRoadD

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ord_nonneg_of_mem (v : Place L F) {f : F} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) :
    0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : F) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem ord_pos_of_evalAt_eq_zero (v : Place L F) (hv : v.IsRational) {f : F} (hf0 : f ≠ 0)
    (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) : 0 < v.ord f := by
  have hnn := ord_nonneg_of_mem v hf0 hf
  rcases hnn.lt_or_eq with h | h
  · exact h
  · exfalso
    exact v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h.symm h0

theorem mapDomain_apply_eq_sum {α β : Type*} [DecidableEq β] (g : α → β) (D : α →₀ ℤ) (q : β) :
    Finsupp.mapDomain g D q = ∑ P ∈ D.support, if g P = q then D P else 0 := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum]
  exact Finset.sum_congr rfl fun P _ => by rw [Finsupp.single_apply]

private theorem _root_.P2MRoadD.evalAt_mem_of_mem_integers [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    v₀.evalAt f ∈ A := by
  classical
  by_contra ha
  set a : L := v₀.evalAt f with ha_def
  have ha0 : a ≠ 0 := fun h => ha (h ▸ A.zero_mem)

  have hainv_A : a⁻¹ ∈ A := (A.mem_or_inv_mem a).resolve_left ha
  have hmapa : algebraMap L F a ∉ R.integers := fun h => ha ((R.algebraMap_mem_iff a).mp h)
  have hmapainv : algebraMap L F a⁻¹ ∈ R.integers := (R.algebraMap_mem_iff a⁻¹).mpr hainv_A
  have hnonunit : (⟨algebraMap L F a⁻¹, hmapainv⟩ : R.integers) ∈ maximalIdeal R.integers := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    obtain ⟨w, hw⟩ := hu

    apply hmapa
    have hwinv : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 = algebraMap L F a := by
      have h1 : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * algebraMap L F a⁻¹ = 1 := by
        have := congrArg (fun z : R.integers => (z : F)) w.inv_mul
        simpa [hw] using this
      have h2 : algebraMap L F a⁻¹ = (algebraMap L F a)⁻¹ := map_inv₀ _ _
      rw [h2] at h1
      have hane : algebraMap L F a ≠ 0 := (map_ne_zero _).mpr ha0
      calc ((w⁻¹ : (R.integers)ˣ) : R.integers).1
          = ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * (algebraMap L F a)⁻¹ * algebraMap L F a := by
            rw [mul_assoc, inv_mul_cancel₀ hane, mul_one]
        _ = algebraMap L F a := by rw [h1, one_mul]
    rw [← hwinv]
    exact ((w⁻¹ : (R.integers)ˣ) : R.integers).2

  have hg_mem : a⁻¹ • f ∈ R.integers := by
    rw [Algebra.smul_def]; exact mul_mem hmapainv hf
  have hg_max : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) ∈ maximalIdeal R.integers := by
    have : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) = ⟨algebraMap L F a⁻¹, hmapainv⟩ * ⟨f, hf⟩ :=
      Subtype.ext (Algebra.smul_def _ _)
    rw [this]
    exact Ideal.mul_mem_right _ _ hnonunit
  have hres_g : R.residue ⟨a⁻¹ • f, hg_mem⟩ = 0 := by
    have : (⟨a⁻¹ • f, hg_mem⟩ : R.integers) ∈ RingHom.ker R.residue := by rw [R.ker_residue]; exact hg_max
    exact this
  set h : F := a⁻¹ • f - 1 with hh_def
  have hh_mem : h ∈ R.integers := sub_mem hg_mem (one_mem _)
  have hres_h : R.residue ⟨h, hh_mem⟩ = -1 := by
    have : (⟨h, hh_mem⟩ : R.integers) = ⟨a⁻¹ • f, hg_mem⟩ - 1 := Subtype.ext rfl
    rw [this, map_sub, map_one, hres_g, zero_sub]
  have hres_h_ne : R.residue ⟨h, hh_mem⟩ ≠ 0 := by rw [hres_h]; exact neg_ne_zero.mpr one_ne_zero
  have hh0 : h ≠ 0 := by
    intro h0
    apply hres_h_ne
    have : (⟨h, hh_mem⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hh_reg : ∀ P, R.placeMap P = R.placeMap v₀ → h ∈ P.toValuationSubring := fun P hP =>
    sub_mem (by rw [Algebra.smul_def]; exact mul_mem (P.algebraMap_mem' _) (hreg P hP)) (one_mem _)
  have hh_val : v₀.evalAt h = 0 := by
    have hf0 : f ∈ v₀.toValuationSubring := hreg v₀ rfl
    have hsm : a⁻¹ • f ∈ v₀.toValuationSubring := by
      rw [Algebra.smul_def]; exact mul_mem (v₀.algebraMap_mem' _) hf0
    have e1 : v₀.evalAt h = v₀.evalAt (a⁻¹ • f) - v₀.evalAt 1 := by
      apply v₀.algebraMap_residueField_injective
      rw [map_sub, v₀.algebraMap_evalAt hv₀ (sub_mem hsm (one_mem _)), v₀.algebraMap_evalAt hv₀ hsm,
        v₀.algebraMap_evalAt hv₀ (one_mem _), ← map_sub]
      rfl
    rw [e1, v₀.evalAt_one, Algebra.smul_def, v₀.evalAt_mul_of_mem hv₀ (v₀.algebraMap_mem' _) hf0,
      v₀.evalAt_algebraMap_eq, ← ha_def, inv_mul_cancel₀ ha0, sub_self]
  have hord_v₀ : 0 < v₀.ord h := ord_pos_of_evalAt_eq_zero v₀ hv₀ hh0 (hh_reg v₀ rfl) hh_val

  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) h hh0
  have hpush := R.mapDomain_placeMap ⟨h, hh_mem⟩ hres_h_ne D hD (R.placeMap v₀)

  have hrhs : (R.placeMap v₀).ord (R.residue ⟨h, hh_mem⟩) = 0 := by
    rw [hres_h, show (-1 : Fbar) = algebraMap (ResidueField A) Fbar (-1) by rw [map_neg, map_one]]
    exact ConstantReduction.ord_algebraMap (L := ResidueField A) (F := Fbar) _ (neg_ne_zero.mpr one_ne_zero)

  have hlhs : 0 < Finsupp.mapDomain R.placeMap D (R.placeMap v₀) := by
    rw [mapDomain_apply_eq_sum]
    have hv₀supp : v₀ ∈ D.support := by
      rw [Finsupp.mem_support_iff, hD v₀]; exact hord_v₀.ne'
    have hnn : ∀ P ∈ D.support, 0 ≤ (if R.placeMap P = R.placeMap v₀ then D P else 0) := by
      intro P _
      split_ifs with hP
      · rw [hD P]; exact ord_nonneg_of_mem P hh0 (hh_reg P hP)
      · exact le_rfl
    calc (0 : ℤ) < (if R.placeMap v₀ = R.placeMap v₀ then D v₀ else 0) := by
          rw [if_pos rfl, hD v₀]; exact hord_v₀
      _ ≤ ∑ P ∈ D.support, (if R.placeMap P = R.placeMap v₀ then D P else 0) :=
          Finset.single_le_sum hnn hv₀supp
  rw [hpush, hrhs] at hlhs
  exact lt_irrefl _ hlhs

p2m_export "P2MRoadD" "evalAt_mem_of_mem_integers"

section Fibre
variable [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)

theorem ord_add_ord_le_ord_residue (g : F) (hg : g ∈ R.integers) (hres : R.residue ⟨g, hg⟩ ≠ 0)
    (v₀ w : Place L F) (hw : R.placeMap w = R.placeMap v₀) (hne : w ≠ v₀)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → g ∈ P.toValuationSubring) :
    v₀.ord g + w.ord g ≤ (R.placeMap v₀).ord (R.residue ⟨g, hg⟩) := by
  classical
  have hg0 : g ≠ 0 := by
    intro h0; apply hres
    have : (⟨g, hg⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) g hg0
  have hpush := R.mapDomain_placeMap ⟨g, hg⟩ hres D hD (R.placeMap v₀)
  rw [mapDomain_apply_eq_sum] at hpush
  have hnn : ∀ P ∈ D.support, 0 ≤ (if R.placeMap P = R.placeMap v₀ then D P else 0) := by
    intro P _
    split_ifs with hP
    · rw [hD P]; exact ord_nonneg_of_mem P hg0 (hreg P hP)
    · exact le_rfl

  have key : ∀ (T : Finset (Place L F)), T ⊆ D.support →
      ∑ P ∈ T, (if R.placeMap P = R.placeMap v₀ then D P else 0)
        ≤ (R.placeMap v₀).ord (R.residue ⟨g, hg⟩) := by
    intro T hT
    rw [← hpush]
    exact Finset.sum_le_sum_of_subset_of_nonneg hT (fun P hP _ => hnn P hP)

  have hout : ∀ P, P ∉ D.support → P.ord g = 0 := by
    intro P hP
    rw [Finsupp.notMem_support_iff] at hP
    rw [← hD P, hP]
  by_cases h₀ : v₀ ∈ D.support <;> by_cases h₁ : w ∈ D.support
  · have := key {v₀, w} (by
      intro P hP; rw [Finset.mem_insert, Finset.mem_singleton] at hP
      rcases hP with rfl | rfl <;> assumption)
    rw [Finset.sum_pair (Ne.symm hne), if_pos rfl, if_pos hw, hD, hD] at this
    exact this
  · have := key {v₀} (by intro P hP; rw [Finset.mem_singleton] at hP; rw [hP]; exact h₀)
    rw [Finset.sum_singleton, if_pos rfl, hD] at this
    rw [hout w h₁, add_zero]; exact this
  · have := key {w} (by intro P hP; rw [Finset.mem_singleton] at hP; rw [hP]; exact h₁)
    rw [Finset.sum_singleton, if_pos hw, hD] at this
    rw [hout v₀ h₀, zero_add]; exact this
  · rw [hout v₀ h₀, hout w h₁, add_zero]
    have := key ∅ (Finset.empty_subset _)
    rwa [Finset.sum_empty] at this

theorem ord_le_ord_residue (g : F) (hg : g ∈ R.integers) (hres : R.residue ⟨g, hg⟩ ≠ 0)
    (v₀ : Place L F) (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → g ∈ P.toValuationSubring) :
    v₀.ord g ≤ (R.placeMap v₀).ord (R.residue ⟨g, hg⟩) := by
  classical
  have hg0 : g ≠ 0 := by
    intro h0; apply hres
    have : (⟨g, hg⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) g hg0
  have hpush := R.mapDomain_placeMap ⟨g, hg⟩ hres D hD (R.placeMap v₀)
  rw [mapDomain_apply_eq_sum] at hpush
  have hnn : ∀ P ∈ D.support, 0 ≤ (if R.placeMap P = R.placeMap v₀ then D P else 0) := by
    intro P _
    split_ifs with hP
    · rw [hD P]; exact ord_nonneg_of_mem P hg0 (hreg P hP)
    · exact le_rfl
  by_cases h₀ : v₀ ∈ D.support
  · have := Finset.single_le_sum hnn h₀
    rw [if_pos rfl, hD, hpush] at this
    exact this
  · rw [Finsupp.notMem_support_iff] at h₀
    rw [← hD v₀, h₀, ← hpush]
    exact Finset.sum_nonneg hnn

end Fibre

theorem isUnit_of_residue_ne_zero (R : ConstantReduction A F Fbar) (g : R.integers) (h : R.residue g ≠ 0) :
    IsUnit g := by
  by_contra hu
  apply h
  have : g ∈ RingHom.ker R.residue := by
    rw [R.ker_residue]; exact (mem_maximalIdeal _).mpr hu
  exact this

end P2MRoadD

open IsLocalRing

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart"
namespace ConstantReduction
p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap"
namespace RoadD
p2m_open "AlgebraicCurve.ConstantReduction AlgebraicCurve"

theorem mapDomain_apply_eq_sum_filter {α β : Type*} [DecidableEq β] {M : Type*} [AddCommMonoid M]
    (f : α → β) (D : α →₀ M) (b : β) :
    Finsupp.mapDomain f D b = ∑ a ∈ D.support.filter (fun a => f a = b), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finsupp.single_apply]

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]
variable (R : ConstantReduction A F Fbar)

open scoped Classical

theorem ord_residue_eq_sum_fibre (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) (Q : Place (ResidueField A) Fbar) :
    Q.ord (R.residue f) =
      ∑ P ∈ D.support.filter (fun P => R.placeMap P = Q), P.ord (f : F) := by
  classical
  rw [← R.mapDomain_placeMap f hf D hD Q, mapDomain_apply_eq_sum_filter]
  exact Finset.sum_congr rfl fun P _ => hD P

theorem ord_le_ord_residue_of_fibre_nonneg (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) (Q : Place (ResidueField A) Fbar)
    (hreg : ∀ P, R.placeMap P = Q → 0 ≤ P.ord (f : F))
    (P₀ : Place L F) (hP₀ : R.placeMap P₀ = Q) :
    P₀.ord (f : F) ≤ Q.ord (R.residue f) := by
  classical
  rw [ord_residue_eq_sum_fibre R f hf D hD Q]
  by_cases hmem : P₀ ∈ D.support.filter (fun P => R.placeMap P = Q)
  · exact Finset.single_le_sum (f := fun P => P.ord (f : F))
      (fun P hP => hreg P (Finset.mem_filter.mp hP).2) hmem
  · have h0 : P₀.ord (f : F) = 0 := by
      have : P₀ ∉ D.support := fun h => hmem (Finset.mem_filter.mpr ⟨h, hP₀⟩)
      rw [← hD P₀]
      exact Finsupp.notMem_support_iff.mp this
    rw [h0]
    exact Finset.sum_nonneg fun P hP => hreg P (Finset.mem_filter.mp hP).2

theorem ord_residue_nonneg_of_fibre_nonneg (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) (Q : Place (ResidueField A) Fbar)
    (hreg : ∀ P, R.placeMap P = Q → 0 ≤ P.ord (f : F)) :
    0 ≤ Q.ord (R.residue f) := by
  classical
  rw [ord_residue_eq_sum_fibre R f hf D hD Q]
  exact Finset.sum_nonneg fun P hP => hreg P (Finset.mem_filter.mp hP).2

theorem ord_residue_pos_of_vanishing (f : R.integers) (hf : R.residue f ≠ 0) (D : Divisor L F)
    (hD : ∀ P, D P = P.ord (f : F)) (Q : Place (ResidueField A) Fbar)
    (hreg : ∀ P, R.placeMap P = Q → 0 ≤ P.ord (f : F))
    (P₀ : Place L F) (hP₀ : R.placeMap P₀ = Q) (hvan : 0 < P₀.ord (f : F)) :
    0 < Q.ord (R.residue f) :=
  lt_of_lt_of_le hvan (ord_le_ord_residue_of_fibre_nonneg R f hf D hD Q hreg P₀ hP₀)

end AlgebraicCurve.ConstantReduction.RoadD

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart"
namespace ConstantReduction
p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap"
namespace RoadD
p2m_open "AlgebraicCurve.ConstantReduction AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ord_nonneg_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E) {f : E}
    (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) : 0 ≤ v.ord f := by
  have h1 : v.adicValuation f ≤ 1 := by
    have := v.adicValuation_coe ⟨f, hf⟩
    rw [show ((⟨f, hf⟩ : v.toValuationSubring) : E) = f from rfl] at this
    rw [this]
    exact IsDedekindDomain.HeightOneSpectrum.intValuation_le_one _ _
  have hne := v.adicValuation_ne_zero hf0
  have h2 : WithZero.exp (WithZero.log (v.adicValuation f)) ≤ WithZero.exp 0 := by
    rw [WithZero.exp_log hne, WithZero.exp_zero]; exact h1
  rw [WithZero.exp_le_exp] at h2
  show 0 ≤ -(WithZero.log (v.adicValuation f))
  omega

theorem ord_pos_of_evalAt_eq_zero {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {f : E} (hf0 : f ≠ 0) (hf : f ∈ v.toValuationSubring) (h0 : v.evalAt f = 0) :
    0 < v.ord f := by
  rcases (ord_nonneg_of_mem v hf0 hf).lt_or_eq with h | h
  · exact h
  · exact absurd h0 (v.evalAt_ne_zero_of_ord_eq_zero hv hf0 h.symm)

theorem evalAt_eq_zero_of_ord_pos {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    {f : E} (hf : f ∈ v.toValuationSubring) (h : 0 < v.ord f) : v.evalAt f = 0 := by
  have hmax : (⟨f, hf⟩ : v.toValuationSubring) ∈ maximalIdeal v.toValuationSubring := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := v.ord_coe_unit hu.unit
    rw [IsUnit.unit_spec] at this
    exact absurd this (ne_of_gt h)
  rw [v.evalAt_of_mem hf, (IsLocalRing.residue_eq_zero_iff _).mpr hmax, ← map_zero (algebraMap K v.ResidueField),
    v.residueInv_algebraMap]

theorem evalAt_add_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {f g : E} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_sub_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {f g : E} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_sub]
  rfl

end AlgebraicCurve.ConstantReduction.RoadD

namespace AlgebraicCurve p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart" namespace ConstantReduction p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap" end AlgebraicCurve.ConstantReduction
namespace AlgebraicCurve.ConstantReduction
p2m_open_scoped "AlgebraicCurve AlgebraicCurve.ConstantReduction" in
private theorem _root_.AlgebraicCurve.ConstantReduction.evalAt_mem_of_mem_integers
    {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    [AlgebraicCurve.HasPrincipalDivisors L F] (R : AlgebraicCurve.ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : AlgebraicCurve.Place L F) (hv₀ : v₀.IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    v₀.evalAt f ∈ A :=
  P2MRoadD.evalAt_mem_of_mem_integers R f hf v₀ hv₀ hreg

end AlgebraicCurve.ConstantReduction
p2m_export "" "AlgebraicCurve.ConstantReduction.evalAt_mem_of_mem_integers"
namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart"
namespace ConstantReduction
p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap"
namespace RoadD
p2m_open "AlgebraicCurve.ConstantReduction AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_mem_and_evalAt_eq [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational)
    (hQ : (R.placeMap v₀).IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring)
    (haA : v₀.evalAt f ∈ A) :
    R.residue ⟨f, hf⟩ ∈ (R.placeMap v₀).toValuationSubring ∧
      (R.placeMap v₀).evalAt (R.residue ⟨f, hf⟩) = IsLocalRing.residue A ⟨v₀.evalAt f, haA⟩ := by
  classical
  set a : L := v₀.evalAt f with ha
  set Q := R.placeMap v₀ with hQdef
  set abar : ResidueField A := IsLocalRing.residue A ⟨a, haA⟩ with habar
  have hc_mem : algebraMap L F a ∈ R.integers := (R.algebraMap_mem_iff a).mpr haA
  have hres_c : R.residue ⟨algebraMap L F a, hc_mem⟩ = algebraMap (ResidueField A) Fbar abar :=
    R.residue_algebraMap ⟨a, haA⟩
  set h : F := f - algebraMap L F a with hh
  have hh_mem : h ∈ R.integers := sub_mem hf hc_mem
  have hres_h : R.residue ⟨h, hh_mem⟩ = R.residue ⟨f, hf⟩ - algebraMap (ResidueField A) Fbar abar := by
    have : (⟨h, hh_mem⟩ : R.integers) = ⟨f, hf⟩ - ⟨algebraMap L F a, hc_mem⟩ := Subtype.ext rfl
    rw [this, map_sub, hres_c]
  have hconst_mem : algebraMap (ResidueField A) Fbar abar ∈ Q.toValuationSubring := Q.algebraMap_mem' _
  by_cases hzero : R.residue ⟨h, hh_mem⟩ = 0
  ·
    have hfbar : R.residue ⟨f, hf⟩ = algebraMap (ResidueField A) Fbar abar := by
      rwa [hres_h, sub_eq_zero] at hzero
    rw [hfbar]
    exact ⟨hconst_mem, Q.evalAt_algebraMap_eq abar⟩
  ·
    have hh0 : h ≠ 0 := by
      intro h0; apply hzero
      have : (⟨h, hh_mem⟩ : R.integers) = 0 := Subtype.ext h0
      rw [this, map_zero]
    have hh_reg : ∀ P, R.placeMap P = Q → h ∈ P.toValuationSubring := fun P hP =>
      sub_mem (hreg P hP) (P.algebraMap_mem' _)
    have hh_val : v₀.evalAt h = 0 := by
      rw [hh, evalAt_sub_of_mem v₀ hv₀ (hreg v₀ rfl) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq, ← ha,
        sub_self]
    have hord_v₀ : 0 < v₀.ord h := ord_pos_of_evalAt_eq_zero v₀ hv₀ hh0 (hh_reg v₀ rfl) hh_val
    obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) h hh0
    have hpos : 0 < Q.ord (R.residue ⟨h, hh_mem⟩) :=
      ord_residue_pos_of_vanishing R ⟨h, hh_mem⟩ hzero D hD Q
        (fun P hP => ord_nonneg_of_mem P hh0 (hh_reg P hP)) v₀ rfl hord_v₀
    have hhbar_mem : R.residue ⟨h, hh_mem⟩ ∈ Q.toValuationSubring :=
      Q.mem_toValuationSubring_of_ord_nonneg_alt hzero hpos.le
    have hhbar_val : Q.evalAt (R.residue ⟨h, hh_mem⟩) = 0 := evalAt_eq_zero_of_ord_pos Q hhbar_mem hpos
    have hfbar : R.residue ⟨f, hf⟩ = R.residue ⟨h, hh_mem⟩ + algebraMap (ResidueField A) Fbar abar := by
      rw [hres_h, sub_add_cancel]
    refine ⟨?_, ?_⟩
    · rw [hfbar]; exact add_mem hhbar_mem hconst_mem
    · rw [hfbar, evalAt_add_of_mem Q hQ hhbar_mem hconst_mem, hhbar_val, Q.evalAt_algebraMap_eq, zero_add]

theorem residue_mem_placeMap_toValuationSubring [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational)
    (hQ : (R.placeMap v₀).IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    R.residue ⟨f, hf⟩ ∈ (R.placeMap v₀).toValuationSubring :=
  (residue_mem_and_evalAt_eq R f hf v₀ hv₀ hQ hreg
    (ConstantReduction.evalAt_mem_of_mem_integers R f hf v₀ hv₀ hreg)).1

theorem evalAt_placeMap_residue_eq_residue_evalAt [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational)
    (hQ : (R.placeMap v₀).IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    (R.placeMap v₀).evalAt (R.residue ⟨f, hf⟩) =
      IsLocalRing.residue A ⟨v₀.evalAt f, ConstantReduction.evalAt_mem_of_mem_integers R f hf v₀ hv₀ hreg⟩ :=
  (residue_mem_and_evalAt_eq R f hf v₀ hv₀ hQ hreg _).2

theorem evalAt_sub_evalAt_mem_maximalIdeal [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) {v₀ w : Place L F} (hv₀ : v₀.IsRational) (hw : w.IsRational)
    (hQ : (R.placeMap v₀).IsRational) (hfib : R.placeMap w = R.placeMap v₀)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    (⟨v₀.evalAt f, ConstantReduction.evalAt_mem_of_mem_integers R f hf v₀ hv₀ hreg⟩ -
        ⟨w.evalAt f, ConstantReduction.evalAt_mem_of_mem_integers R f hf w hw
          (fun P hP => hreg P (hP.trans hfib))⟩ : A) ∈ maximalIdeal A := by
  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero,
    ← evalAt_placeMap_residue_eq_residue_evalAt R f hf v₀ hv₀ hQ hreg,
    ← evalAt_placeMap_residue_eq_residue_evalAt R f hf w hw (hfib ▸ hQ) (fun P hP => hreg P (hP.trans hfib)),
    hfib]

end AlgebraicCurve.ConstantReduction.RoadD

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart"
namespace ConstantReduction
p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap"
namespace RoadD
p2m_open "AlgebraicCurve.ConstantReduction AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem isRational_of_deg_eq_one {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (h : v.deg = 1) : v.IsRational := by

  intro x
  have hfd : Module.finrank K v.ResidueField = 1 := h
  haveI : FiniteDimensional K v.ResidueField := Module.finite_of_finrank_eq_succ hfd
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (1 : v.ResidueField) one_ne_zero).mp hfd x
  exact ⟨c, by rw [Algebra.algebraMap_eq_smul_one]; exact hc⟩

theorem isRational_placeMap_of_isRational (R : ConstantReduction A F Fbar) {v₀ : Place L F}
    (hv₀ : v₀.IsRational) : (R.placeMap v₀).IsRational :=
  isRational_of_deg_eq_one _ ((R.deg_placeMap v₀).trans (Place.deg_eq_one_of_isRational hv₀))

end AlgebraicCurve.ConstantReduction.RoadD

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "ConstantReduction ConstantReduction.ord_algebraMap ConstantReduction.ord_smul Place Place.ord_zero Place.ord_one Divisor HasPrincipalDivisors HasPrincipalDivisors.exists_divisor riemannRochSpace mem_riemannRochSpace_iff H1 Place.deg_eq_one_of_isRational prox regVal pivotIndex evalVec prox_eq_neg_log_iSup_sub_of_chart prox_eq_zero_of_far_of_chart"
namespace ConstantReduction
p2m_export "AlgebraicCurve.ConstantReduction" "IsGood ord_algebraMap ord_smul integers placeMap residue algebraMap_mem_iff residue_algebraMap deg_placeMap exists_smul_mem ker_residue mapDomain_placeMap"
namespace RoadD
p2m_open "AlgebraicCurve.ConstantReduction AlgebraicCurve"

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

private theorem _root_.AlgebraicCurve.ConstantReduction.RoadD.ord_add_ord_le_ord_residue [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar) (g : F) (hg : g ∈ R.integers)
    (hres : R.residue ⟨g, hg⟩ ≠ 0)
    (v₀ w : Place L F) (hw : R.placeMap w = R.placeMap v₀) (hne : w ≠ v₀)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → g ∈ P.toValuationSubring) :
    v₀.ord g + w.ord g ≤ (R.placeMap v₀).ord (R.residue ⟨g, hg⟩) :=
  P2MRoadD.ord_add_ord_le_ord_residue R g hg hres v₀ w hw hne hreg

p2m_export "AlgebraicCurve.ConstantReduction.RoadD" "ord_add_ord_le_ord_residue"

theorem ord_prod {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E) {ι : Type*}
    (s : Finset ι) (g : ι → E) (hg : ∀ i ∈ s, g i ≠ 0) :
    v.ord (∏ i ∈ s, g i) = ∑ i ∈ s, v.ord (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Place.ord_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha,
      v.ord_mul (hg a (Finset.mem_insert_self a s))
        (Finset.prod_ne_zero_iff.mpr fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem ord_pow {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E) (g : E) (n : ℕ) :
    v.ord (g ^ n) = n * v.ord g := by
  rw [← zpow_natCast, v.ord_zpow]

theorem evalAt_pow_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {g : E} (hg : g ∈ v.toValuationSubring) (n : ℕ) :
    v.evalAt (g ^ n) = v.evalAt g ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, v.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hg n) hg, ih]

theorem evalAt_prod_of_mem {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {ι : Type*} (s : Finset ι) (g : ι → E)
    (hg : ∀ i ∈ s, g i ∈ v.toValuationSubring) :
    v.evalAt (∏ i ∈ s, g i) = ∏ i ∈ s, v.evalAt (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [v.evalAt_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      v.evalAt_mul_of_mem hv (hg a (Finset.mem_insert_self a s))
        (prod_mem fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

theorem inv_mem_and_evalAt_inv {K E : Type*} [Field K] [Field E] [Algebra K E] (v : Place K E)
    (hv : v.IsRational) {g : E} (hg0 : g ≠ 0) (h : v.ord g = 0) :
    g⁻¹ ∈ v.toValuationSubring ∧ v.evalAt g⁻¹ = (v.evalAt g)⁻¹ := by
  have hmem : g ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hg0 h.ge
  have hinv : g⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hg0) (by rw [v.ord_inv, h, neg_zero])
  refine ⟨hinv, ?_⟩
  have hne : v.evalAt g ≠ 0 := v.evalAt_ne_zero_of_ord_eq_zero hv hg0 h
  have h1 : v.evalAt g * v.evalAt g⁻¹ = 1 := by
    rw [← v.evalAt_mul_of_mem hv hmem hinv, mul_inv_cancel₀ hg0, v.evalAt_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem sub_const_facts [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (τ : F) (hτ : τ ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1) :
    ∃ hd : τ - algebraMap L F (v₀.evalAt τ) ∈ R.integers,
      R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩
          = R.residue ⟨τ, hτ⟩ - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩)) ∧
      R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩ ≠ 0 ∧
      (R.placeMap v₀).ord (R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩) = 1 ∧
      (∀ P, R.placeMap P = R.placeMap v₀ → τ - algebraMap L F (v₀.evalAt τ) ∈ P.toValuationSubring) ∧
      τ - algebraMap L F (v₀.evalAt τ) ≠ 0 ∧
      v₀.ord (τ - algebraMap L F (v₀.evalAt τ)) = 1 := by
  have ha : v₀.evalAt τ ∈ A := ConstantReduction.evalAt_mem_of_mem_integers R τ hτ v₀ hv₀ hregτ
  have hconst : algebraMap L F (v₀.evalAt τ) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ha
  have hd : τ - algebraMap L F (v₀.evalAt τ) ∈ R.integers := sub_mem hτ hconst
  have hres : R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩
      = R.residue ⟨τ, hτ⟩ - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩)) := by
    have e1 : (⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩ : R.integers) = ⟨τ, hτ⟩ - ⟨algebraMap L F (v₀.evalAt τ), hconst⟩ :=
      Subtype.ext rfl
    rw [e1, map_sub, evalAt_placeMap_residue_eq_residue_evalAt R τ hτ v₀ hv₀ hQ hregτ]
    congr 1
    exact R.residue_algebraMap ⟨v₀.evalAt τ, ha⟩
  have hord : (R.placeMap v₀).ord (R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩) = 1 := by
    rw [hres]; exact hunif
  have hne : R.residue ⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩ ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at hord; exact zero_ne_one hord
  have hreg : ∀ P, R.placeMap P = R.placeMap v₀ → τ - algebraMap L F (v₀.evalAt τ) ∈ P.toValuationSubring :=
    fun P hP => sub_mem (hregτ P hP) (P.algebraMap_mem' _)
  have hd0 : τ - algebraMap L F (v₀.evalAt τ) ≠ 0 := by
    intro h0; apply hne
    have : (⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hval : v₀.evalAt (τ - algebraMap L F (v₀.evalAt τ)) = 0 := by
    rw [evalAt_sub_of_mem v₀ hv₀ (hregτ v₀ rfl) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq, sub_self]
  have hpos : 0 < v₀.ord (τ - algebraMap L F (v₀.evalAt τ)) :=
    ord_pos_of_evalAt_eq_zero v₀ hv₀ hd0 (hreg v₀ rfl) hval
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) _ hd0
  have hle := ord_le_ord_residue_of_fibre_nonneg R ⟨_, hd⟩ hne D hD (R.placeMap v₀)
    (fun P hP => ord_nonneg_of_mem P hd0 (hreg P hP)) v₀ rfl
  refine ⟨hd, hres, hne, hord, hreg, hd0, ?_⟩
  have : v₀.ord (τ - algebraMap L F (v₀.evalAt τ)) ≤ 1 := by
    have h' : v₀.ord ((⟨τ - algebraMap L F (v₀.evalAt τ), hd⟩ : R.integers) : F) ≤ _ := hle
    rw [hord] at h'
    exact h'
  omega

open scoped Classical in
theorem valuation_regVal_eq_prod [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (u τ : F) (lam : L) (hlamu : lam • u ∈ R.integers) (hunit : R.residue ⟨lam • u, hlamu⟩ ≠ 0)
    (hτ : τ ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hrat : ∀ P, R.placeMap P = R.placeMap v₀ → P.IsRational)
    (hregu : ∀ P, R.placeMap P = R.placeMap v₀ → u ∈ P.toValuationSubring)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1)
    (D : Divisor L F) (hD : ∀ P, D P = P.ord u) :
    A.valuation (lam * v₀.evalAt (u * ((τ - algebraMap L F (v₀.evalAt τ))⁻¹) ^ (D v₀).toNat))
      = ∏ w ∈ ((D.support.filter fun w => R.placeMap w = R.placeMap v₀).erase v₀),
          A.valuation (v₀.evalAt τ - w.evalAt τ) ^ (D w).toNat := by

  set Q := R.placeMap v₀ with hQdef
  set Fib := D.support.filter (fun w => R.placeMap w = Q) with hFib
  set Z := Fib.erase v₀ with hZ
  set dw : Place L F → F := fun w => τ - algebraMap L F (w.evalAt τ) with hdw_def
  set e : ℕ := (D v₀).toNat with he
  set n : Place L F → ℕ := fun w => (D w).toNat with hn

  have hlamu0 : lam • u ≠ 0 := by
    intro h0; apply hunit
    have : (⟨lam • u, hlamu⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hlam0 : lam ≠ 0 := by intro h; exact hlamu0 (by rw [h, zero_smul])
  have hu0 : u ≠ 0 := by intro h; exact hlamu0 (by rw [h, smul_zero])

  have hZmem : ∀ w ∈ Z, R.placeMap w = Q ∧ w ≠ v₀ ∧ w ∈ D.support := by
    intro w hw
    rw [hZ, Finset.mem_erase] at hw
    obtain ⟨hne, hw⟩ := hw
    rw [hFib, Finset.mem_filter] at hw
    exact ⟨hw.2, hne, hw.1⟩

  have hDnn : ∀ P, R.placeMap P = Q → 0 ≤ D P := fun P hP => by
    rw [hD P]; exact ord_nonneg_of_mem P hu0 (hregu P hP)
  have he' : ((e : ℕ) : ℤ) = D v₀ := Int.toNat_of_nonneg (hDnn v₀ rfl)
  have hn' : ∀ w ∈ Z, ((n w : ℕ) : ℤ) = D w := fun w hw => Int.toNat_of_nonneg (hDnn w (hZmem w hw).1)

  obtain ⟨hd_mem, hres_d, hne_d, hordQ_d, hreg_d, hd0, hordv_d⟩ :=
    sub_const_facts R τ hτ v₀ hv₀ hQ hregτ hunif
  set d : F := τ - algebraMap L F (v₀.evalAt τ) with hd_def
  have hw_facts : ∀ w ∈ Z, ∃ hdw : dw w ∈ R.integers,
      R.residue ⟨dw w, hdw⟩ ≠ 0 ∧ Q.ord (R.residue ⟨dw w, hdw⟩) = 1 ∧
      (∀ P, R.placeMap P = Q → dw w ∈ P.toValuationSubring) ∧ dw w ≠ 0 ∧ w.ord (dw w) = 1 := by
    intro w hw
    obtain ⟨hwfib, hwne, -⟩ := hZmem w hw
    have hQw : (R.placeMap w).IsRational := by rw [hwfib]; exact hQ
    have hregτw : ∀ P, R.placeMap P = R.placeMap w → τ ∈ P.toValuationSubring :=
      fun P hP => hregτ P (hP.trans hwfib)
    have hunifw : (R.placeMap w).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap w).evalAt (R.residue ⟨τ, hτ⟩))) = 1 := by
      rw [hwfib]; exact hunif
    obtain ⟨hm, -, hne', hord', hreg', h0', hordw'⟩ :=
      sub_const_facts R τ hτ w (hrat w hwfib) hQw hregτw hunifw
    refine ⟨hm, hne', ?_, fun P hP => hreg' P (hP.trans hwfib.symm), h0', hordw'⟩
    rw [← hwfib]; exact hord'

  have hord_d_other : ∀ P, R.placeMap P = Q → P ≠ v₀ → P.ord d = 0 := by
    intro P hP hne
    have h := ord_add_ord_le_ord_residue R d hd_mem hne_d v₀ P hP hne hreg_d
    rw [hordv_d, hordQ_d] at h
    have h2 := ord_nonneg_of_mem P hd0 (hreg_d P hP)
    omega
  have hord_dw_other : ∀ w ∈ Z, ∀ P, R.placeMap P = Q → P ≠ w → P.ord (dw w) = 0 := by
    intro w hw P hP hne
    obtain ⟨hm, hne', hord', hreg', h0', hordw'⟩ := hw_facts w hw
    obtain ⟨hwfib, -, -⟩ := hZmem w hw
    have h := ord_add_ord_le_ord_residue R (dw w) hm hne' w P (hP.trans hwfib.symm) hne
      (fun P' hP' => hreg' P' (hP'.trans hwfib))
    rw [hordw', hwfib, hord'] at h
    have h2 := ord_nonneg_of_mem P h0' (hreg' P hP)
    omega

  have hdw_mem : ∀ w ∈ Z, dw w ∈ R.integers := fun w hw => (hw_facts w hw).1
  set Pint : R.integers := ⟨d, hd_mem⟩ ^ e * ∏ w ∈ Z.attach, ⟨dw w, hdw_mem w w.2⟩ ^ n w with hPint
  have hPcoe : (Pint : F) = d ^ e * ∏ w ∈ Z, dw w ^ n w := by
    rw [hPint]
    push_cast
    rw [Finset.prod_attach Z (fun w => dw w ^ n w)]
  have hresP : R.residue Pint = R.residue ⟨d, hd_mem⟩ ^ e *
      ∏ w ∈ Z.attach, R.residue ⟨dw w, hdw_mem w w.2⟩ ^ n w := by
    rw [hPint, map_mul, map_pow, map_prod]
    exact congrArg _ (Finset.prod_congr rfl fun w _ => map_pow _ _ _)
  have hresP_ne : R.residue Pint ≠ 0 := by
    rw [hresP]
    exact mul_ne_zero (pow_ne_zero _ hne_d)
      (Finset.prod_ne_zero_iff.mpr fun (w : {x // x ∈ Z}) _ => pow_ne_zero _ (hw_facts w.1 w.2).2.1)
  have hordQ_P : Q.ord (R.residue Pint) = e + ∑ w ∈ Z, (n w : ℤ) := by
    have hfac : ∀ w : {x // x ∈ Z}, R.residue ⟨dw w.1, hdw_mem w.1 w.2⟩ ^ n w.1 ≠ 0 :=
      fun w => pow_ne_zero _ (hw_facts w.1 w.2).2.1
    rw [hresP, Q.ord_mul (pow_ne_zero _ hne_d) (Finset.prod_ne_zero_iff.mpr fun w _ => hfac w),
      ord_pow, hordQ_d, mul_one, ord_prod Q _ _ (fun w _ => hfac w)]
    congr 1
    rw [← Finset.sum_attach Z (fun w => (n w : ℤ))]
    refine Finset.sum_congr rfl fun (w : {x // x ∈ Z}) _ => ?_
    rw [ord_pow, (hw_facts w.1 w.2).2.2.1, mul_one]
  have hPunit : IsUnit Pint := by
    by_contra hu
    apply hresP_ne
    have : Pint ∈ RingHom.ker R.residue := by
      rw [R.ker_residue]; exact (IsLocalRing.mem_maximalIdeal _).mpr hu
    exact this
  set xi : R.integers := ((hPunit.unit⁻¹ : R.integersˣ) : R.integers) with hxi
  have hPx : Pint * xi = 1 := by
    have h := hPunit.unit.mul_inv
    rwa [IsUnit.unit_spec] at h
  have hP0 : (Pint : F) ≠ 0 := by
    rw [hPcoe]
    exact mul_ne_zero (pow_ne_zero _ hd0)
      (Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (hw_facts w hw).2.2.2.2.1)
  have hxcoe : (xi : F) = (Pint : F)⁻¹ := by
    have h1 : (Pint : F) * (xi : F) = 1 := by
      have := congrArg (fun z : R.integers => (z : F)) hPx
      simpa using this
    exact eq_inv_of_mul_eq_one_right h1
  have hresx : R.residue xi = (R.residue Pint)⁻¹ := by
    have h1 : R.residue Pint * R.residue xi = 1 := by rw [← map_mul, hPx, map_one]
    exact eq_inv_of_mul_eq_one_right h1
  set f : F := (lam • u) * (Pint : F)⁻¹ with hf
  have hfmem : f ∈ R.integers := by
    rw [hf, ← hxcoe]; exact mul_mem hlamu xi.2
  have hfint : (⟨f, hfmem⟩ : R.integers) = ⟨lam • u, hlamu⟩ * xi :=
    Subtype.ext (by show f = lam • u * (xi : F); rw [hf, hxcoe])
  have hresf : R.residue ⟨f, hfmem⟩ = R.residue ⟨lam • u, hlamu⟩ * (R.residue Pint)⁻¹ := by
    rw [hfint, map_mul, hresx]
  have hresf_ne : R.residue ⟨f, hfmem⟩ ≠ 0 := by
    rw [hresf]; exact mul_ne_zero hunit (inv_ne_zero hresP_ne)
  have hf0 : f ≠ 0 := by
    rw [hf]; exact mul_ne_zero hlamu0 (inv_ne_zero hP0)

  have hD' : ∀ P, D P = P.ord (lam • u) := fun P => by
    rw [hD P, ConstantReduction.ord_smul P hlam0 u]
  have hordQ_lamu : Q.ord (R.residue ⟨lam • u, hlamu⟩) = D v₀ + ∑ w ∈ Z, D w := by
    rw [ord_residue_eq_sum_fibre R ⟨lam • u, hlamu⟩ hunit D hD' Q]
    have hsum : ∑ P ∈ Fib, P.ord (lam • u) = ∑ P ∈ Fib, D P :=
      Finset.sum_congr rfl fun P _ => (hD' P).symm
    rw [← hFib, hsum]
    by_cases hv : v₀ ∈ Fib
    · rw [hZ, ← Finset.add_sum_erase Fib (fun P => D P) hv]
    · have hD0 : D v₀ = 0 := by
        have : v₀ ∉ D.support := fun h => hv (by rw [hFib, Finset.mem_filter]; exact ⟨h, rfl⟩)
        exact Finsupp.notMem_support_iff.mp this
      rw [hD0, zero_add, hZ, Finset.erase_eq_of_notMem hv]
  have hordQ_f : Q.ord (R.residue ⟨f, hfmem⟩) = 0 := by
    rw [hresf, Q.ord_mul hunit (inv_ne_zero hresP_ne), Q.ord_inv, hordQ_lamu, hordQ_P, ← he']
    have : ∑ w ∈ Z, D w = ∑ w ∈ Z, (n w : ℤ) := Finset.sum_congr rfl fun w hw => (hn' w hw).symm
    rw [this]
    ring

  have hord_f : ∀ P, R.placeMap P = Q → P.ord f = 0 := by
    intro P hP
    have hPord : P.ord (Pint : F) = (e : ℤ) * P.ord d + ∑ w ∈ Z, (n w : ℤ) * P.ord (dw w) := by
      rw [hPcoe, P.ord_mul (pow_ne_zero _ hd0)
          (Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (hw_facts w hw).2.2.2.2.1),
        ord_pow, ord_prod P _ _ (fun w hw => pow_ne_zero _ (hw_facts w hw).2.2.2.2.1)]
      congr 1
      exact Finset.sum_congr rfl fun w _ => ord_pow P _ _
    have hsumZ : ∑ w ∈ Z, (n w : ℤ) * P.ord (dw w) = if P ∈ Z then (n P : ℤ) else 0 := by
      by_cases hPZ : P ∈ Z
      · rw [if_pos hPZ]
        rw [Finset.sum_eq_single_of_mem P hPZ (fun w hw hwP => by
          rw [hord_dw_other w hw P hP (Ne.symm hwP), mul_zero])]
        rw [(hw_facts P hPZ).2.2.2.2.2, mul_one]
      · rw [if_neg hPZ]
        exact Finset.sum_eq_zero fun w hw => by
          rw [hord_dw_other w hw P hP (fun h => hPZ (h ▸ hw)), mul_zero]
    rw [hf, P.ord_mul hlamu0 (inv_ne_zero hP0), P.ord_inv, ← hD' P, hPord, hsumZ]
    by_cases hPv : P = v₀
    · subst hPv
      have : P ∉ Z := by rw [hZ]; exact Finset.notMem_erase P Fib
      rw [if_neg this, hordv_d, ← he']
      ring
    · rw [hord_d_other P hP hPv, mul_zero, zero_add]
      by_cases hPZ : P ∈ Z
      · rw [if_pos hPZ, hn' P hPZ]; ring
      · rw [if_neg hPZ]
        have : P ∉ D.support := fun h => hPZ (by
          rw [hZ, Finset.mem_erase, hFib, Finset.mem_filter]; exact ⟨hPv, h, hP⟩)
        rw [Finsupp.notMem_support_iff.mp this]
        ring
  have hreg_f : ∀ P, R.placeMap P = Q → f ∈ P.toValuationSubring := fun P hP =>
    P.mem_toValuationSubring_of_ord_nonneg_alt hf0 (hord_f P hP).ge

  have haf : v₀.evalAt f ∈ A := ConstantReduction.evalAt_mem_of_mem_integers R f hfmem v₀ hv₀ hreg_f
  have hval1 : A.valuation (v₀.evalAt f) = 1 := by
    have hQval : Q.evalAt (R.residue ⟨f, hfmem⟩) ≠ 0 :=
      Q.evalAt_ne_zero_of_ord_eq_zero hQ hresf_ne hordQ_f
    have hres := evalAt_placeMap_residue_eq_residue_evalAt R f hfmem v₀ hv₀ hQ hreg_f
    rw [hres] at hQval

    have hnotmax : (⟨v₀.evalAt f, haf⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun h =>
      hQval ((IsLocalRing.residue_eq_zero_iff _).mpr h)
    have hle : A.valuation (v₀.evalAt f) ≤ 1 := (A.valuation_le_one_iff _).mpr haf
    have hnotlt : ¬ A.valuation (v₀.evalAt f) < 1 := fun h =>
      hnotmax ((A.valuation_lt_one_iff ⟨v₀.evalAt f, haf⟩).mpr h)
    exact le_antisymm hle (not_lt.mp hnotlt)

  have hfshape : f = algebraMap L F lam * (u * d⁻¹ ^ e) * ∏ w ∈ Z, (dw w)⁻¹ ^ n w := by
    rw [hf, hPcoe, Algebra.smul_def, mul_inv, inv_pow, ← Finset.prod_inv_distrib]
    rw [Finset.prod_congr rfl fun w _ => (inv_pow (dw w) (n w))]
    ring
  have hg_mem : u * d⁻¹ ^ e ∈ v₀.toValuationSubring := by
    have hg0 : u * d⁻¹ ^ e ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ (inv_ne_zero hd0))
    refine v₀.mem_toValuationSubring_of_ord_nonneg_alt hg0 ?_
    rw [v₀.ord_mul hu0 (pow_ne_zero _ (inv_ne_zero hd0)), ord_pow, v₀.ord_inv, hordv_d, ← hD v₀, ← he']
    ring_nf
    exact le_rfl
  have hdw_v₀ : ∀ w ∈ Z, (dw w)⁻¹ ∈ v₀.toValuationSubring ∧ v₀.evalAt (dw w)⁻¹ = (v₀.evalAt τ - w.evalAt τ)⁻¹ := by
    intro w hw
    obtain ⟨-, -, -, hreg', h0', -⟩ := hw_facts w hw
    obtain ⟨hwfib, hwne, -⟩ := hZmem w hw
    obtain ⟨hm, hev⟩ := inv_mem_and_evalAt_inv v₀ hv₀ h0' (hord_dw_other w hw v₀ rfl (Ne.symm hwne))
    refine ⟨hm, ?_⟩
    rw [hev, hdw_def]
    simp only
    rw [evalAt_sub_of_mem v₀ hv₀ (hregτ v₀ rfl) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq]
  have hevf : v₀.evalAt f = lam * v₀.evalAt (u * d⁻¹ ^ e) *
      ∏ w ∈ Z, (v₀.evalAt τ - w.evalAt τ)⁻¹ ^ n w := by
    have hm1 : algebraMap L F lam * (u * d⁻¹ ^ e) ∈ v₀.toValuationSubring :=
      mul_mem (v₀.algebraMap_mem' _) hg_mem
    have hm2 : ∀ w ∈ Z, (dw w)⁻¹ ^ n w ∈ v₀.toValuationSubring := fun w hw => pow_mem (hdw_v₀ w hw).1 _
    rw [hfshape, v₀.evalAt_mul_of_mem hv₀ hm1 (prod_mem hm2), v₀.evalAt_mul_of_mem hv₀ (v₀.algebraMap_mem' _) hg_mem,
      v₀.evalAt_algebraMap_eq, evalAt_prod_of_mem v₀ hv₀ _ _ hm2]
    congr 1
    refine Finset.prod_congr rfl fun w hw => ?_
    rw [evalAt_pow_of_mem v₀ hv₀ (hdw_v₀ w hw).1, (hdw_v₀ w hw).2]

  have hτne : ∀ w ∈ Z, v₀.evalAt τ - w.evalAt τ ≠ 0 := by
    intro w hw
    have := (hdw_v₀ w hw).2

    have h0 : v₀.evalAt (dw w) ≠ 0 :=
      v₀.evalAt_ne_zero_of_ord_eq_zero hv₀ (hw_facts w hw).2.2.2.2.1
        (hord_dw_other w hw v₀ rfl (Ne.symm (hZmem w hw).2.1))
    have hval : v₀.evalAt (dw w) = v₀.evalAt τ - w.evalAt τ := by
      rw [hdw_def]; simp only
      rw [evalAt_sub_of_mem v₀ hv₀ (hregτ v₀ rfl) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq]
    rwa [hval] at h0
  rw [hevf, map_mul, map_prod] at hval1
  simp only [map_pow, map_inv₀] at hval1

  have hprod_ne : ∏ w ∈ Z, (A.valuation (v₀.evalAt τ - w.evalAt τ))⁻¹ ^ n w ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (inv_ne_zero
      ((Valuation.ne_zero_iff _).mpr (hτne w hw)))
  have := eq_inv_of_mul_eq_one_left hval1
  rw [this, ← Finset.prod_inv_distrib]
  exact Finset.prod_congr rfl fun w _ => by rw [inv_pow, inv_inv]

end AlgebraicCurve.ConstantReduction.RoadD

namespace P2MRoadD

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem residue_evalAt_eq_evalAt_placeMap [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (f : F) (hf : f ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hreg : ∀ P, R.placeMap P = R.placeMap v₀ → f ∈ P.toValuationSubring) :
    IsLocalRing.residue A ⟨v₀.evalAt f, evalAt_mem_of_mem_integers R f hf v₀ hv₀ hreg⟩
      = (R.placeMap v₀).evalAt (R.residue ⟨f, hf⟩) :=
  (AlgebraicCurve.ConstantReduction.RoadD.evalAt_placeMap_residue_eq_residue_evalAt R f hf v₀ hv₀ hQ hreg).symm

theorem exists_evalAt_sub_evalAt_not_mem_maximalIdeal [HasPrincipalDivisors L F]
    (R : ConstantReduction A F Fbar) {ι : Type*} (x : ι → F) (hx : ∀ i, x i ∈ R.integers)
    (hsep : ∀ Q Q' : Place (ResidueField A) Fbar, Q ≠ Q' →
      ∃ i, Q.evalAt (R.residue ⟨x i, hx i⟩) ≠ Q'.evalAt (R.residue ⟨x i, hx i⟩))
    {v₀ w : Place L F} (hv₀ : v₀.IsRational) (hw₁ : w.IsRational)
    (hQ₀ : (R.placeMap v₀).IsRational) (hQw : (R.placeMap w).IsRational) (hw : R.placeMap w ≠ R.placeMap v₀)
    (hreg₀ : ∀ i P, R.placeMap P = R.placeMap v₀ → x i ∈ P.toValuationSubring)
    (hregw : ∀ i P, R.placeMap P = R.placeMap w → x i ∈ P.toValuationSubring) :
    ∃ i, (⟨v₀.evalAt (x i), evalAt_mem_of_mem_integers R (x i) (hx i) v₀ hv₀ (hreg₀ i)⟩
          - ⟨w.evalAt (x i), evalAt_mem_of_mem_integers R (x i) (hx i) w hw₁ (hregw i)⟩ : A)
        ∉ maximalIdeal A := by
  obtain ⟨i, hi⟩ := hsep (R.placeMap v₀) (R.placeMap w) (Ne.symm hw)
  refine ⟨i, fun hmem => hi ?_⟩
  have h1 := residue_evalAt_eq_evalAt_placeMap R (x i) (hx i) v₀ hv₀ hQ₀ (hreg₀ i)
  have h2 := residue_evalAt_eq_evalAt_placeMap R (x i) (hx i) w hw₁ hQw (hregw i)
  rw [← h1, ← h2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
  exact hmem

theorem dist_aux [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (τ : F) (hτ : τ ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1)
    {w : Place L F} (hw₁ : w.IsRational) (hw : R.placeMap w = R.placeMap v₀) (hne : w ≠ v₀) :
    let d : F := τ - algebraMap L F (v₀.evalAt τ)
    d ∈ R.integers ∧ (∀ hd : d ∈ R.integers, R.residue ⟨d, hd⟩ ≠ 0 ∧ (R.placeMap v₀).ord (R.residue ⟨d, hd⟩) = 1) ∧
      (∀ P, R.placeMap P = R.placeMap v₀ → d ∈ P.toValuationSubring) ∧
      v₀.ord d = 1 ∧ w.ord d = 0 ∧ d ≠ 0 ∧ w.evalAt τ ≠ v₀.evalAt τ := by
  intro d
  have ha : v₀.evalAt τ ∈ A := evalAt_mem_of_mem_integers R τ hτ v₀ hv₀ hregτ
  have hconst : algebraMap L F (v₀.evalAt τ) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ha
  have hd_mem : d ∈ R.integers := sub_mem hτ hconst
  have hres_d : R.residue ⟨d, hd_mem⟩ = R.residue ⟨τ, hτ⟩
      - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩)) := by
    have e1 : (⟨d, hd_mem⟩ : R.integers) = ⟨τ, hτ⟩ - ⟨algebraMap L F (v₀.evalAt τ), hconst⟩ := Subtype.ext rfl
    rw [e1, map_sub]
    congr 1
    have e2 : (⟨algebraMap L F (v₀.evalAt τ), hconst⟩ : R.integers)
        = ⟨algebraMap L F ((⟨v₀.evalAt τ, ha⟩ : A) : L), (R.algebraMap_mem_iff _).mpr (⟨v₀.evalAt τ, ha⟩ : A).2⟩ :=
      Subtype.ext rfl
    rw [e2, R.residue_algebraMap ⟨v₀.evalAt τ, ha⟩, residue_evalAt_eq_evalAt_placeMap R τ hτ v₀ hv₀ hQ hregτ]
  have hres_ne : R.residue ⟨d, hd_mem⟩ ≠ 0 := by
    intro h0
    rw [hres_d] at h0
    rw [h0, Place.ord_zero] at hunif
    exact zero_ne_one hunif
  have hd0 : d ≠ 0 := by
    intro h0; apply hres_ne
    have : (⟨d, hd_mem⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hreg_d : ∀ P, R.placeMap P = R.placeMap v₀ → d ∈ P.toValuationSubring := fun P hP =>
    sub_mem (hregτ P hP) (P.algebraMap_mem' _)

  have hval : v₀.evalAt d = 0 := by
    have e1 : v₀.evalAt d = v₀.evalAt τ - v₀.evalAt (algebraMap L F (v₀.evalAt τ)) := by
      apply v₀.algebraMap_residueField_injective
      rw [map_sub, v₀.algebraMap_evalAt hv₀ (hreg_d v₀ rfl), v₀.algebraMap_evalAt hv₀ (hregτ v₀ rfl),
        v₀.algebraMap_evalAt hv₀ (v₀.algebraMap_mem' _), ← map_sub]
      rfl
    rw [e1, v₀.evalAt_algebraMap_eq, sub_self]
  have h1 : 0 < v₀.ord d := ord_pos_of_evalAt_eq_zero v₀ hv₀ hd0 (hreg_d v₀ rfl) hval
  have h2 := ord_add_ord_le_ord_residue R d hd_mem hres_ne v₀ w hw hne hreg_d
  rw [hres_d, hunif] at h2
  have h3 : 0 ≤ w.ord d := ord_nonneg_of_mem w hd0 (hreg_d w hw)
  have hv₀1 : v₀.ord d = 1 := by omega
  have hw0 : w.ord d = 0 := by omega
  refine ⟨hd_mem, fun _ => ⟨hres_ne, by rw [hres_d, hunif]⟩, hreg_d, hv₀1, hw0, hd0, ?_⟩

  have hdw : w.evalAt d ≠ 0 := w.evalAt_ne_zero_of_ord_eq_zero hw₁ hd0 hw0
  intro heq
  apply hdw
  have e1 : w.evalAt d = w.evalAt τ - w.evalAt (algebraMap L F (v₀.evalAt τ)) := by
    apply w.algebraMap_residueField_injective
    rw [map_sub, w.algebraMap_evalAt hw₁ (hreg_d w hw), w.algebraMap_evalAt hw₁ (hregτ w hw),
      w.algebraMap_evalAt hw₁ (w.algebraMap_mem' _), ← map_sub]
    rfl
  rw [e1, w.evalAt_algebraMap_eq, heq, sub_self]

theorem ord_sub_const_eq_zero_of_ne [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (τ : F) (hτ : τ ∈ R.integers) (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1)
    {P : Place L F} (hP : R.placeMap P = R.placeMap v₀) (hne : P ≠ v₀) :
    P.ord (τ - algebraMap L F (v₀.evalAt τ)) = 0 := by

  have ha : v₀.evalAt τ ∈ A := evalAt_mem_of_mem_integers R τ hτ v₀ hv₀ hregτ
  have hconst : algebraMap L F (v₀.evalAt τ) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ha
  set d : F := τ - algebraMap L F (v₀.evalAt τ) with hd
  have hd_mem : d ∈ R.integers := sub_mem hτ hconst
  have hres_d : R.residue ⟨d, hd_mem⟩ = R.residue ⟨τ, hτ⟩
      - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩)) := by
    have e1 : (⟨d, hd_mem⟩ : R.integers) = ⟨τ, hτ⟩ - ⟨algebraMap L F (v₀.evalAt τ), hconst⟩ := Subtype.ext rfl
    rw [e1, map_sub]
    congr 1
    have e2 : (⟨algebraMap L F (v₀.evalAt τ), hconst⟩ : R.integers)
        = ⟨algebraMap L F ((⟨v₀.evalAt τ, ha⟩ : A) : L), (R.algebraMap_mem_iff _).mpr (⟨v₀.evalAt τ, ha⟩ : A).2⟩ :=
      Subtype.ext rfl
    rw [e2, R.residue_algebraMap ⟨v₀.evalAt τ, ha⟩, residue_evalAt_eq_evalAt_placeMap R τ hτ v₀ hv₀ hQ hregτ]
  have hres_ne : R.residue ⟨d, hd_mem⟩ ≠ 0 := by
    intro h0; rw [hres_d] at h0; rw [h0, Place.ord_zero] at hunif; exact zero_ne_one hunif
  have hd0 : d ≠ 0 := by
    intro h0; apply hres_ne
    have : (⟨d, hd_mem⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hreg_d : ∀ Q, R.placeMap Q = R.placeMap v₀ → d ∈ Q.toValuationSubring := fun Q hQ =>
    sub_mem (hregτ Q hQ) (Q.algebraMap_mem' _)
  have hval : v₀.evalAt d = 0 := by
    have e1 : v₀.evalAt d = v₀.evalAt τ - v₀.evalAt (algebraMap L F (v₀.evalAt τ)) := by
      apply v₀.algebraMap_residueField_injective
      rw [map_sub, v₀.algebraMap_evalAt hv₀ (hreg_d v₀ rfl), v₀.algebraMap_evalAt hv₀ (hregτ v₀ rfl),
        v₀.algebraMap_evalAt hv₀ (v₀.algebraMap_mem' _), ← map_sub]
      rfl
    rw [e1, v₀.evalAt_algebraMap_eq, sub_self]
  have h1 : 0 < v₀.ord d := ord_pos_of_evalAt_eq_zero v₀ hv₀ hd0 (hreg_d v₀ rfl) hval
  have h2 := ord_add_ord_le_ord_residue R d hd_mem hres_ne v₀ P hP hne hreg_d
  rw [hres_d, hunif] at h2
  have h3 : 0 ≤ P.ord d := ord_nonneg_of_mem P hd0 (hreg_d P hP)
  omega

theorem valuation_evalAt_sub_le [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    {ι : Type*} (x : ι → F) (hx : ∀ i, x i ∈ R.integers) (τ : F) (hτ : τ ∈ R.integers)
    (v₀ : Place L F) (hv₀ : v₀.IsRational) (hQ : (R.placeMap v₀).IsRational)
    (hregx : ∀ i P, R.placeMap P = R.placeMap v₀ → x i ∈ P.toValuationSubring)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1)
    {w : Place L F} (hw₁ : w.IsRational) (hw : R.placeMap w = R.placeMap v₀) (hne : w ≠ v₀) (i : ι) :
    A.valuation (v₀.evalAt (x i) - w.evalAt (x i)) ≤ A.valuation (v₀.evalAt τ - w.evalAt τ) ∧
    ((R.placeMap v₀).ord (R.residue ⟨x i, hx i⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨x i, hx i⟩))) = 1 →
      A.valuation (v₀.evalAt (x i) - w.evalAt (x i)) = A.valuation (v₀.evalAt τ - w.evalAt τ)) := by
  obtain ⟨hd_mem, hres_ne', hreg_d, hv₀1, hw0, hd0, hτne⟩ := dist_aux R τ hτ v₀ hv₀ hQ hregτ hunif hw₁ hw hne
  set d : F := τ - algebraMap L F (v₀.evalAt τ) with hd
  have hres_ne : R.residue ⟨d, hd_mem⟩ ≠ 0 := (hres_ne' hd_mem).1
  have hordd : (R.placeMap v₀).ord (R.residue ⟨d, hd_mem⟩) = 1 := (hres_ne' hd_mem).2

  have ha : v₀.evalAt (x i) ∈ A := evalAt_mem_of_mem_integers R (x i) (hx i) v₀ hv₀ (hregx i)
  have hconst : algebraMap L F (v₀.evalAt (x i)) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ha
  set n : F := x i - algebraMap L F (v₀.evalAt (x i)) with hn
  have hn_mem : n ∈ R.integers := sub_mem (hx i) hconst
  have hreg_n : ∀ P, R.placeMap P = R.placeMap v₀ → n ∈ P.toValuationSubring := fun P hP =>
    sub_mem (hregx i P hP) (P.algebraMap_mem' _)

  have hdu : IsUnit (⟨d, hd_mem⟩ : R.integers) := isUnit_of_residue_ne_zero R ⟨d, hd_mem⟩ hres_ne
  obtain ⟨ud, hud⟩ := hdu
  have hdinv_mem : d⁻¹ ∈ R.integers := by
    have : ((ud⁻¹ : (R.integers)ˣ) : R.integers).1 = d⁻¹ := by
      have h1 : ((ud⁻¹ : (R.integers)ˣ) : R.integers).1 * d = 1 := by
        have := congrArg (fun z : R.integers => (z : F)) ud.inv_mul
        simpa [hud] using this
      exact (eq_inv_of_mul_eq_one_left h1)
    rw [← this]; exact ((ud⁻¹ : (R.integers)ˣ) : R.integers).2

  set q : F := n * d⁻¹ with hq
  have hq_mem : q ∈ R.integers := mul_mem hn_mem hdinv_mem
  have hdP : ∀ P, R.placeMap P = R.placeMap v₀ → P ≠ v₀ → d⁻¹ ∈ P.toValuationSubring := fun P hP hPne =>
    P.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hd0)
      (by rw [P.ord_inv, ord_sub_const_eq_zero_of_ne R τ hτ v₀ hv₀ hQ hregτ hunif hP hPne, neg_zero])
  have hreg_q : ∀ P, R.placeMap P = R.placeMap v₀ → q ∈ P.toValuationSubring := by
    intro P hP
    by_cases hPv : P = v₀
    · subst hPv
      rcases eq_or_ne n 0 with hn0 | hn0
      · rw [hq, hn0, zero_mul]; exact zero_mem _
      · apply P.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hn0 (inv_ne_zero hd0))
        rw [P.ord_mul hn0 (inv_ne_zero hd0), P.ord_inv, hv₀1]
        have hvaln : P.evalAt n = 0 := by
          have e1 : P.evalAt n = P.evalAt (x i) - P.evalAt (algebraMap L F (P.evalAt (x i))) := by
            apply P.algebraMap_residueField_injective
            rw [map_sub, P.algebraMap_evalAt hv₀ (hreg_n P rfl), P.algebraMap_evalAt hv₀ (hregx i P rfl),
              P.algebraMap_evalAt hv₀ (P.algebraMap_mem' _), ← map_sub]
            rfl
          rw [e1, P.evalAt_algebraMap_eq, sub_self]
        have := ord_pos_of_evalAt_eq_zero P hv₀ hn0 (hreg_n P rfl) hvaln
        omega
    · exact mul_mem (hreg_n P hP) (hdP P hP hPv)

  have hqw : w.evalAt q ∈ A := evalAt_mem_of_mem_integers R q hq_mem w hw₁ (fun P hP => hreg_q P (hP.trans hw))
  have hnw : w.evalAt n = w.evalAt (x i) - v₀.evalAt (x i) := by
    have e1 : w.evalAt n = w.evalAt (x i) - w.evalAt (algebraMap L F (v₀.evalAt (x i))) := by
      apply w.algebraMap_residueField_injective
      rw [map_sub, w.algebraMap_evalAt hw₁ (hreg_n w hw), w.algebraMap_evalAt hw₁ (hregx i w hw),
        w.algebraMap_evalAt hw₁ (w.algebraMap_mem' _), ← map_sub]
      rfl
    rw [e1, w.evalAt_algebraMap_eq]
  have hdw : w.evalAt d = w.evalAt τ - v₀.evalAt τ := by
    have e1 : w.evalAt d = w.evalAt τ - w.evalAt (algebraMap L F (v₀.evalAt τ)) := by
      apply w.algebraMap_residueField_injective
      rw [map_sub, w.algebraMap_evalAt hw₁ (hreg_d w hw), w.algebraMap_evalAt hw₁ (hregτ w hw),
        w.algebraMap_evalAt hw₁ (w.algebraMap_mem' _), ← map_sub]
      rfl
    rw [e1, w.evalAt_algebraMap_eq]
  have hprod : w.evalAt n = w.evalAt q * w.evalAt d := by
    rw [← w.evalAt_mul_of_mem hw₁ (hreg_q w hw) (hreg_d w hw), hq, mul_assoc, inv_mul_cancel₀ hd0, mul_one]

  have hneg1 : v₀.evalAt (x i) - w.evalAt (x i) = -(w.evalAt n) := by rw [hnw]; ring
  have hneg2 : v₀.evalAt τ - w.evalAt τ = -(w.evalAt d) := by rw [hdw]; ring
  have hqle : A.valuation (w.evalAt q) ≤ 1 := (A.valuation_le_one_iff _).mpr hqw
  constructor
  · rw [hneg1, hneg2, Valuation.map_neg, Valuation.map_neg, hprod, Valuation.map_mul]
    exact mul_le_of_le_one_left' hqle
  ·
    intro htan
    rw [hneg1, hneg2, Valuation.map_neg, Valuation.map_neg, hprod, Valuation.map_mul]
    suffices hq1 : A.valuation (w.evalAt q) = 1 by rw [hq1, one_mul]

    have hres_n : R.residue ⟨n, hn_mem⟩ = R.residue ⟨x i, hx i⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨x i, hx i⟩)) := by
      have e1 : (⟨n, hn_mem⟩ : R.integers) = ⟨x i, hx i⟩ - ⟨algebraMap L F (v₀.evalAt (x i)), hconst⟩ := Subtype.ext rfl
      rw [e1, map_sub]
      congr 1
      have e2 : (⟨algebraMap L F (v₀.evalAt (x i)), hconst⟩ : R.integers)
          = ⟨algebraMap L F ((⟨v₀.evalAt (x i), ha⟩ : A) : L), (R.algebraMap_mem_iff _).mpr (⟨v₀.evalAt (x i), ha⟩ : A).2⟩ :=
        Subtype.ext rfl
      rw [e2, R.residue_algebraMap ⟨v₀.evalAt (x i), ha⟩,
        residue_evalAt_eq_evalAt_placeMap R (x i) (hx i) v₀ hv₀ hQ (hregx i)]
    have hres_n_ne : R.residue ⟨n, hn_mem⟩ ≠ 0 := by
      intro h0; rw [hres_n] at h0; rw [h0, Place.ord_zero] at htan; exact zero_ne_one htan
    have hres_dinv : R.residue ⟨d⁻¹, hdinv_mem⟩ = (R.residue ⟨d, hd_mem⟩)⁻¹ := by
      have hmul : R.residue ⟨d, hd_mem⟩ * R.residue ⟨d⁻¹, hdinv_mem⟩ = 1 := by
        rw [← map_mul]
        have : (⟨d, hd_mem⟩ : R.integers) * ⟨d⁻¹, hdinv_mem⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hd0)
        rw [this, map_one]
      exact (eq_inv_of_mul_eq_one_right hmul)
    have hres_q : R.residue ⟨q, hq_mem⟩ = R.residue ⟨n, hn_mem⟩ * (R.residue ⟨d, hd_mem⟩)⁻¹ := by
      have : (⟨q, hq_mem⟩ : R.integers) = ⟨n, hn_mem⟩ * ⟨d⁻¹, hdinv_mem⟩ := Subtype.ext rfl
      rw [this, map_mul, hres_dinv]
    have hord_q : (R.placeMap v₀).ord (R.residue ⟨q, hq_mem⟩) = 0 := by
      have hordn : (R.placeMap v₀).ord (R.residue ⟨n, hn_mem⟩) = 1 := by rw [hres_n, htan]
      rw [hres_q, (R.placeMap v₀).ord_mul hres_n_ne (inv_ne_zero hres_ne), (R.placeMap v₀).ord_inv, hordn, hordd]
      norm_num
    have hres_q_ne : R.residue ⟨q, hq_mem⟩ ≠ 0 := by
      rw [hres_q]; exact mul_ne_zero hres_n_ne (inv_ne_zero hres_ne)
    have hqbarval : (R.placeMap v₀).evalAt (R.residue ⟨q, hq_mem⟩) ≠ 0 :=
      (R.placeMap v₀).evalAt_ne_zero_of_ord_eq_zero hQ hres_q_ne hord_q

    have hklb := residue_evalAt_eq_evalAt_placeMap R q hq_mem w hw₁ (by rw [hw]; exact hQ)
      (fun P hP => hreg_q P (hP.trans hw))
    have hqbarval' : (R.placeMap w).evalAt (R.residue ⟨q, hq_mem⟩) ≠ 0 := by rw [hw]; exact hqbarval
    have hunitA : (⟨w.evalAt q, hqw⟩ : A) ∉ maximalIdeal A := by
      intro hm
      apply hqbarval'
      rw [← hklb]
      exact (IsLocalRing.residue_eq_zero_iff _).mpr hm
    have : IsUnit (⟨w.evalAt q, hqw⟩ : A) := by
      by_contra hu; exact hunitA ((mem_maximalIdeal _).mpr hu)
    exact (A.valuation_eq_one_iff ⟨w.evalAt q, hqw⟩).mp this

end P2MRoadD

namespace P2MRoadD

variable {L : Type*} [Field L] {A : ValuationSubring L}
variable {F : Type*} [Field F] [Algebra L F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

open Classical in

theorem sum_fibre_eq_of_support_subset (R : ConstantReduction A F Fbar)
    (D : Divisor L F) (T : Finset (Place L F)) (hT : D.support ⊆ T) (Q : Place (ResidueField A) Fbar) :
    Finsupp.mapDomain R.placeMap D Q = ∑ P ∈ T, if R.placeMap P = Q then D P else 0 := by
  classical
  rw [mapDomain_apply_eq_sum]
  apply Finset.sum_subset hT
  intro P _ hP
  rw [Finsupp.notMem_support_iff.mp hP]
  simp

theorem ord_eq_neg_of_chart [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (x : F) (hx : x ∈ R.integers) (hres : R.residue ⟨x, hx⟩ ≠ 0) (E' : Divisor L F)
    (Q : Place (ResidueField A) Fbar)
    (hlow : ∀ z, R.placeMap z = Q → -E' z ≤ z.ord x)
    (hbpf : Q.ord (R.residue ⟨x, hx⟩) = -(Finsupp.mapDomain R.placeMap E' Q)) :
    ∀ z, R.placeMap z = Q → z.ord x = -E' z := by
  classical
  have hx0 : x ≠ 0 := by
    intro h0; apply hres
    have : (⟨x, hx⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := L) (F := F) x hx0

  intro z hz
  set T : Finset (Place L F) := D.support ∪ E'.support ∪ {z} with hT
  have hDT : D.support ⊆ T := by
    intro P hP; simp only [hT, Finset.mem_union, Finset.mem_singleton]; exact Or.inl (Or.inl hP)
  have hET : E'.support ⊆ T := by
    intro P hP; simp only [hT, Finset.mem_union, Finset.mem_singleton]; exact Or.inl (Or.inr hP)
  have hzT : z ∈ T := by simp [hT]
  have h1 := R.mapDomain_placeMap ⟨x, hx⟩ hres D hD Q
  rw [sum_fibre_eq_of_support_subset R D T hDT Q] at h1
  have h2 := sum_fibre_eq_of_support_subset R E' T hET Q

  have hsum : ∑ P ∈ T, (if R.placeMap P = Q then D P + E' P else 0) = 0 := by
    have : ∑ P ∈ T, (if R.placeMap P = Q then D P + E' P else 0)
        = ∑ P ∈ T, (if R.placeMap P = Q then D P else 0) + ∑ P ∈ T, (if R.placeMap P = Q then E' P else 0) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun P _ => by split_ifs <;> simp
    rw [this, h1, ← h2, hbpf]
    ring_nf
  have hnn : ∀ P ∈ T, 0 ≤ (if R.placeMap P = Q then D P + E' P else 0) := by
    intro P _
    split_ifs with hP
    · rw [hD P]; linarith [hlow P hP]
    · exact le_rfl
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum z hzT
  rw [if_pos hz, hD z] at hterm
  linarith

theorem chartFun_mem [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (xi xj : F) (hxi : xi ∈ R.integers) (hxj : xj ∈ R.integers) (hres : R.residue ⟨xi, hxi⟩ ≠ 0)
    (E' : Divisor L F) (Q : Place (ResidueField A) Fbar)
    (hlowi : ∀ z, R.placeMap z = Q → -E' z ≤ z.ord xi)
    (hlowj : ∀ z, R.placeMap z = Q → xj ≠ 0 → -E' z ≤ z.ord xj)
    (hbpf : Q.ord (R.residue ⟨xi, hxi⟩) = -(Finsupp.mapDomain R.placeMap E' Q)) :
    xj * xi⁻¹ ∈ R.integers ∧ ∀ z, R.placeMap z = Q → xj * xi⁻¹ ∈ z.toValuationSubring := by
  have hxi0 : xi ≠ 0 := by
    intro h0; apply hres
    have : (⟨xi, hxi⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]

  have hu : IsUnit (⟨xi, hxi⟩ : R.integers) := isUnit_of_residue_ne_zero R ⟨xi, hxi⟩ hres
  obtain ⟨w, hw⟩ := hu
  have hinv : xi⁻¹ ∈ R.integers := by
    have : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 = xi⁻¹ := by
      have h1 : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * xi = 1 := by
        have := congrArg (fun z : R.integers => (z : F)) w.inv_mul
        simpa [hw] using this
      exact eq_inv_of_mul_eq_one_left h1
    rw [← this]; exact ((w⁻¹ : (R.integers)ˣ) : R.integers).2
  refine ⟨mul_mem hxj hinv, fun z hz => ?_⟩
  rcases eq_or_ne xj 0 with h0 | h0
  · rw [h0, zero_mul]; exact zero_mem _
  · apply z.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero h0 (inv_ne_zero hxi0))
    rw [z.ord_mul h0 (inv_ne_zero hxi0), z.ord_inv, ord_eq_neg_of_chart R xi hxi hres E' Q hlowi hbpf z hz]
    linarith [hlowj z hz h0]

theorem trivSection_mem [HasPrincipalDivisors L F] (R : ConstantReduction A F Fbar)
    (xi u : F) (hxi : xi ∈ R.integers) (hres : R.residue ⟨xi, hxi⟩ ≠ 0)
    (E' : Divisor L F) (Q : Place (ResidueField A) Fbar) (k : ℕ)
    (hlowi : ∀ z, R.placeMap z = Q → -E' z ≤ z.ord xi)
    (hbpf : Q.ord (R.residue ⟨xi, hxi⟩) = -(Finsupp.mapDomain R.placeMap E' Q))
    (hu0 : u ≠ 0) (hlowu : ∀ z, R.placeMap z = Q → -((k : ℤ) * E' z) ≤ z.ord u) :
    ∀ z, R.placeMap z = Q →
      u * (xi⁻¹) ^ k ∈ z.toValuationSubring ∧ z.ord (u * (xi⁻¹) ^ k) = z.ord u + (k : ℤ) * E' z := by
  have hxi0 : xi ≠ 0 := by
    intro h0; apply hres
    have : (⟨xi, hxi⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  intro z hz
  have hord : z.ord (u * (xi⁻¹) ^ k) = z.ord u + (k : ℤ) * E' z := by
    have hpow : ∀ n : ℕ, z.ord ((xi⁻¹) ^ n) = (n : ℤ) * E' z := by
      intro n
      induction n with
      | zero => simp [Place.ord_one]
      | succ n ih =>
        rw [pow_succ, z.ord_mul (pow_ne_zero n (inv_ne_zero hxi0)) (inv_ne_zero hxi0), ih, z.ord_inv,
          ord_eq_neg_of_chart R xi hxi hres E' Q hlowi hbpf z hz]
        push_cast; ring
    rw [z.ord_mul hu0 (pow_ne_zero k (inv_ne_zero hxi0)), hpow k]
  refine ⟨?_, hord⟩
  apply z.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hu0 (pow_ne_zero k (inv_ne_zero hxi0)))
  rw [hord]; linarith [hlowu z hz]

end P2MRoadD

namespace P2MJensenProx

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve"

variable {K : Type*} [Field K]

theorem iSup_mul_abv (ν : AbsoluteValue K ℝ) {r : ℕ} (c : K) (a : Fin r → K) :
    (⨆ i, ν (c * a i)) = ν c * ⨆ i, ν (a i) := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    simp_rw [map_mul]
    exact (Real.mul_iSup_of_nonneg (ν.nonneg c) _).symm

theorem prox_smul_left (ν : AbsoluteValue K ℝ) {r : ℕ} (c : K) (hc : c ≠ 0) (x y : Fin r → K)
    (hm : ∃ p : Fin r × Fin r, x p.1 * y p.2 - x p.2 * y p.1 ≠ 0) :
    prox ν (c • x) y = prox ν x y := by
  unfold prox
  have h1 : (⨆ i, ν ((c • x) i)) = ν c * ⨆ i, ν (x i) := by
    simp only [Pi.smul_apply, smul_eq_mul]; exact iSup_mul_abv ν c x
  have h2 : (⨆ p : Fin r × Fin r, ν ((c • x) p.1 * y p.2 - (c • x) p.2 * y p.1))
      = ν c * ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) := by
    have : ∀ p : Fin r × Fin r, (c • x) p.1 * y p.2 - (c • x) p.2 * y p.1 = c * (x p.1 * y p.2 - x p.2 * y p.1) := by
      intro p; simp only [Pi.smul_apply, smul_eq_mul]; ring
    simp_rw [this, map_mul]
    rcases isEmpty_or_nonempty (Fin r × Fin r) with h | h
    · simp
    · exact (Real.mul_iSup_of_nonneg (ν.nonneg c) _).symm
  rw [h1, h2]
  have hνc : 0 < ν c := ν.pos hc

  have key : ∀ S : ℝ, 0 ≤ S → Real.log (ν c * S) = (if S = 0 then 0 else Real.log (ν c)) + Real.log S := by
    intro S hS
    by_cases h0 : S = 0
    · simp [h0]
    · rw [if_neg h0, Real.log_mul hνc.ne' h0]
  have hSx : 0 ≤ ⨆ i, ν (x i) := by
    rcases isEmpty_or_nonempty (Fin r) with h | h
    · simp
    · exact Real.iSup_nonneg fun i => ν.nonneg _
  have hSm : 0 ≤ ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) := by
    rcases isEmpty_or_nonempty (Fin r × Fin r) with h | h
    · simp
    · exact Real.iSup_nonneg fun p => ν.nonneg _
  rw [key _ hSx, key _ hSm]

  by_cases hx0 : (⨆ i, ν (x i)) = 0
  · have hxz : ∀ i, x i = 0 := by
      intro i
      rcases isEmpty_or_nonempty (Fin r) with h | h
      · exact (IsEmpty.false i).elim
      · have hle : ν (x i) ≤ ⨆ i, ν (x i) := le_ciSup (f := fun i => ν (x i)) (Set.finite_range _).bddAbove i
        rw [hx0] at hle
        exact (AbsoluteValue.eq_zero ν).mp (le_antisymm hle (ν.nonneg _))
    have hm0 : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1)) = 0 := by
      rcases isEmpty_or_nonempty (Fin r × Fin r) with h | h
      · simp
      · have : ∀ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) = 0 := fun p => by
          rw [hxz p.1, hxz p.2]; simp
        simp_rw [this]; exact ciSup_const
    rw [if_pos hx0, if_pos hm0]; ring
  · rw [if_neg hx0]
    by_cases hm0 : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1)) = 0
    · exfalso
      obtain ⟨p, hp⟩ := hm
      haveI : Nonempty (Fin r × Fin r) := ⟨p⟩
      have hle : ν (x p.1 * y p.2 - x p.2 * y p.1) ≤ ⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1) :=
        le_ciSup (f := fun p : Fin r × Fin r => ν (x p.1 * y p.2 - x p.2 * y p.1)) (Set.finite_range _).bddAbove p
      rw [hm0] at hle
      exact hp ((AbsoluteValue.eq_zero ν).mp (le_antisymm hle (ν.nonneg _)))
    · rw [if_neg hm0]; ring

theorem prox_comm (ν : AbsoluteValue K ℝ) {r : ℕ} (x y : Fin r → K) : prox ν x y = prox ν y x := by
  unfold prox
  have : (⨆ p : Fin r × Fin r, ν (x p.1 * y p.2 - x p.2 * y p.1))
      = ⨆ p : Fin r × Fin r, ν (y p.1 * x p.2 - y p.2 * x p.1) := by
    apply Equiv.iSup_congr (Equiv.prodComm (Fin r) (Fin r))
    intro p
    simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
    congr 1; ring
  rw [this]; ring

theorem prox_smul_right (ν : AbsoluteValue K ℝ) {r : ℕ} (c : K) (hc : c ≠ 0) (x y : Fin r → K)
    (hm : ∃ p : Fin r × Fin r, x p.1 * y p.2 - x p.2 * y p.1 ≠ 0) :
    prox ν x (c • y) = prox ν x y := by
  rw [prox_comm, prox_smul_left ν c hc y x ?_, prox_comm]
  obtain ⟨p, hp⟩ := hm
  exact ⟨(p.2, p.1), by intro h; apply hp; linear_combination h⟩

theorem prox_map {K' : Type*} [Field K'] (φ : K →+* K') (ν : K → ℝ) (ν' : K' → ℝ)
    (hν : ∀ a, ν' (φ a) = ν a) {r : ℕ} (x y : Fin r → K) :
    prox ν' (fun i => φ (x i)) (fun i => φ (y i)) = prox ν x y := by
  unfold prox
  simp_rw [← map_mul, ← map_sub, hν]

theorem iSup_mul_abv' (ν : AbsoluteValue K ℝ) {ι₀ : Type*} [Finite ι₀] [Nonempty ι₀] (c : K) (a : ι₀ → K) :
    (⨆ i, ν (c * a i)) = ν c * ⨆ i, ν (a i) := by
  simp_rw [map_mul]
  haveI : Fintype ι₀ := Fintype.ofFinite ι₀
  exact (Real.mul_iSup_of_nonneg (ν.nonneg c) _).symm

end P2MJensenProx

namespace P2MJensenAh

variable {K : Type*} [Field K] {L₀ : Type*} [Field L₀] (ι : L₀ →+* K)
  (ν : AbsoluteValue L₀ ℝ) (A : ValuationSubring K) (hA : ∀ a : L₀, ν a ≤ 1 ↔ ι a ∈ A)
include hA

theorem le_iff {a b : L₀} (hb : b ≠ 0) : ν a ≤ ν b ↔ A.valuation (ι a) ≤ A.valuation (ι b) := by
  have hιb : ι b ≠ 0 := (map_ne_zero ι).mpr hb
  have hvb : A.valuation (ι b) ≠ 0 := by rwa [ne_eq, map_eq_zero]
  rw [← div_le_one (ν.pos hb), ← map_div₀, hA, map_div₀, ← A.valuation_le_one_iff, map_div₀,
    div_le_one₀ (zero_lt_iff.mpr hvb)]

theorem eq_of_valuation_eq {a b : L₀} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : A.valuation (ι a) = A.valuation (ι b)) : ν a = ν b :=
  le_antisymm ((le_iff ι ν A hA hb).mpr h.le) ((le_iff ι ν A hA ha).mpr h.ge)

theorem eq_one_iff_isUnit {a : L₀} (ha : ι a ∈ A) : ν a = 1 ↔ IsUnit (⟨ι a, ha⟩ : A) := by
  rw [ValuationSubring.valuation_eq_one_iff, ← (A.valuation).map_one, ← ι.map_one]
  constructor
  · intro h
    apply le_antisymm
    · exact (le_iff ι ν A hA one_ne_zero).mp (by rw [h, map_one])
    · have ha0 : a ≠ 0 := fun h0 => by rw [h0, map_zero] at h; exact zero_ne_one h
      exact (le_iff ι ν A hA ha0).mp (by rw [h, map_one])
  · intro h
    have h' : A.valuation (ι a) = A.valuation (ι 1) := h
    have ha0 : a ≠ 0 := by
      intro h0
      have : A.valuation (ι a) = 0 := by rw [h0, map_zero, map_zero]
      rw [this, eq_comm, map_eq_zero, map_one] at h'
      exact one_ne_zero h'
    have := eq_of_valuation_eq ι ν A hA ha0 one_ne_zero h'
    rwa [map_one] at this

theorem lt_one_iff_mem_maximalIdeal {a : L₀} (ha : ι a ∈ A) :
    ν a < 1 ↔ (⟨ι a, ha⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, ← eq_one_iff_isUnit ι ν A hA ha]
  have hle : ν a ≤ 1 := (hA a).mpr ha
  constructor
  · intro h h1; exact h.ne h1
  · intro h; exact lt_of_le_of_ne hle h

end P2MJensenAh

namespace P2MJensenC

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx"

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem stub_prox_chart {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j : Fin r) (hxj : x j = 1) (hyj : y j = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hy : ∀ i, ν (y i) ≤ 1) :
    prox ν x y = -Real.log (⨆ i, ν (x i - y i)) :=
  AlgebraicCurve.prox_eq_neg_log_iSup_sub_of_chart ν hna x y j hxj hyj hx hy

theorem stub_prox_far {L : Type*} [Field L]
    (ν : AbsoluteValue L ℝ) (hna : IsNonarchimedean ⇑ν) {r : ℕ}
    (x y : Fin r → L) (j b : Fin r) (hxj : x j = 1) (hyb : y b = 1)
    (hx : ∀ i, ν (x i) ≤ 1) (hyj : ν (y j) < 1) :
    prox ν x y = 0 :=
  AlgebraicCurve.prox_eq_zero_of_far_of_chart ν hna x y j b hxj hyb hx hyj

theorem prox_same_fibre [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* K) (ν : AbsoluteValue L₀ ℝ) (hna : IsNonarchimedean ⇑ν)
    (hA : ∀ a : L₀, ν a ≤ 1 ↔ ι a ∈ A)
    {r : ℕ} (x : Fin r → F) (hx : ∀ i, x i ∈ R.integers) (ī i₁ : Fin r) (hres : R.residue ⟨x ī, hx ī⟩ ≠ 0)
    (E' : Divisor K F) (Q : Place (ResidueField A) Fbar) (hQ : Q.IsRational)
    (hlow : ∀ j z, R.placeMap z = Q → x j ≠ 0 → -E' z ≤ z.ord (x j))
    (hbpf : Q.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q))
    (hunif : ∀ hmem : x i₁ * (x ī)⁻¹ ∈ R.integers, Q.ord (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩
        - algebraMap (ResidueField A) Fbar (Q.evalAt (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩))) = 1)
    {v₀ w : Place K F} (hv₀ : v₀.IsRational) (hw₁ : w.IsRational)
    (hv₀Q : R.placeMap v₀ = Q) (hwQ : R.placeMap w = Q) (hne : w ≠ v₀)
    (X₀ X : Fin r → L₀) (hX₀ : ∀ j, ι (X₀ j) = v₀.evalAt (x j * (x ī)⁻¹))
    (hX : ∀ j, ι (X j) = w.evalAt (x j * (x ī)⁻¹)) :
    prox ν X₀ X = -Real.log (ν (X₀ i₁ - X i₁)) ∧ X₀ i₁ ≠ X i₁ := by
  have hxī0 : x ī ≠ 0 := by
    intro h0; apply hres
    have : (⟨x ī, hx ī⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hlowī : ∀ z, R.placeMap z = Q → -E' z ≤ z.ord (x ī) := fun z hz => hlow ī z hz hxī0
  set S : Fin r → F := fun j => x j * (x ī)⁻¹ with hS
  have hSmem : ∀ j, S j ∈ R.integers ∧ ∀ z, R.placeMap z = Q → S j ∈ z.toValuationSubring := fun j =>
    chartFun_mem R (x ī) (x j) (hx ī) (hx j) hres E' Q hlowī (fun z hz h0 => hlow j z hz h0) hbpf
  have hSint : ∀ j, S j ∈ R.integers := fun j => (hSmem j).1
  have hSreg : ∀ j P, R.placeMap P = R.placeMap v₀ → S j ∈ P.toValuationSubring := fun j P hP =>
    (hSmem j).2 P (hP.trans hv₀Q)
  have hQv : (R.placeMap v₀).IsRational := by rw [hv₀Q]; exact hQ

  have hrow : ∀ (v : Place K F), v.IsRational → R.placeMap v = Q → ∀ j, v.evalAt (S j) ∈ A := by
    intro v hv hvQ j
    exact evalAt_mem_of_mem_integers R (S j) (hSint j) v hv (fun P hP => (hSmem j).2 P (hP.trans hvQ))
  have hone : ∀ (v : Place K F), v.evalAt (S ī) = 1 := by
    intro v; show v.evalAt (x ī * (x ī)⁻¹) = 1; rw [mul_inv_cancel₀ hxī0, v.evalAt_one]
  have hX₀ī : X₀ ī = 1 := ι.injective (by rw [hX₀ ī, map_one]; exact hone v₀)
  have hXī : X ī = 1 := ι.injective (by rw [hX ī, map_one]; exact hone w)
  have hX₀le : ∀ j, ν (X₀ j) ≤ 1 := fun j => (hA _).mpr (by rw [hX₀ j]; exact hrow v₀ hv₀ hv₀Q j)
  have hXle : ∀ j, ν (X j) ≤ 1 := fun j => (hA _).mpr (by rw [hX j]; exact hrow w hw₁ hwQ j)

  have hform := stub_prox_chart ν hna X₀ X ī hX₀ī hXī hX₀le hXle

  have hunif' : (R.placeMap v₀).ord (R.residue ⟨S i₁, hSint i₁⟩
      - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨S i₁, hSint i₁⟩))) = 1 := by
    rw [hv₀Q]; exact hunif (hSint i₁)
  have hwv : R.placeMap w = R.placeMap v₀ := hwQ.trans hv₀Q.symm
  have hdist := fun j => valuation_evalAt_sub_le R S hSint (S i₁) (hSint i₁) v₀ hv₀ hQv hSreg (hSreg i₁)
    hunif' hw₁ hwv hne j
  obtain ⟨-, -, -, -, -, -, hτne⟩ := dist_aux R (S i₁) (hSint i₁) v₀ hv₀ hQv (hSreg i₁) hunif' hw₁ hwv hne
  have hdiff : ∀ j, ι (X₀ j - X j) = v₀.evalAt (S j) - w.evalAt (S j) := fun j => by rw [map_sub, hX₀ j, hX j]
  have hne₁ : X₀ i₁ ≠ X i₁ := by
    intro h; apply hτne
    have := hdiff i₁
    rw [h, sub_self, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm
  have hdiff0 : X₀ i₁ - X i₁ ≠ 0 := sub_ne_zero.mpr hne₁
  refine ⟨?_, hne₁⟩
  rw [hform]
  haveI : Nonempty (Fin r) := ⟨ī⟩
  have hsup : (⨆ j, ν (X₀ j - X j)) = ν (X₀ i₁ - X i₁) := by
    apply le_antisymm
    · apply ciSup_le
      intro j
      apply (le_iff ι ν A hA hdiff0).mpr
      rw [hdiff j, hdiff i₁]
      exact (hdist j).1
    · exact le_ciSup (f := fun j => ν (X₀ j - X j)) (Set.finite_range _).bddAbove i₁
  rw [hsup]

end P2MJensenC

namespace P2MJensenC

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx"

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem ord_eq_zero_of_evalAt_ne_zero' {K' E : Type*} [Field K'] [Field E] [Algebra K' E] (v : Place K' E)
    (hv : v.IsRational) {f : E} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) : v.ord f = 0 := by
  have hres : IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩ ≠ 0 := by
    intro h0; apply h
    apply v.algebraMap_residueField_injective
    rw [v.algebraMap_evalAt hv hf, h0, map_zero]
  obtain ⟨u, hu⟩ := (IsLocalRing.residue_ne_zero_iff_isUnit _).mp hres
  have := v.ord_coe_unit u
  rwa [hu] at this

theorem evalAt_inv_of_ord_eq_zero' {K' E : Type*} [Field K'] [Field E] [Algebra K' E] (v : Place K' E)
    (hv : v.IsRational) {f : E} (hf : f ≠ 0) (h : v.ord f = 0) :
    f⁻¹ ∈ v.toValuationSubring ∧ v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  have hfm : f ∈ v.toValuationSubring := v.mem_toValuationSubring_of_ord_nonneg_alt hf h.ge
  have hfi : f⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hf) (by rw [v.ord_inv, h, neg_zero])
  refine ⟨hfi, ?_⟩
  have key : v.evalAt f * v.evalAt f⁻¹ = 1 := by
    rw [← v.evalAt_mul_of_mem hv hfm hfi, mul_inv_cancel₀ hf, v.evalAt_one]
  exact eq_inv_of_mul_eq_one_right key

theorem inv_mem_residue_inv (R : ConstantReduction A F Fbar) (x : F) (hx : x ∈ R.integers)
    (hres : R.residue ⟨x, hx⟩ ≠ 0) :
    ∃ hinv : x⁻¹ ∈ R.integers, R.residue ⟨x⁻¹, hinv⟩ = (R.residue ⟨x, hx⟩)⁻¹ := by
  have hx0 : x ≠ 0 := by
    intro h0; apply hres
    have : (⟨x, hx⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  obtain ⟨w, hw⟩ := isUnit_of_residue_ne_zero R ⟨x, hx⟩ hres
  have hinv : x⁻¹ ∈ R.integers := by
    have : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 = x⁻¹ := by
      have h1 : ((w⁻¹ : (R.integers)ˣ) : R.integers).1 * x = 1 := by
        have := congrArg (fun z : R.integers => (z : F)) w.inv_mul
        simpa [hw] using this
      exact eq_inv_of_mul_eq_one_left h1
    rw [← this]; exact ((w⁻¹ : (R.integers)ˣ) : R.integers).2
  refine ⟨hinv, ?_⟩
  have hmul : R.residue ⟨x, hx⟩ * R.residue ⟨x⁻¹, hinv⟩ = 1 := by
    rw [← map_mul]
    have : (⟨x, hx⟩ : R.integers) * ⟨x⁻¹, hinv⟩ = 1 := Subtype.ext (mul_inv_cancel₀ hx0)
    rw [this, map_one]
  exact eq_inv_of_mul_eq_one_right hmul

theorem prox_diff_fibre [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* K) (ν : AbsoluteValue L₀ ℝ) (hna : IsNonarchimedean ⇑ν)
    (hA : ∀ a : L₀, ν a ≤ 1 ↔ ι a ∈ A)
    {r : ℕ} (x : Fin r → F) (hx : ∀ i, x i ∈ R.integers) (E' : Divisor K F)
    (ī ī' : Fin r) (Q Q' : Place (ResidueField A) Fbar) (hQ : Q.IsRational) (hQ' : Q'.IsRational)
    (hQQ' : Q ≠ Q')
    (hresī : R.residue ⟨x ī, hx ī⟩ ≠ 0) (hresī' : R.residue ⟨x ī', hx ī'⟩ ≠ 0)
    (hlow : ∀ j z, (R.placeMap z = Q ∨ R.placeMap z = Q') → x j ≠ 0 → -E' z ≤ z.ord (x j))
    (hbpf : Q.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q))
    (hbpf' : Q'.ord (R.residue ⟨x ī', hx ī'⟩) = -(Finsupp.mapDomain R.placeMap E' Q'))
    (hsep : Q'.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q') →
      ∀ hmem : ∀ j, x j * (x ī)⁻¹ ∈ R.integers,
      ∃ j, Q.evalAt (R.residue ⟨x j * (x ī)⁻¹, hmem j⟩) ≠ Q'.evalAt (R.residue ⟨x j * (x ī)⁻¹, hmem j⟩))
    {v₀ w : Place K F} (hv₀ : v₀.IsRational) (hw₁ : w.IsRational)
    (hv₀Q : R.placeMap v₀ = Q) (hwQ' : R.placeMap w = Q')
    (X₀ X : Fin r → L₀) (hX₀ : ∀ j, ι (X₀ j) = v₀.evalAt (x j * (x ī)⁻¹))
    (hX : ∀ j, ι (X j) = w.evalAt (x j * (x ī')⁻¹)) :
    prox ν X₀ X = 0 ∧ ∃ p : Fin r × Fin r, X₀ p.1 * X p.2 - X₀ p.2 * X p.1 ≠ 0 := by
  have hne0 : ∀ i, R.residue ⟨x i, hx i⟩ ≠ 0 → x i ≠ 0 := by
    intro i h h0; apply h
    have : (⟨x i, hx i⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hxī0 := hne0 ī hresī
  have hxī'0 := hne0 ī' hresī'
  have hSmem : ∀ j, x j * (x ī)⁻¹ ∈ R.integers ∧ ∀ z, R.placeMap z = Q → x j * (x ī)⁻¹ ∈ z.toValuationSubring :=
    fun j => chartFun_mem R (x ī) (x j) (hx ī) (hx j) hresī E' Q (fun z hz => hlow ī z (Or.inl hz) hxī0)
      (fun z hz h0 => hlow j z (Or.inl hz) h0) hbpf
  have hTmem : ∀ j, x j * (x ī')⁻¹ ∈ R.integers ∧ ∀ z, R.placeMap z = Q' → x j * (x ī')⁻¹ ∈ z.toValuationSubring :=
    fun j => chartFun_mem R (x ī') (x j) (hx ī') (hx j) hresī' E' Q' (fun z hz => hlow ī' z (Or.inr hz) hxī'0)
      (fun z hz h0 => hlow j z (Or.inr hz) h0) hbpf'
  have hrow₀ : ∀ j, v₀.evalAt (x j * (x ī)⁻¹) ∈ A := fun j =>
    evalAt_mem_of_mem_integers R _ (hSmem j).1 v₀ hv₀ (fun P hP => (hSmem j).2 P (hP.trans hv₀Q))
  have hroww : ∀ j, w.evalAt (x j * (x ī')⁻¹) ∈ A := fun j =>
    evalAt_mem_of_mem_integers R _ (hTmem j).1 w hw₁ (fun P hP => (hTmem j).2 P (hP.trans hwQ'))
  have hX₀le : ∀ j, ν (X₀ j) ≤ 1 := fun j => (hA _).mpr (by rw [hX₀ j]; exact hrow₀ j)
  have hXle : ∀ j, ν (X j) ≤ 1 := fun j => (hA _).mpr (by rw [hX j]; exact hroww j)
  have hX₀ī : X₀ ī = 1 := ι.injective (by rw [hX₀ ī, map_one, mul_inv_cancel₀ hxī0, v₀.evalAt_one])
  have hXī' : X ī' = 1 := ι.injective (by rw [hX ī', map_one, mul_inv_cancel₀ hxī'0, w.evalAt_one])
  rcases (hXle ī).lt_or_eq with hlt | heq
  · refine ⟨stub_prox_far ν hna X₀ X ī ī' hX₀ī hXī' hX₀le hlt, (ī, ī'), ?_⟩
    rw [hX₀ī, hXī', one_mul]
    intro h0
    have h1 : X₀ ī' * X ī = 1 := by linear_combination -h0
    have : ν (X₀ ī' * X ī) < 1 := by
      rw [map_mul]
      calc ν (X₀ ī') * ν (X ī) ≤ 1 * ν (X ī) := by
            exact mul_le_mul_of_nonneg_right (hX₀le ī') (ν.nonneg _)
        _ = ν (X ī) := one_mul _
        _ < 1 := hlt
    rw [h1, map_one] at this
    exact lt_irrefl _ this

  set T : F := x ī * (x ī')⁻¹ with hT
  have hTint : T ∈ R.integers := (hTmem ī).1
  have hTreg : ∀ P, R.placeMap P = R.placeMap w → T ∈ P.toValuationSubring := fun P hP =>
    (hTmem ī).2 P (hP.trans hwQ')
  have hQw : (R.placeMap w).IsRational := by rw [hwQ']; exact hQ'
  have hTw : w.evalAt T ∈ A := hroww ī
  have hXī_mem : ι (X ī) ∈ A := by rw [hX ī]; exact hTw
  have hunitA : IsUnit (⟨ι (X ī), hXī_mem⟩ : A) := (eq_one_iff_isUnit ι ν A hA hXī_mem).mp heq
  have hresA : IsLocalRing.residue A ⟨w.evalAt T, hTw⟩ ≠ 0 := by
    have e : (⟨ι (X ī), hXī_mem⟩ : A) = ⟨w.evalAt T, hTw⟩ := Subtype.ext (hX ī)
    rw [← e]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hunitA
  have hklbT := residue_evalAt_eq_evalAt_placeMap R T hTint w hw₁ hQw hTreg
  have hTval : (R.placeMap w).evalAt (R.residue ⟨T, hTint⟩) ≠ 0 := by rw [← hklbT]; exact hresA
  have hTmem' : R.residue ⟨T, hTint⟩ ∈ (R.placeMap w).toValuationSubring :=
    AlgebraicCurve.ConstantReduction.RoadD.residue_mem_placeMap_toValuationSubring R T hTint w hw₁ hQw hTreg
  have hordT : (R.placeMap w).ord (R.residue ⟨T, hTint⟩) = 0 :=
    ord_eq_zero_of_evalAt_ne_zero' _ hQw hTmem' hTval
  obtain ⟨hinv', hres_inv'⟩ := inv_mem_residue_inv R (x ī') (hx ī') hresī'
  have hresT : R.residue ⟨T, hTint⟩ = R.residue ⟨x ī, hx ī⟩ * (R.residue ⟨x ī', hx ī'⟩)⁻¹ := by
    have : (⟨T, hTint⟩ : R.integers) = ⟨x ī, hx ī⟩ * ⟨(x ī')⁻¹, hinv'⟩ := Subtype.ext rfl
    rw [this, map_mul, hres_inv']
  have hch : Q'.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q') := by
    rw [hwQ', hresT, Q'.ord_mul hresī (inv_ne_zero hresī'), Q'.ord_inv, hbpf'] at hordT
    linarith

  have hS'mem : ∀ j, x j * (x ī)⁻¹ ∈ R.integers ∧ ∀ z, R.placeMap z = Q' → x j * (x ī)⁻¹ ∈ z.toValuationSubring :=
    fun j => chartFun_mem R (x ī) (x j) (hx ī) (hx j) hresī E' Q' (fun z hz => hlow ī z (Or.inr hz) hxī0)
      (fun z hz h0 => hlow j z (Or.inr hz) h0) hch
  have hroww' : ∀ j, w.evalAt (x j * (x ī)⁻¹) ∈ A := fun j =>
    evalAt_mem_of_mem_integers R _ (hS'mem j).1 w hw₁ (fun P hP => (hS'mem j).2 P (hP.trans hwQ'))

  have hXī0 : X ī ≠ 0 := fun h0 => by rw [h0, map_zero] at heq; exact zero_ne_one heq
  have hTw0 : w.evalAt T ≠ 0 := by rw [← hX ī]; exact (map_ne_zero ι).mpr hXī0
  have hordTw : w.ord T = 0 := ord_eq_zero_of_evalAt_ne_zero' w hw₁ (hTreg w rfl) hTw0
  have hT0 : T ≠ 0 := mul_ne_zero hxī0 (inv_ne_zero hxī'0)
  obtain ⟨hTinv_mem, hTinv_val⟩ := evalAt_inv_of_ord_eq_zero' w hw₁ hT0 hordTw
  set X'' : Fin r → L₀ := fun j => X j * (X ī)⁻¹ with hX''def
  have hX'' : ∀ j, ι (X'' j) = w.evalAt (x j * (x ī)⁻¹) := by
    intro j
    have hsplit : x j * (x ī)⁻¹ = (x j * (x ī')⁻¹) * T⁻¹ := by
      rw [hT]; field_simp
    rw [hsplit, w.evalAt_mul_of_mem hw₁ ((hTmem j).2 w hwQ') hTinv_mem, hTinv_val, hX''def]
    simp only []
    rw [map_mul, map_inv₀, hX j, hX ī]
  have hXsmul : X = (X ī) • X'' := by
    funext j; simp only [hX''def, Pi.smul_apply, smul_eq_mul]; field_simp

  have hSint : ∀ j, x j * (x ī)⁻¹ ∈ R.integers := fun j => (hSmem j).1
  obtain ⟨j₀, hj₀⟩ := hsep hch hSint
  have hQv₀ : (R.placeMap v₀).IsRational := by rw [hv₀Q]; exact hQ
  have h1 := residue_evalAt_eq_evalAt_placeMap R (x j₀ * (x ī)⁻¹) (hSint j₀) v₀ hv₀ hQv₀
    (fun P hP => (hSmem j₀).2 P (hP.trans hv₀Q))
  have h2 := residue_evalAt_eq_evalAt_placeMap R (x j₀ * (x ī)⁻¹) (hSint j₀) w hw₁ hQw
    (fun P hP => (hS'mem j₀).2 P (hP.trans hwQ'))
  rw [← hv₀Q, ← hwQ'] at hj₀
  have hdiff_mem : ι (X₀ j₀ - X'' j₀) ∈ A := by
    rw [map_sub, hX₀ j₀, hX'' j₀]; exact sub_mem (hrow₀ j₀) (hroww' j₀)
  have hdiff_unit : ν (X₀ j₀ - X'' j₀) = 1 := by
    have hle : ν (X₀ j₀ - X'' j₀) ≤ 1 := (hA _).mpr hdiff_mem
    by_contra hne1
    have hlt : ν (X₀ j₀ - X'' j₀) < 1 := lt_of_le_of_ne hle hne1
    have hmax := (lt_one_iff_mem_maximalIdeal ι ν A hA hdiff_mem).mp hlt
    apply hj₀
    rw [← h1, ← h2, ← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    have e : (⟨v₀.evalAt (x j₀ * (x ī)⁻¹), evalAt_mem_of_mem_integers R _ (hSint j₀) v₀ hv₀
          (fun P hP => (hSmem j₀).2 P (hP.trans hv₀Q))⟩
        - ⟨w.evalAt (x j₀ * (x ī)⁻¹), evalAt_mem_of_mem_integers R _ (hSint j₀) w hw₁
          (fun P hP => (hS'mem j₀).2 P (hP.trans hwQ'))⟩ : A)
        = ⟨ι (X₀ j₀ - X'' j₀), hdiff_mem⟩ := by
      apply Subtype.ext
      show v₀.evalAt (x j₀ * (x ī)⁻¹) - w.evalAt (x j₀ * (x ī)⁻¹) = ι (X₀ j₀ - X'' j₀)
      rw [map_sub, hX₀ j₀, hX'' j₀]
    rw [e]; exact hmax
  have hdiff_ne : X₀ j₀ - X'' j₀ ≠ 0 := fun h0 => by rw [h0, map_zero] at hdiff_unit; exact zero_ne_one hdiff_unit

  have hX''ī : X'' ī = 1 := by simp only [hX''def]; exact mul_inv_cancel₀ hXī0
  have hminor : ∃ p : Fin r × Fin r, X₀ p.1 * X'' p.2 - X₀ p.2 * X'' p.1 ≠ 0 :=
    ⟨(ī, j₀), by rw [hX₀ī, hX''ī, one_mul, mul_one]; intro h; apply hdiff_ne; linear_combination -h⟩
  refine ⟨?_, ?_⟩
  swap
  · obtain ⟨p, hp⟩ := hminor
    refine ⟨p, ?_⟩
    rw [hXsmul]
    simp only [Pi.smul_apply, smul_eq_mul]
    intro h0; apply hp
    have : X ī * (X₀ p.1 * X'' p.2 - X₀ p.2 * X'' p.1) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left hXī0
  rw [hXsmul, prox_smul_right ν (X ī) hXī0 X₀ X'' hminor]
  have hX''le : ∀ j, ν (X'' j) ≤ 1 := fun j => (hA _).mpr (by rw [hX'' j]; exact hroww' j)
  rw [stub_prox_chart ν hna X₀ X'' ī hX₀ī hX''ī hX₀le hX''le]
  have hsup : (⨆ j, ν (X₀ j - X'' j)) = 1 := by
    haveI : Nonempty (Fin r) := ⟨ī⟩
    apply le_antisymm
    · apply ciSup_le; intro j
      calc ν (X₀ j - X'' j) = ν (X₀ j + -X'' j) := by rw [sub_eq_add_neg]
        _ ≤ max (ν (X₀ j)) (ν (-X'' j)) := hna _ _
        _ ≤ 1 := max_le (hX₀le j) (by rw [ν.map_neg]; exact hX''le j)
    · rw [← hdiff_unit]
      exact le_ciSup (f := fun j => ν (X₀ j - X'' j)) (Set.finite_range _).bddAbove j₀
  rw [hsup, Real.log_one, neg_zero]

end P2MJensenC

namespace P2MJensenD

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenC"

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem sum_mul_neg_log_eq {L₀ : Type*} [Field L₀] (ν : AbsoluteValue L₀ ℝ) {α : Type*} (T : Finset α)
    (n : α → ℕ) (z : α → L₀) (hz : ∀ w ∈ T, z w ≠ 0) :
    ∑ w ∈ T, (n w : ℝ) * (-Real.log (ν (z w))) = -Real.log (ν (∏ w ∈ T, z w ^ n w)) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have hT0 : ν (∏ w ∈ T, z w ^ n w) ≠ 0 :=
      (AbsoluteValue.ne_zero_iff ν).mpr
        (Finset.prod_ne_zero_iff.mpr fun w hw => pow_ne_zero _ (hz w (Finset.mem_insert_of_mem hw)))
    rw [Finset.sum_insert ha, Finset.prod_insert ha, map_mul, map_pow,
      Real.log_mul (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr (hz a (Finset.mem_insert_self a T)))) hT0,
      Real.log_pow, ih (fun w hw => hz w (Finset.mem_insert_of_mem hw))]
    ring

end P2MJensenD

namespace P2MJensenD

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenC"

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

open Classical in

theorem sum_prox_eq [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* K) (ν : AbsoluteValue L₀ ℝ) (hna : IsNonarchimedean ⇑ν)
    (hA : ∀ a : L₀, ν a ≤ 1 ↔ ι a ∈ A)
    {r : ℕ} (x : Fin r → F) (hx : ∀ i, x i ∈ R.integers) (E' : Divisor K F)
    (hlow : ∀ j z, x j ≠ 0 → -E' z ≤ z.ord (x j))
    (Q : Place (ResidueField A) Fbar) (hQ : Q.IsRational) (ī i₁ : Fin r)
    (hresī : R.residue ⟨x ī, hx ī⟩ ≠ 0)
    (hbpf : Q.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q))
    (hunif : ∀ hmem : x i₁ * (x ī)⁻¹ ∈ R.integers, Q.ord (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩
        - algebraMap (ResidueField A) Fbar (Q.evalAt (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩))) = 1)
    (B : Divisor K F) (hBnn : ∀ w, 0 ≤ B w)
    (cw : Place K F → Fin r) (hcwQ : ∀ w ∈ B.support, R.placeMap w = Q → cw w = ī)
    (hres' : ∀ w ∈ B.support, R.residue ⟨x (cw w), hx (cw w)⟩ ≠ 0)
    (hbpf' : ∀ w ∈ B.support, (R.placeMap w).ord (R.residue ⟨x (cw w), hx (cw w)⟩)
        = -(Finsupp.mapDomain R.placeMap E' (R.placeMap w)))
    (hsep' : ∀ w ∈ B.support, R.placeMap w ≠ Q →
        (R.placeMap w).ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' (R.placeMap w)) →
        ∀ hmem : ∀ j, x j * (x ī)⁻¹ ∈ R.integers,
        ∃ j, Q.evalAt (R.residue ⟨x j * (x ī)⁻¹, hmem j⟩) ≠ (R.placeMap w).evalAt (R.residue ⟨x j * (x ī)⁻¹, hmem j⟩))
    (hrat : ∀ w ∈ B.support, w.IsRational ∧ (R.placeMap w).IsRational)
    {v₀ : Place K F} (hv₀ : v₀.IsRational) (hv₀Q : R.placeMap v₀ = Q)
    (X₀ : Fin r → L₀) (hX₀ : ∀ j, ι (X₀ j) = v₀.evalAt (x j * (x ī)⁻¹))
    (Xw : Place K F → Fin r → L₀)
    (hXw : ∀ w ∈ B.support, ∀ j, ι (Xw w j) = w.evalAt (x j * (x (cw w))⁻¹)) :
    (∑ w ∈ (B.erase v₀).support, ((B.erase v₀) w : ℝ) * prox ν X₀ (Xw w))
        = -Real.log (ν (∏ w ∈ (B.erase v₀).support.filter (fun w => R.placeMap w = Q),
              (X₀ i₁ - Xw w i₁) ^ (B w).toNat))
      ∧ (∀ w ∈ (B.erase v₀).support, R.placeMap w = Q → X₀ i₁ ≠ Xw w i₁)
      ∧ (∀ w ∈ (B.erase v₀).support, ∃ p : Fin r × Fin r, X₀ p.1 * Xw w p.2 - X₀ p.2 * Xw w p.1 ≠ 0) := by
  have hsuppE : (B.erase v₀).support = B.support.erase v₀ := Finsupp.support_erase
  have hmemT : ∀ w ∈ (B.erase v₀).support, w ∈ B.support ∧ w ≠ v₀ := by
    intro w hw; rw [hsuppE, Finset.mem_erase] at hw; exact ⟨hw.2, hw.1⟩

  have hfib : ∀ w ∈ (B.erase v₀).support, R.placeMap w = Q →
      prox ν X₀ (Xw w) = -Real.log (ν (X₀ i₁ - Xw w i₁)) ∧ X₀ i₁ ≠ Xw w i₁ := by
    intro w hw hwQ
    obtain ⟨hwB, hne⟩ := hmemT w hw
    have hXw' : ∀ j, ι (Xw w j) = w.evalAt (x j * (x ī)⁻¹) := by
      intro j; rw [hXw w hwB j, hcwQ w hwB hwQ]
    exact prox_same_fibre R ι ν hna hA x hx ī i₁ hresī E' Q hQ (fun j z _ h0 => hlow j z h0) hbpf hunif
      hv₀ (hrat w hwB).1 hv₀Q hwQ hne X₀ (Xw w) hX₀ hXw'

  have hfar : ∀ w ∈ (B.erase v₀).support, R.placeMap w ≠ Q → prox ν X₀ (Xw w) = 0
      ∧ ∃ p : Fin r × Fin r, X₀ p.1 * Xw w p.2 - X₀ p.2 * Xw w p.1 ≠ 0 := by
    intro w hw hwQ
    obtain ⟨hwB, hne⟩ := hmemT w hw
    exact prox_diff_fibre R ι ν hna hA x hx E' ī (cw w) Q (R.placeMap w) hQ (hrat w hwB).2 (Ne.symm hwQ)
      hresī (hres' w hwB) (fun j z _ h0 => hlow j z h0) hbpf (hbpf' w hwB) (hsep' w hwB hwQ)
      hv₀ (hrat w hwB).1 hv₀Q rfl X₀ (Xw w) hX₀ (hXw w hwB)

  have hxī0 : x ī ≠ 0 := by
    intro h0; apply hresī
    have : (⟨x ī, hx ī⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hX₀ī : X₀ ī = 1 := ι.injective (by rw [hX₀ ī, map_one, mul_inv_cancel₀ hxī0, v₀.evalAt_one])
  refine ⟨?_, fun w hw hwQ => (hfib w hw hwQ).2, ?_⟩
  swap
  · intro w hw
    by_cases hwQ : R.placeMap w = Q
    · obtain ⟨hwB, hne⟩ := hmemT w hw
      have hXwī : Xw w ī = 1 := by
        apply ι.injective
        rw [hXw w hwB ī, hcwQ w hwB hwQ, map_one, mul_inv_cancel₀ hxī0, w.evalAt_one]
      refine ⟨(ī, i₁), ?_⟩
      rw [hX₀ī, hXwī, one_mul, mul_one]
      exact sub_ne_zero.mpr (hfib w hw hwQ).2.symm
    · exact (hfar w hw hwQ).2

  rw [← Finset.sum_filter_add_sum_filter_not _ (fun w => R.placeMap w = Q)]
  have h2 : ∑ w ∈ (B.erase v₀).support.filter (fun w => ¬ R.placeMap w = Q),
      ((B.erase v₀) w : ℝ) * prox ν X₀ (Xw w) = 0 := by
    apply Finset.sum_eq_zero
    intro w hw
    rw [Finset.mem_filter] at hw
    rw [(hfar w hw.1 hw.2).1, mul_zero]
  rw [h2, add_zero]
  have h1 : ∑ w ∈ (B.erase v₀).support.filter (fun w => R.placeMap w = Q),
      ((B.erase v₀) w : ℝ) * prox ν X₀ (Xw w)
      = ∑ w ∈ (B.erase v₀).support.filter (fun w => R.placeMap w = Q),
          ((B w).toNat : ℝ) * (-Real.log (ν (X₀ i₁ - Xw w i₁))) := by
    apply Finset.sum_congr rfl
    intro w hw
    rw [Finset.mem_filter] at hw
    obtain ⟨hwB, hne⟩ := hmemT w hw.1
    rw [(hfib w hw.1 hw.2).1, Finsupp.erase_ne hne]
    congr 1
    have : ((B w).toNat : ℤ) = B w := Int.toNat_of_nonneg (hBnn w)
    exact_mod_cast this.symm
  rw [h1]
  exact sum_mul_neg_log_eq ν _ (fun w => (B w).toNat) (fun w => X₀ i₁ - Xw w i₁)
    (fun w hw => by
      rw [Finset.mem_filter] at hw
      exact sub_ne_zero.mpr (hfib w hw.1 hw.2).2)

end P2MJensenD

namespace P2MJensenD

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenC"

variable {K : Type*} [Field K] {A : ValuationSubring K}
variable {F : Type*} [Field F] [Algebra K F]
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

open Classical in

theorem valuation_regVal_eq [HasPrincipalDivisors K F] (R : ConstantReduction A F Fbar)
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* K)
    {r : ℕ} (x : Fin r → F) (hx : ∀ i, x i ∈ R.integers) (E' : Divisor K F)
    (hlow : ∀ j z, x j ≠ 0 → -E' z ≤ z.ord (x j))
    (Q : Place (ResidueField A) Fbar) (hQ : Q.IsRational) (ī i₁ : Fin r)
    (hresī : R.residue ⟨x ī, hx ī⟩ ≠ 0)
    (hbpf : Q.ord (R.residue ⟨x ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q))
    (hunif : ∀ hmem : x i₁ * (x ī)⁻¹ ∈ R.integers, Q.ord (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩
        - algebraMap (ResidueField A) Fbar (Q.evalAt (R.residue ⟨x i₁ * (x ī)⁻¹, hmem⟩))) = 1)
    (k : ℕ) (u : F) (hu0 : u ≠ 0) (hlowu : ∀ z, -((k : ℤ) * E' z) ≤ z.ord u)
    (B : Divisor K F) (hB : ∀ w, B w = w.ord u + (k : ℤ) * E' w)
    (lam : K) (hlamU : lam • (u * ((x ī)⁻¹) ^ k) ∈ R.integers)
    (hunit : R.residue ⟨lam • (u * ((x ī)⁻¹) ^ k), hlamU⟩ ≠ 0)
    (hratfib : ∀ P, R.placeMap P = Q → P.IsRational)
    {v₀ : Place K F} (hv₀ : v₀.IsRational) (hv₀Q : R.placeMap v₀ = Q)
    (X₀ : Fin r → L₀) (hX₀ : ∀ j, ι (X₀ j) = v₀.evalAt (x j * (x ī)⁻¹))
    (Xw : Place K F → Fin r → L₀)
    (hXw : ∀ w ∈ B.support, R.placeMap w = Q → ∀ j, ι (Xw w j) = w.evalAt (x j * (x ī)⁻¹)) :
    A.valuation (lam * v₀.evalAt ((u * ((x ī)⁻¹) ^ k)
        * ((x i₁ * (x ī)⁻¹ - algebraMap K F (v₀.evalAt (x i₁ * (x ī)⁻¹)))⁻¹) ^ (B v₀).toNat))
      = A.valuation (ι (∏ w ∈ (B.erase v₀).support.filter (fun w => R.placeMap w = Q),
          (X₀ i₁ - Xw w i₁) ^ (B w).toNat)) := by
  have hxī0 : x ī ≠ 0 := by
    intro h0; apply hresī
    have : (⟨x ī, hx ī⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  set U : F := u * ((x ī)⁻¹) ^ k with hU
  set τ : F := x i₁ * (x ī)⁻¹ with hτdef
  have hU0 : U ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ (inv_ne_zero hxī0))

  have hUfib := trivSection_mem R (x ī) u (hx ī) hresī E' Q k (fun z hz => hlow ī z hxī0) hbpf hu0
    (fun z _ => hlowu z)
  have hτmem := chartFun_mem R (x ī) (x i₁) (hx ī) (hx i₁) hresī E' Q (fun z hz => hlow ī z hxī0)
    (fun z hz h0 => hlow i₁ z h0) hbpf
  obtain ⟨D, hD, -⟩ := HasPrincipalDivisors.exists_divisor (K := K) (F := F) U hU0
  have hDB : ∀ w, R.placeMap w = Q → D w = B w := by
    intro w hw; rw [hD w, (hUfib w hw).2, hB w]

  have hQv : (R.placeMap v₀).IsRational := by rw [hv₀Q]; exact hQ
  have hmain := AlgebraicCurve.ConstantReduction.RoadD.valuation_regVal_eq_prod R U τ lam hlamU hunit hτmem.1
    v₀ hv₀ hQv (fun P hP => hratfib P (hP.trans hv₀Q)) (fun P hP => (hUfib P (hP.trans hv₀Q)).1)
    (fun P hP => hτmem.2 P (hP.trans hv₀Q)) (by rw [hv₀Q]; exact hunif hτmem.1) D hD
  rw [hDB v₀ hv₀Q] at hmain
  rw [hmain]

  have hset : ((D.support.filter fun w => R.placeMap w = R.placeMap v₀).erase v₀)
      = (B.erase v₀).support.filter (fun w => R.placeMap w = Q) := by
    ext w
    simp only [Finset.mem_erase, Finset.mem_filter, Finsupp.mem_support_iff, Finsupp.support_erase, hv₀Q]
    constructor
    · rintro ⟨hne, hD0, hwQ⟩
      exact ⟨⟨hne, by rwa [← hDB w hwQ]⟩, hwQ⟩
    · rintro ⟨⟨hne, hB0⟩, hwQ⟩
      exact ⟨hne, by rwa [hDB w hwQ], hwQ⟩
  rw [hset, map_prod ι, map_prod A.valuation]
  apply Finset.prod_congr rfl
  intro w hw
  rw [Finset.mem_filter, Finsupp.support_erase, Finset.mem_erase] at hw
  obtain ⟨⟨hne, hwB⟩, hwQ⟩ := hw
  rw [map_pow, map_pow, hDB w hwQ, map_sub ι, hX₀ i₁, hXw w hwB hwQ i₁]

end P2MJensenD

namespace P2MJensenE

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx"

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem exists_forall_ord_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) :
    ∃ i : Fin r, ∀ j : Fin r, v.ord (s i) ≤ v.ord (s j) := by
  classical
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => v.ord (s i)) Finset.univ_nonempty
  exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩

theorem ord_pivot_le (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (j : Fin r) :
    v.ord (s (pivotIndex s v hr)) ≤ v.ord (s j) := by
  classical
  have hex := exists_forall_ord_le hr s v
  have : pivotIndex s v hr = Classical.choose hex := by rw [pivotIndex, dif_pos hex]
  rw [this]; exact Classical.choose_spec hex j

theorem evalVec_apply (hr : 0 < r) (s : Fin r → F) (v : Place (AlgebraicClosure ℚ) F) (i : Fin r) :
    evalVec s v i = v.evalAt (s i * (s (pivotIndex s v hr))⁻¹) := by
  rw [evalVec]; simp only [dif_pos hr]

theorem evalVec_eq_mul_chart (hr : 0 < r) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) (ī : Fin r)
    (hmin : ∀ j, v.ord (s ī) ≤ v.ord (s j)) (j : Fin r) :
    evalVec s v j = evalVec s v ī * v.evalAt (s j * (s ī)⁻¹) ∧ evalVec s v ī ≠ 0 := by
  set p := pivotIndex s v hr with hp
  have hordeq : v.ord (s ī) = v.ord (s p) := le_antisymm (hmin p) (ord_pivot_le hr s v ī)
  have h1 : s ī * (s p)⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 ī) (inv_ne_zero (hs0 p)))
      (by rw [v.ord_mul (hs0 ī) (inv_ne_zero (hs0 p)), v.ord_inv]; omega)
  have h1ord : v.ord (s ī * (s p)⁻¹) = 0 := by
    rw [v.ord_mul (hs0 ī) (inv_ne_zero (hs0 p)), v.ord_inv]; omega
  have h2 : s j * (s ī)⁻¹ ∈ v.toValuationSubring :=
    v.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 ī)))
      (by rw [v.ord_mul (hs0 j) (inv_ne_zero (hs0 ī)), v.ord_inv]; linarith [hmin j])
  have hne : evalVec s v ī ≠ 0 := by
    rw [evalVec_apply hr s v ī, ← hp]
    exact v.evalAt_ne_zero_of_ord_eq_zero hv (mul_ne_zero (hs0 ī) (inv_ne_zero (hs0 p))) h1ord
  refine ⟨?_, hne⟩
  rw [evalVec_apply hr s v j, evalVec_apply hr s v ī, ← hp]
  have hsplit : s j * (s p)⁻¹ = (s ī * (s p)⁻¹) * (s j * (s ī)⁻¹) := by
    field_simp [hs0 ī, hs0 p]
  rw [hsplit, v.evalAt_mul_of_mem hv h1 h2]

theorem chart_row_of_pivot_row (hr : 0 < r) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0)
    (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) (ī : Fin r)
    (hmin : ∀ j, v.ord (s ī) ≤ v.ord (s j))
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* AlgebraicClosure ℚ) (xc : Fin r → L₀)
    (hxc : ∀ j, ι (xc j) = evalVec s v j) :
    xc ī ≠ 0 ∧ (∀ j, ι (xc j * (xc ī)⁻¹) = v.evalAt (s j * (s ī)⁻¹)) ∧
      xc = (xc ī) • (fun j => xc j * (xc ī)⁻¹) := by
  have hne : xc ī ≠ 0 := by
    intro h0
    have := (evalVec_eq_mul_chart hr s hs0 v hv ī hmin ī).2
    rw [← hxc ī, h0, map_zero] at this
    exact this rfl
  refine ⟨hne, fun j => ?_, ?_⟩
  · rw [map_mul, map_inv₀, hxc j, hxc ī, (evalVec_eq_mul_chart hr s hs0 v hv ī hmin j).1]
    have := (evalVec_eq_mul_chart hr s hs0 v hv ī hmin ī).2
    field_simp
  · funext j; simp only [Pi.smul_apply, smul_eq_mul]; field_simp

theorem log_iSup_pivot_row {L₀ : Type*} [Field L₀] (ν : AbsoluteValue L₀ ℝ) (xc X : Fin r → L₀) (ī : Fin r)
    (a : L₀) (hxc : xc = a • X) (hX : ∀ j, ν (X j) ≤ 1) (hXī : X ī = 1) :
    Real.log (⨆ i, ν (xc i)) = Real.log (ν a) := by
  haveI : Nonempty (Fin r) := ⟨ī⟩
  have hsupX : (⨆ i, ν (X i)) = 1 := by
    apply le_antisymm (ciSup_le hX)
    have := le_ciSup (f := fun i => ν (X i)) (Set.finite_range _).bddAbove ī
    rwa [hXī, map_one] at this
  have : (⨆ i, ν (xc i)) = ν a * ⨆ i, ν (X i) := by
    rw [hxc]; simp only [Pi.smul_apply, smul_eq_mul]; exact iSup_mul_abv ν a X
  rw [this, hsupX, mul_one]

end P2MJensenE

namespace P2MJensenE

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx"

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem evalAt_pow_of_mem' (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f : F}
    (hf : f ∈ v.toValuationSubring) (n : ℕ) : v.evalAt (f ^ n) = (v.evalAt f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, v.evalAt_one]
  | succ n ih => rw [pow_succ, pow_succ, v.evalAt_mul_of_mem hv (pow_mem hf n) hf, ih]

theorem ne_zero_of_ord_ne_zero (v : Place (AlgebraicClosure ℚ) F) {f : F} (h : v.ord f ≠ 0) : f ≠ 0 := by
  intro h0; apply h; rw [h0, Place.ord_zero]

theorem regVal_eq (hr : 0 < r) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0)
    (v₀ : Place (AlgebraicClosure ℚ) F) (hv₀ : v₀.IsRational) (ī : Fin r)
    (hmin : ∀ j, v₀.ord (s ī) ≤ v₀.ord (s j))
    (k e : ℕ) (u d t : F) (hu0 : u ≠ 0) (hd : v₀.ord d = 1)
    (hU : v₀.ord (u * ((s ī)⁻¹) ^ k) = e) (ht : 0 < e → v₀.ord t = 1) :
    regVal s v₀ t k e u
        = v₀.evalAt (u * ((s ī)⁻¹) ^ k * (d⁻¹) ^ e) * (evalVec s v₀ ī) ^ k * (v₀.evalAt (d * t⁻¹)) ^ e
      ∧ v₀.evalAt (u * ((s ī)⁻¹) ^ k * (d⁻¹) ^ e) ≠ 0
      ∧ (0 < e → v₀.evalAt (d * t⁻¹) ≠ 0) := by
  set p := pivotIndex s v₀ hr with hp
  set U : F := u * ((s ī)⁻¹) ^ k with hUdef
  set g : F := s ī * (s p)⁻¹ with hg
  have hd0 : d ≠ 0 := ne_zero_of_ord_ne_zero v₀ (by rw [hd]; exact one_ne_zero)
  have hU0 : U ≠ 0 := mul_ne_zero hu0 (pow_ne_zero _ (inv_ne_zero (hs0 ī)))
  have hordeq : v₀.ord (s ī) = v₀.ord (s p) := le_antisymm (hmin p) (ord_pivot_le hr s v₀ ī)
  have hgord : v₀.ord g = 0 := by rw [hg, v₀.ord_mul (hs0 ī) (inv_ne_zero (hs0 p)), v₀.ord_inv]; omega
  have hg0 : g ≠ 0 := mul_ne_zero (hs0 ī) (inv_ne_zero (hs0 p))
  have hgmem : g ∈ v₀.toValuationSubring := v₀.mem_toValuationSubring_of_ord_nonneg_alt hg0 hgord.ge
  have hgval : v₀.evalAt g = evalVec s v₀ ī := by rw [evalVec_apply hr s v₀ ī, ← hp]

  have hcU : v₀.ord (U * (d⁻¹) ^ e) = 0 := by
    rw [v₀.ord_mul hU0 (pow_ne_zero _ (inv_ne_zero hd0))]
    have : ∀ n : ℕ, v₀.ord ((d⁻¹) ^ n) = -(n : ℤ) := by
      intro n; induction n with
      | zero => simp [Place.ord_one]
      | succ n ih => rw [pow_succ, v₀.ord_mul (pow_ne_zero _ (inv_ne_zero hd0)) (inv_ne_zero hd0), ih, v₀.ord_inv, hd]; push_cast; ring
    rw [this e, hU]; ring
  have hcUmem : U * (d⁻¹) ^ e ∈ v₀.toValuationSubring :=
    v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hU0 (pow_ne_zero _ (inv_ne_zero hd0))) hcU.ge
  have hcUne : v₀.evalAt (U * (d⁻¹) ^ e) ≠ 0 :=
    v₀.evalAt_ne_zero_of_ord_eq_zero hv₀ (mul_ne_zero hU0 (pow_ne_zero _ (inv_ne_zero hd0))) hcU
  have hreg : regVal s v₀ t k e u = v₀.evalAt (u * ((s p)⁻¹) ^ k * (t⁻¹) ^ e) := by
    rw [regVal, dif_pos hr]
  refine ⟨?_, hcUne, ?_⟩
  · rcases Nat.eq_zero_or_pos e with he | he
    ·
      subst he
      simp only [pow_zero, mul_one] at hcUmem hcUne ⊢
      rw [hreg]
      simp only [pow_zero, mul_one]
      have c1 : ((s ī)⁻¹) ^ k * (s ī * (s p)⁻¹) ^ k = ((s p)⁻¹) ^ k := by
        rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ (hs0 ī), one_mul]
      have hid : u * ((s p)⁻¹) ^ k = U * g ^ k := by
        rw [hUdef, hg, mul_assoc, c1]
      rw [hid, v₀.evalAt_mul_of_mem hv₀ hcUmem (pow_mem hgmem k), evalAt_pow_of_mem' v₀ hv₀ hgmem, hgval]
    · have htord := ht he
      have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v₀ (by rw [htord]; exact one_ne_zero)
      have hbord : v₀.ord (d * t⁻¹) = 0 := by rw [v₀.ord_mul hd0 (inv_ne_zero ht0), v₀.ord_inv, hd, htord]; ring
      have hbmem : d * t⁻¹ ∈ v₀.toValuationSubring :=
        v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hd0 (inv_ne_zero ht0)) hbord.ge
      rw [hreg]
      have c1 : ((s ī)⁻¹) ^ k * (s ī * (s p)⁻¹) ^ k = ((s p)⁻¹) ^ k := by
        rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ (hs0 ī), one_mul]
      have c2 : (d⁻¹) ^ e * (d * t⁻¹) ^ e = (t⁻¹) ^ e := by
        rw [← mul_pow, ← mul_assoc, inv_mul_cancel₀ hd0, one_mul]
      have hid : u * ((s p)⁻¹) ^ k * (t⁻¹) ^ e = (U * (d⁻¹) ^ e) * g ^ k * (d * t⁻¹) ^ e := by
        rw [hUdef, hg]
        calc u * ((s p)⁻¹) ^ k * (t⁻¹) ^ e
            = u * (((s ī)⁻¹) ^ k * (s ī * (s p)⁻¹) ^ k) * ((d⁻¹) ^ e * (d * t⁻¹) ^ e) := by rw [c1, c2]
          _ = u * ((s ī)⁻¹) ^ k * (d⁻¹) ^ e * (s ī * (s p)⁻¹) ^ k * (d * t⁻¹) ^ e := by ring
      rw [hid, v₀.evalAt_mul_of_mem hv₀ (mul_mem hcUmem (pow_mem hgmem k)) (pow_mem hbmem e),
        v₀.evalAt_mul_of_mem hv₀ hcUmem (pow_mem hgmem k), evalAt_pow_of_mem' v₀ hv₀ hgmem,
        evalAt_pow_of_mem' v₀ hv₀ hbmem, hgval]
  · intro he
    have htord := ht he
    have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v₀ (by rw [htord]; exact one_ne_zero)
    have hbord : v₀.ord (d * t⁻¹) = 0 := by rw [v₀.ord_mul hd0 (inv_ne_zero ht0), v₀.ord_inv, hd, htord]; ring
    exact v₀.evalAt_ne_zero_of_ord_eq_zero hv₀ (mul_ne_zero hd0 (inv_ne_zero ht0)) hbord

end P2MJensenE

namespace P2MJensenE

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx"

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}

theorem evalAt_sub_of_mem' (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_sub]
  rfl

theorem evalAt_const_mul_of_mem (v : Place (AlgebraicClosure ℚ) F) (hv : v.IsRational) (a : AlgebraicClosure ℚ)
    {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt (algebraMap (AlgebraicClosure ℚ) F a * f) = a * v.evalAt f := by
  rw [v.evalAt_mul_of_mem hv (v.algebraMap_mem' a) hf, v.evalAt_algebraMap_eq]

theorem regVal_chordFun_eq (hr : 0 < r) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0)
    (v₀ : Place (AlgebraicClosure ℚ) F) (hv₀ : v₀.IsRational) (ī i₁ : Fin r)
    (hmin : ∀ j, v₀.ord (s ī) ≤ v₀.ord (s j)) (d t : F)
    (hdτ : d = s i₁ * (s ī)⁻¹ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (s i₁ * (s ī)⁻¹)))
    (hd : v₀.ord d = 1) (ht : v₀.ord t = 1) (q : Fin r × Fin r) :
    let S : Fin r → F := fun j => s j * (s ī)⁻¹
    let qf : Fin r → F := fun j => (S j - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S j))) * d⁻¹
    (∀ j, qf j ∈ v₀.toValuationSubring) ∧ v₀.evalAt (qf ī) = 0 ∧ v₀.evalAt (qf i₁) = 1 ∧
    regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)
      = (evalVec s v₀ ī) ^ 2 * v₀.evalAt (d * t⁻¹)
          * (v₀.evalAt (S q.1) * v₀.evalAt (qf q.2) - v₀.evalAt (S q.2) * v₀.evalAt (qf q.1)) := by
  intro S qf
  set p := pivotIndex s v₀ hr with hp
  set g : F := s ī * (s p)⁻¹ with hg
  set α : AlgebraicClosure ℚ := evalVec s v₀ ī with hα
  have hd0 : d ≠ 0 := ne_zero_of_ord_ne_zero v₀ (by rw [hd]; exact one_ne_zero)
  have ht0 : t ≠ 0 := ne_zero_of_ord_ne_zero v₀ (by rw [ht]; exact one_ne_zero)
  have hordeq : v₀.ord (s ī) = v₀.ord (s p) := le_antisymm (hmin p) (ord_pivot_le hr s v₀ ī)
  have hg0 : g ≠ 0 := mul_ne_zero (hs0 ī) (inv_ne_zero (hs0 p))
  have hgord : v₀.ord g = 0 := by rw [hg, v₀.ord_mul (hs0 ī) (inv_ne_zero (hs0 p)), v₀.ord_inv]; omega
  have hgmem : g ∈ v₀.toValuationSubring := v₀.mem_toValuationSubring_of_ord_nonneg_alt hg0 hgord.ge
  have hgval : v₀.evalAt g = α := by rw [hα, evalVec_apply hr s v₀ ī, ← hp]
  have hSmem : ∀ j, S j ∈ v₀.toValuationSubring := fun j =>
    v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero (hs0 j) (inv_ne_zero (hs0 ī)))
      (by rw [v₀.ord_mul (hs0 j) (inv_ne_zero (hs0 ī)), v₀.ord_inv]; linarith [hmin j])

  have hnval : ∀ j, v₀.evalAt (S j - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S j))) = 0 := by
    intro j
    rw [evalAt_sub_of_mem' v₀ hv₀ (hSmem j) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq, sub_self]
  have hqmem : ∀ j, qf j ∈ v₀.toValuationSubring := by
    intro j
    show (S j - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S j))) * d⁻¹ ∈ v₀.toValuationSubring
    rcases eq_or_ne (S j - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S j))) 0 with h0 | h0
    · rw [h0, zero_mul]; exact zero_mem _
    · apply v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero h0 (inv_ne_zero hd0))
      rw [v₀.ord_mul h0 (inv_ne_zero hd0), v₀.ord_inv, hd]
      have := ord_pos_of_evalAt_eq_zero v₀ hv₀ h0 (sub_mem (hSmem j) (v₀.algebraMap_mem' _)) (hnval j)
      omega
  have hqī : v₀.evalAt (qf ī) = 0 := by
    show v₀.evalAt ((S ī - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S ī))) * d⁻¹) = 0
    have : S ī = 1 := mul_inv_cancel₀ (hs0 ī)
    rw [this, v₀.evalAt_one, map_one, sub_self, zero_mul]
    have h00 : v₀.evalAt (0 : F) = v₀.evalAt (algebraMap (AlgebraicClosure ℚ) F 0) := by rw [map_zero]
    rw [h00, v₀.evalAt_algebraMap_eq]
  have hqi₁ : v₀.evalAt (qf i₁) = 1 := by
    show v₀.evalAt ((S i₁ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S i₁))) * d⁻¹) = 1
    have : S i₁ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S i₁)) = d := by rw [hdτ]
    rw [this, mul_inv_cancel₀ hd0, v₀.evalAt_one]
  refine ⟨hqmem, hqī, hqi₁, ?_⟩

  have hb_mem : d * t⁻¹ ∈ v₀.toValuationSubring :=
    v₀.mem_toValuationSubring_of_ord_nonneg_alt (mul_ne_zero hd0 (inv_ne_zero ht0))
      (by rw [v₀.ord_mul hd0 (inv_ne_zero ht0), v₀.ord_inv, hd, ht]; norm_num)
  set W : F := algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S q.1)) * qf q.2
    - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (S q.2)) * qf q.1 with hW
  have hWmem : W ∈ v₀.toValuationSubring :=
    sub_mem (mul_mem (v₀.algebraMap_mem' _) (hqmem _)) (mul_mem (v₀.algebraMap_mem' _) (hqmem _))
  have hev : ∀ j, evalVec s v₀ j = α * v₀.evalAt (S j) := fun j =>
    (evalVec_eq_mul_chart hr s hs0 v₀ hv₀ ī hmin j).1
  have hid : (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1) * ((s p)⁻¹) ^ 1 * (t⁻¹) ^ 1
      = algebraMap (AlgebraicClosure ℚ) F α * (g * (d * t⁻¹) * W) := by
    rw [hev q.1, hev q.2, Algebra.smul_def, Algebra.smul_def, map_mul, map_mul, hW, hg]
    simp only [pow_one, qf, S]
    set A1 := algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (s q.1 * (s ī)⁻¹)) with hA1
    set A2 := algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (s q.2 * (s ī)⁻¹)) with hA2
    set a := algebraMap (AlgebraicClosure ℚ) F α with ha
    have h1 := hs0 ī
    have h2 := hs0 p
    field_simp
    ring
  rw [regVal, dif_pos hr, ← hp, hid, evalAt_const_mul_of_mem v₀ hv₀ α (mul_mem (mul_mem hgmem hb_mem) hWmem),
    v₀.evalAt_mul_of_mem hv₀ (mul_mem hgmem hb_mem) hWmem, v₀.evalAt_mul_of_mem hv₀ hgmem hb_mem, hgval,
    hW, evalAt_sub_of_mem' v₀ hv₀ (mul_mem (v₀.algebraMap_mem' _) (hqmem _)) (mul_mem (v₀.algebraMap_mem' _) (hqmem _)),
    evalAt_const_mul_of_mem v₀ hv₀ _ (hqmem _), evalAt_const_mul_of_mem v₀ hv₀ _ (hqmem _)]
  ring

end P2MJensenE

namespace P2MJensenF

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenC P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenE"

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem smul_trivSection_mem (R : ConstantReduction A F Fbar) (u xi : F) (lam : AlgebraicClosure ℚ) (k : ℕ)
    (hlamu : lam • u ∈ R.integers) (hres : R.residue ⟨lam • u, hlamu⟩ ≠ 0)
    (hxi : xi ∈ R.integers) (hxres : R.residue ⟨xi, hxi⟩ ≠ 0) :
    ∃ h : lam • (u * (xi⁻¹) ^ k) ∈ R.integers, R.residue ⟨lam • (u * (xi⁻¹) ^ k), h⟩ ≠ 0 := by
  obtain ⟨hinv, hres_inv⟩ := inv_mem_residue_inv R xi hxi hxres
  have hmem : lam • (u * (xi⁻¹) ^ k) ∈ R.integers := by
    rw [← smul_mul_assoc]; exact mul_mem hlamu (pow_mem hinv k)
  refine ⟨hmem, ?_⟩
  have : (⟨lam • (u * (xi⁻¹) ^ k), hmem⟩ : R.integers) = ⟨lam • u, hlamu⟩ * ⟨xi⁻¹, hinv⟩ ^ k :=
    Subtype.ext (by simp)
  rw [this, map_mul, map_pow, hres_inv]
  exact mul_ne_zero hres (pow_ne_zero _ (inv_ne_zero hxres))

theorem ord_discParam_eq_one [HasPrincipalDivisors (AlgebraicClosure ℚ) F] (R : ConstantReduction A F Fbar)
    (τ : F) (hτ : τ ∈ R.integers) (v₀ : Place (AlgebraicClosure ℚ) F) (hv₀ : v₀.IsRational)
    (hQ : (R.placeMap v₀).IsRational)
    (hregτ : ∀ P, R.placeMap P = R.placeMap v₀ → τ ∈ P.toValuationSubring)
    (hunif : (R.placeMap v₀).ord (R.residue ⟨τ, hτ⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩))) = 1) :
    let d : F := τ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt τ)
    v₀.ord d = 1 ∧ d ≠ 0 ∧ (∃ hd : d ∈ R.integers, R.residue ⟨d, hd⟩ ≠ 0) ∧
      (∀ P, R.placeMap P = R.placeMap v₀ → d ∈ P.toValuationSubring) ∧
      (∀ P, R.placeMap P = R.placeMap v₀ → P ≠ v₀ → P.ord d = 0) := by
  intro d
  have ha : v₀.evalAt τ ∈ A := evalAt_mem_of_mem_integers R τ hτ v₀ hv₀ hregτ
  have hconst : algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt τ) ∈ R.integers := (R.algebraMap_mem_iff _).mpr ha
  have hd_mem : d ∈ R.integers := sub_mem hτ hconst
  have hres_d : R.residue ⟨d, hd_mem⟩ = R.residue ⟨τ, hτ⟩
      - algebraMap (ResidueField A) Fbar ((R.placeMap v₀).evalAt (R.residue ⟨τ, hτ⟩)) := by
    have e1 : (⟨d, hd_mem⟩ : R.integers)
        = ⟨τ, hτ⟩ - ⟨algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt τ), hconst⟩ := Subtype.ext rfl
    rw [e1, map_sub]
    congr 1
    have e2 : (⟨algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt τ), hconst⟩ : R.integers)
        = ⟨algebraMap (AlgebraicClosure ℚ) F ((⟨v₀.evalAt τ, ha⟩ : A) : AlgebraicClosure ℚ),
            (R.algebraMap_mem_iff _).mpr (⟨v₀.evalAt τ, ha⟩ : A).2⟩ := Subtype.ext rfl
    rw [e2, R.residue_algebraMap ⟨v₀.evalAt τ, ha⟩, residue_evalAt_eq_evalAt_placeMap R τ hτ v₀ hv₀ hQ hregτ]
  have hres_ne : R.residue ⟨d, hd_mem⟩ ≠ 0 := by
    intro h0; rw [hres_d] at h0; rw [h0, Place.ord_zero] at hunif; exact zero_ne_one hunif
  have hd0 : d ≠ 0 := by
    intro h0; apply hres_ne
    have : (⟨d, hd_mem⟩ : R.integers) = 0 := Subtype.ext h0
    rw [this, map_zero]
  have hreg_d : ∀ P, R.placeMap P = R.placeMap v₀ → d ∈ P.toValuationSubring := fun P hP =>
    sub_mem (hregτ P hP) (P.algebraMap_mem' _)
  have hval : v₀.evalAt d = 0 := by
    rw [evalAt_sub_of_mem' v₀ hv₀ (hregτ v₀ rfl) (v₀.algebraMap_mem' _), v₀.evalAt_algebraMap_eq, sub_self]
  have h1 : 0 < v₀.ord d := ord_pos_of_evalAt_eq_zero v₀ hv₀ hd0 (hreg_d v₀ rfl) hval
  have h2 := ord_le_ord_residue R d hd_mem hres_ne v₀ hreg_d
  rw [hres_d, hunif] at h2
  refine ⟨by omega, hd0, ⟨hd_mem, hres_ne⟩, hreg_d, fun P hP hne => ?_⟩
  exact ord_sub_const_eq_zero_of_ne R τ hτ v₀ hv₀ hQ hregτ hunif hP hne

end P2MJensenF

namespace P2MJensenF

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenProx P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenC P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenE"

variable {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F]
variable {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem prox_pivot_eq_prox_chart {L₀ : Type*} [Field L₀] (ν : AbsoluteValue L₀ ℝ) {r : ℕ}
    (x₀ X₀ xw Xw : Fin r → L₀) (a b : L₀) (ha : a ≠ 0) (hb : b ≠ 0) (hx₀ : x₀ = a • X₀) (hxw : xw = b • Xw)
    (hminor : ∃ p : Fin r × Fin r, X₀ p.1 * Xw p.2 - X₀ p.2 * Xw p.1 ≠ 0) :
    prox ν x₀ xw = prox ν X₀ Xw := by
  obtain ⟨p, hp⟩ := hminor
  have hminor' : ∃ p : Fin r × Fin r, X₀ p.1 * (b • Xw) p.2 - X₀ p.2 * (b • Xw) p.1 ≠ 0 := by
    refine ⟨p, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul]
    intro h0; apply hp
    have : b * (X₀ p.1 * Xw p.2 - X₀ p.2 * Xw p.1) = 0 := by linear_combination h0
    exact (mul_eq_zero.mp this).resolve_left hb
  rw [hx₀, hxw, prox_smul_left ν a ha X₀ (b • Xw) hminor', prox_smul_right ν b hb X₀ Xw ⟨p, hp⟩]

open Classical in

theorem per_base_place [HasPrincipalDivisors (AlgebraicClosure ℚ) F] (R : ConstantReduction A F Fbar)
    {L₀ : Type*} [Field L₀] (ι : L₀ →+* AlgebraicClosure ℚ) (ν : AbsoluteValue L₀ ℝ) (hna : IsNonarchimedean ⇑ν)
    (hA : ∀ a : L₀, ν a ≤ 1 ↔ ι a ∈ A)
    {r : ℕ} (hr : 0 < r) (s : Fin r → F) (hs0 : ∀ i, s i ≠ 0) (hx : ∀ i, s i ∈ R.integers)
    (E' : Divisor (AlgebraicClosure ℚ) F) (hlow : ∀ j z, s j ≠ 0 → -E' z ≤ z.ord (s j))
    (cQ iQ : Place (ResidueField A) Fbar → Fin r)
    (hrat : ∀ P : Place (AlgebraicClosure ℚ) F, P.IsRational ∧ (R.placeMap P).IsRational)
    (hchart : ∀ P : Place (AlgebraicClosure ℚ) F, R.residue ⟨s (cQ (R.placeMap P)), hx _⟩ ≠ 0 ∧
      (R.placeMap P).ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
        = -(Finsupp.mapDomain R.placeMap E' (R.placeMap P)))
    (htan : ∀ P : Place (AlgebraicClosure ℚ) F,
      ∀ hmem : s (iQ (R.placeMap P)) * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
      (R.placeMap P).ord (R.residue ⟨_, hmem⟩
        - algebraMap (ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨_, hmem⟩))) = 1)
    (hsep : ∀ P P' : Place (AlgebraicClosure ℚ) F, R.placeMap P' ≠ R.placeMap P →
      (R.placeMap P').ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
        = -(Finsupp.mapDomain R.placeMap E' (R.placeMap P')) →
      ∀ hmem : ∀ j, s j * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
      ∃ j, (R.placeMap P).evalAt (R.residue ⟨_, hmem j⟩) ≠ (R.placeMap P').evalAt (R.residue ⟨_, hmem j⟩))
    (k : ℕ) (u : F) (hu0 : u ≠ 0) (hlowu : ∀ z, -((k : ℤ) * E' z) ≤ z.ord u)
    (B : Divisor (AlgebraicClosure ℚ) F) (hB : ∀ w, B w = w.ord u + (k : ℤ) * E' w)
    (lam : AlgebraicClosure ℚ) (hlamu : lam • u ∈ R.integers) (hlamres : R.residue ⟨lam • u, hlamu⟩ ≠ 0)
    (v₀ : Place (AlgebraicClosure ℚ) F) (t : F) (ht : 0 < B v₀ → v₀.ord t = 1)
    (xc : Place (AlgebraicClosure ℚ) F → Fin r → L₀)
    (hxcB : ∀ w ∈ B.support, ∀ i, ι (xc w i) = evalVec s w i) (hxc₀ : ∀ i, ι (xc v₀ i) = evalVec s v₀ i)
    (c : L₀) (hc : ι c = regVal s v₀ t k (B v₀).toNat u)
    (y : Fin r × Fin r → L₀)
    (hy : 0 < B v₀ → ∀ q, ι (y q) = regVal s v₀ t 1 1 (evalVec s v₀ q.1 • s q.2 - evalVec s v₀ q.2 • s q.1)) :
    ∃ ρ : L₀, ρ ≠ 0 ∧ A.valuation (ι ρ) = A.valuation lam ∧
      ((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (xc v₀) (xc w))
        = ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (xc v₀ i))
          + (B v₀ : ℝ) * Real.log (⨆ q, ν (y q)) - Real.log (ν c) - Real.log (ν ρ) := by

  set Q := R.placeMap v₀ with hQdef
  have hv₀ : v₀.IsRational := (hrat v₀).1
  have hQ : Q.IsRational := (hrat v₀).2
  set ī := cQ Q with hīdef
  set i₁ := iQ Q with hi₁def
  have hresī : R.residue ⟨s ī, hx ī⟩ ≠ 0 := (hchart v₀).1
  have hbpf : Q.ord (R.residue ⟨s ī, hx ī⟩) = -(Finsupp.mapDomain R.placeMap E' Q) := (hchart v₀).2
  have hunif := htan v₀
  have hBnn : ∀ w, 0 ≤ B w := fun w => by rw [hB w]; linarith [hlowu w]
  set e : ℕ := (B v₀).toNat with hedef
  have heB : (B v₀ : ℤ) = e := (Int.toNat_of_nonneg (hBnn v₀)).symm
  have heR : (B v₀ : ℝ) = (e : ℝ) := by exact_mod_cast heB

  have hmin_of : ∀ (P z : Place (AlgebraicClosure ℚ) F), R.placeMap z = R.placeMap P →
      ∀ j, z.ord (s (cQ (R.placeMap P))) ≤ z.ord (s j) := by
    intro P z hz j
    have hc0 : s (cQ (R.placeMap P)) ≠ 0 := hs0 _
    rw [ord_eq_neg_of_chart R (s (cQ (R.placeMap P))) (hx _) (hchart P).1 E' (R.placeMap P)
      (fun z' hz' => hlow _ z' hc0) (hchart P).2 z hz]
    exact hlow j z (hs0 j)
  have hmin₀ : ∀ j, v₀.ord (s ī) ≤ v₀.ord (s j) := hmin_of v₀ v₀ rfl

  obtain ⟨hα0, hX₀, hxsmul₀⟩ := chart_row_of_pivot_row hr s hs0 v₀ hv₀ ī hmin₀ ι (xc v₀) hxc₀
  set X₀ : Fin r → L₀ := fun j => xc v₀ j * (xc v₀ ī)⁻¹ with hX₀def
  set cw : Place (AlgebraicClosure ℚ) F → Fin r := fun w => cQ (R.placeMap w) with hcwdef
  set Xw : Place (AlgebraicClosure ℚ) F → Fin r → L₀ := fun w j => xc w j * (xc w (cw w))⁻¹ with hXwdef
  have hroww : ∀ w ∈ B.support, xc w (cw w) ≠ 0 ∧ (∀ j, ι (Xw w j) = w.evalAt (s j * (s (cw w))⁻¹)) ∧
      xc w = (xc w (cw w)) • Xw w := fun w hw =>
    chart_row_of_pivot_row hr s hs0 w (hrat w).1 (cw w) (hmin_of w w rfl) ι (xc w) (hxcB w hw)
  have hXw : ∀ w ∈ B.support, ∀ j, ι (Xw w j) = w.evalAt (s j * (s (cw w))⁻¹) := fun w hw => (hroww w hw).2.1
  have hcwQ : ∀ w ∈ B.support, R.placeMap w = Q → cw w = ī := fun w _ hwQ => by
    show cQ (R.placeMap w) = cQ Q; rw [hwQ]

  obtain ⟨hsum, hfibne, hminors⟩ := sum_prox_eq R ι ν hna hA s hx E' hlow Q hQ ī i₁ hresī hbpf hunif B hBnn cw
    hcwQ (fun w _ => (hchart w).1) (fun w _ => (hchart w).2) (fun w _ hne hch => hsep v₀ w hne hch)
    (fun w _ => hrat w) hv₀ rfl X₀ hX₀ Xw hXw

  obtain ⟨hlamU, hunit⟩ := smul_trivSection_mem R u (s ī) lam k hlamu hlamres (hx ī) hresī
  have hval := valuation_regVal_eq R ι s hx E' hlow Q hQ ī i₁ hresī hbpf hunif k u hu0 hlowu B hB lam hlamU hunit
    (fun P _ => (hrat P).1) hv₀ rfl X₀ hX₀ Xw (fun w hw hwQ j => by rw [hXw w hw j, hcwQ w hw hwQ])

  set τ : F := s i₁ * (s ī)⁻¹ with hτdef
  have hτmem := chartFun_mem R (s ī) (s i₁) (hx ī) (hx i₁) hresī E' Q (fun z hz => hlow ī z (hs0 ī))
    (fun z hz h0 => hlow i₁ z h0) hbpf
  set d : F := τ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt τ) with hddef
  obtain ⟨hd1, hd0, ⟨hdint, hdres⟩, hdreg, hdP⟩ := ord_discParam_eq_one R τ hτmem.1 v₀ hv₀ hQ
    (fun P hP => hτmem.2 P hP) (hunif hτmem.1)
  have hUfib := trivSection_mem R (s ī) u (hx ī) hresī E' Q k (fun z hz => hlow ī z (hs0 ī)) hbpf hu0
    (fun z _ => hlowu z)
  have hUord : v₀.ord (u * ((s ī)⁻¹) ^ k) = e := by rw [(hUfib v₀ rfl).2, ← hB v₀, heB]
  have ht' : 0 < e → v₀.ord t = 1 := fun he => ht (by omega)
  obtain ⟨hregVal, hcτ0, hβ0⟩ := regVal_eq hr s hs0 v₀ hv₀ ī hmin₀ k e u d t hu0 hd1 hUord ht'
  set cτK : AlgebraicClosure ℚ := v₀.evalAt (u * ((s ī)⁻¹) ^ k * (d⁻¹) ^ e) with hcτKdef
  set βK : AlgebraicClosure ℚ := v₀.evalAt (d * t⁻¹) with hβKdef
  have hαι : evalVec s v₀ ī = ι (xc v₀ ī) := (hxc₀ ī).symm

  set Tfib := (B.erase v₀).support.filter (fun w => R.placeMap w = Q) with hTfib
  set zfib : L₀ := ∏ w ∈ Tfib, (X₀ i₁ - Xw w i₁) ^ (B w).toNat with hzfib
  have hzfib0 : zfib ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro w hw
    rw [Finset.mem_filter] at hw
    exact pow_ne_zero _ (sub_ne_zero.mpr (hfibne w hw.1 hw.2))
  have hval' : A.valuation (lam * cτK) = A.valuation (ι zfib) := hval

  have hLHS : ((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (xc v₀) (xc w))
      = ∑ w ∈ (B.erase v₀).support, ((B.erase v₀) w : ℝ) * prox ν X₀ (Xw w) := by
    rw [Finsupp.sum]
    apply Finset.sum_congr rfl
    intro w hw
    have hwB : w ∈ B.support := by
      rw [Finsupp.support_erase, Finset.mem_erase] at hw; exact hw.2
    congr 1
    exact prox_pivot_eq_prox_chart ν (xc v₀) X₀ (xc w) (Xw w) (xc v₀ ī) (xc w (cw w)) hα0 (hroww w hwB).1
      hxsmul₀ (hroww w hwB).2.2 (hminors w hw)

  have hX₀int : ∀ j, ν (X₀ j) ≤ 1 := by
    intro j
    apply (hA _).mpr
    rw [hX₀ j]
    have hS := chartFun_mem R (s ī) (s j) (hx ī) (hx j) hresī E' Q (fun z hz => hlow ī z (hs0 ī))
      (fun z hz h0 => hlow j z h0) hbpf
    exact evalAt_mem_of_mem_integers R _ hS.1 v₀ hv₀ (fun P hP => hS.2 P hP)
  have hX₀ī : X₀ ī = 1 := by show xc v₀ ī * (xc v₀ ī)⁻¹ = 1; exact mul_inv_cancel₀ hα0
  have hσ : Real.log (⨆ i, ν (xc v₀ i)) = Real.log (ν (xc v₀ ī)) :=
    log_iSup_pivot_row ν (xc v₀) X₀ ī (xc v₀ ī) hxsmul₀ hX₀int hX₀ī

  rcases Nat.eq_zero_or_pos e with he0 | hepos
  ·
    have hB0 : (B v₀ : ℝ) = 0 := by rw [heR, he0]; simp
    have hcK : ι c = cτK * (ι (xc v₀ ī)) ^ k := by
      rw [hc, hregVal, hαι, he0, pow_zero, mul_one]
    set cτL : L₀ := c * ((xc v₀ ī) ^ k)⁻¹ with hcτL
    have hιcτL : ι cτL = cτK := by
      rw [hcτL, map_mul, map_inv₀, map_pow, hcK]
      have h1 : (ι (xc v₀ ī)) ^ k ≠ 0 := pow_ne_zero k ((map_ne_zero ι).mpr hα0)
      calc cτK * (ι (xc v₀ ī)) ^ k * ((ι (xc v₀ ī)) ^ k)⁻¹ = cτK * ((ι (xc v₀ ī)) ^ k * ((ι (xc v₀ ī)) ^ k)⁻¹) := by ring
        _ = cτK := by rw [mul_inv_cancel₀ h1, mul_one]
    have hcτL0 : cτL ≠ 0 := fun h0 => hcτ0 (by rw [← hιcτL, h0, map_zero])
    have hc0 : c ≠ 0 := fun h0 => hcτL0 (by rw [hcτL, h0, zero_mul])
    refine ⟨zfib * cτL⁻¹, mul_ne_zero hzfib0 (inv_ne_zero hcτL0), ?_, ?_⟩
    · rw [map_mul, map_inv₀, map_mul, map_inv₀, ← hval', hιcτL, map_mul]
      have : A.valuation cτK ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hcτ0
      rw [mul_assoc, mul_inv_cancel₀ this, mul_one]
    · rw [hLHS, hsum, hσ, hB0]
      have hlogc : Real.log (ν c) = Real.log (ν cτL) + (k : ℝ) * Real.log (ν (xc v₀ ī)) := by
        have : c = cτL * (xc v₀ ī) ^ k := by
          rw [hcτL, mul_assoc, inv_mul_cancel₀ (pow_ne_zero k hα0), mul_one]
        rw [this, map_mul, map_pow, Real.log_mul ((AbsoluteValue.ne_zero_iff ν).mpr hcτL0)
          (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hα0)), Real.log_pow]
      have hlogρ : Real.log (ν (zfib * cτL⁻¹)) = Real.log (ν zfib) - Real.log (ν cτL) := by
        rw [map_mul, map_inv₀, Real.log_mul ((AbsoluteValue.ne_zero_iff ν).mpr hzfib0)
          (inv_ne_zero ((AbsoluteValue.ne_zero_iff ν).mpr hcτL0)), Real.log_inv]; ring
      rw [hlogc, hlogρ]; ring
  ·
    have hBpos : 0 < B v₀ := by omega
    have htord : v₀.ord t = 1 := ht hBpos

    have hE2b := fun q => regVal_chordFun_eq hr s hs0 v₀ hv₀ ī i₁ hmin₀ d t rfl hd1 htord q

    obtain ⟨hdinv, -⟩ := inv_mem_residue_inv R d hdint hdres
    have hSfacts : ∀ j, (s j * (s ī)⁻¹ ∈ R.integers ∧ ∀ z, R.placeMap z = Q → s j * (s ī)⁻¹ ∈ z.toValuationSubring) :=
      fun j => chartFun_mem R (s ī) (s j) (hx ī) (hx j) hresī E' Q (fun z hz => hlow ī z (hs0 ī))
        (fun z hz h0 => hlow j z h0) hbpf
    have hSval : ∀ j, v₀.evalAt (s j * (s ī)⁻¹) ∈ A := fun j =>
      evalAt_mem_of_mem_integers R _ (hSfacts j).1 v₀ hv₀ (fun P hP => (hSfacts j).2 P hP)
    set qf : Fin r → F := fun j => (s j * (s ī)⁻¹ - algebraMap (AlgebraicClosure ℚ) F (v₀.evalAt (s j * (s ī)⁻¹))) * d⁻¹
      with hqfdef
    have hqint : ∀ j, qf j ∈ R.integers := fun j =>
      mul_mem (sub_mem (hSfacts j).1 ((R.algebraMap_mem_iff _).mpr (hSval j))) hdinv
    have hqreg : ∀ j P, R.placeMap P = R.placeMap v₀ → qf j ∈ P.toValuationSubring := by
      intro j P hP
      by_cases hPv : P = v₀
      · subst hPv; exact (hE2b (ī, ī)).1 j
      · exact mul_mem (sub_mem ((hSfacts j).2 P hP) (P.algebraMap_mem' _))
          (P.mem_toValuationSubring_of_ord_nonneg_alt (inv_ne_zero hd0) (by rw [P.ord_inv, hdP P hP hPv, neg_zero]))
    have hqval : ∀ j, v₀.evalAt (qf j) ∈ A := fun j =>
      evalAt_mem_of_mem_integers R _ (hqint j) v₀ hv₀ (hqreg j)

    have hyq : ∀ q : Fin r × Fin r, ι (y q) = (ι (xc v₀ ī)) ^ 2 * βK
        * (ι (X₀ q.1) * v₀.evalAt (qf q.2) - ι (X₀ q.2) * v₀.evalAt (qf q.1)) := by
      intro q
      rw [hy hBpos q, (hE2b q).2.2.2, hαι, hX₀ q.1, hX₀ q.2]
    have hq1 : v₀.evalAt (qf i₁) = 1 := (hE2b (ī, ī)).2.2.1
    have hq0 : v₀.evalAt (qf ī) = 0 := (hE2b (ī, ī)).2.1
    set βL : L₀ := y (ī, i₁) * ((xc v₀ ī) ^ 2)⁻¹ with hβLdef
    have hαpow : (ι (xc v₀ ī)) ^ 2 ≠ 0 := pow_ne_zero 2 ((map_ne_zero ι).mpr hα0)
    have hιβL : ι βL = βK := by
      rw [hβLdef, map_mul, map_inv₀, map_pow, hyq (ī, i₁)]
      dsimp only
      rw [hq1, hq0, hX₀ī, map_one, mul_zero, sub_zero, one_mul, mul_one]
      calc (ι (xc v₀ ī)) ^ 2 * βK * ((ι (xc v₀ ī)) ^ 2)⁻¹ = βK * ((ι (xc v₀ ī)) ^ 2 * ((ι (xc v₀ ī)) ^ 2)⁻¹) := by ring
        _ = βK := by rw [mul_inv_cancel₀ hαpow, mul_one]
    have hβL0 : βL ≠ 0 := fun h0 => (hβ0 hepos) (by rw [← hιβL, h0, map_zero])
    set YL : Fin r × Fin r → L₀ := fun q => y q * ((xc v₀ ī) ^ 2 * βL)⁻¹ with hYLdef
    have hιYL : ∀ q, ι (YL q) = ι (X₀ q.1) * v₀.evalAt (qf q.2) - ι (X₀ q.2) * v₀.evalAt (qf q.1) := by
      intro q
      rw [hYLdef]; dsimp only
      rw [map_mul, map_inv₀, map_mul, map_pow, hιβL, hyq q]
      have h2 : βK ≠ 0 := hβ0 hepos
      set W := ι (X₀ q.1) * v₀.evalAt (qf q.2) - ι (X₀ q.2) * v₀.evalAt (qf q.1) with hWdef
      calc (ι (xc v₀ ī)) ^ 2 * βK * W * ((ι (xc v₀ ī)) ^ 2 * βK)⁻¹
          = W * (((ι (xc v₀ ī)) ^ 2 * βK) * ((ι (xc v₀ ī)) ^ 2 * βK)⁻¹) := by ring
        _ = W := by rw [mul_inv_cancel₀ (mul_ne_zero hαpow h2), mul_one]
    have hYLint : ∀ q, ν (YL q) ≤ 1 := by
      intro q; apply (hA _).mpr; rw [hιYL q]
      exact sub_mem (mul_mem (by rw [hX₀]; exact hSval _) (hqval _)) (mul_mem (by rw [hX₀]; exact hSval _) (hqval _))
    have hYL1 : YL (ī, i₁) = 1 := by
      apply ι.injective
      rw [hιYL, map_one]; dsimp only
      rw [hq1, hq0, hX₀ī, map_one, mul_zero, sub_zero, one_mul]
    have hysmul : y = ((xc v₀ ī) ^ 2 * βL) • YL := by
      funext q; simp only [hYLdef, Pi.smul_apply, smul_eq_mul]
      have hne : (xc v₀ ī) ^ 2 * βL ≠ 0 := mul_ne_zero (pow_ne_zero 2 hα0) hβL0
      calc y q = y q * (((xc v₀ ī) ^ 2 * βL) * ((xc v₀ ī) ^ 2 * βL)⁻¹) := by rw [mul_inv_cancel₀ hne, mul_one]
        _ = (xc v₀ ī) ^ 2 * βL * (y q * ((xc v₀ ī) ^ 2 * βL)⁻¹) := by ring
    have hlogy : Real.log (⨆ q, ν (y q)) = 2 * Real.log (ν (xc v₀ ī)) + Real.log (ν βL) := by
      haveI : Nonempty (Fin r × Fin r) := ⟨(ī, i₁)⟩
      have hsupY : (⨆ q, ν (YL q)) = 1 := by
        apply le_antisymm (ciSup_le hYLint)
        have := le_ciSup (f := fun q => ν (YL q)) (Set.finite_range _).bddAbove (ī, i₁)
        rwa [hYL1, map_one] at this
      have : (⨆ q, ν (y q)) = ν ((xc v₀ ī) ^ 2 * βL) * ⨆ q, ν (YL q) := by
        rw [hysmul]; simp only [Pi.smul_apply, smul_eq_mul]; exact iSup_mul_abv' ν _ YL
      rw [this, hsupY, mul_one, map_mul, map_pow, Real.log_mul (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hα0))
        ((AbsoluteValue.ne_zero_iff ν).mpr hβL0), Real.log_pow]
      push_cast; ring

    have hcK : ι c = cτK * (ι (xc v₀ ī)) ^ k * βK ^ e := by
      rw [hc, hregVal, hαι]
    set cτL : L₀ := c * ((xc v₀ ī) ^ k * βL ^ e)⁻¹ with hcτL
    have hιcτL : ι cτL = cτK := by
      rw [hcτL, map_mul, map_inv₀, map_mul, map_pow, map_pow, hιβL, hcK]
      have h1 : (ι (xc v₀ ī)) ^ k ≠ 0 := pow_ne_zero k ((map_ne_zero ι).mpr hα0)
      have h2 : βK ^ e ≠ 0 := pow_ne_zero e (hβ0 hepos)
      calc cτK * (ι (xc v₀ ī)) ^ k * βK ^ e * ((ι (xc v₀ ī)) ^ k * βK ^ e)⁻¹
          = cτK * (((ι (xc v₀ ī)) ^ k * βK ^ e) * ((ι (xc v₀ ī)) ^ k * βK ^ e)⁻¹) := by ring
        _ = cτK := by rw [mul_inv_cancel₀ (mul_ne_zero h1 h2), mul_one]
    have hcτL0 : cτL ≠ 0 := fun h0 => hcτ0 (by rw [← hιcτL, h0, map_zero])
    refine ⟨zfib * cτL⁻¹, mul_ne_zero hzfib0 (inv_ne_zero hcτL0), ?_, ?_⟩
    · rw [map_mul, map_inv₀, map_mul, map_inv₀, ← hval', hιcτL, map_mul]
      have : A.valuation cτK ≠ 0 := by rw [ne_eq, map_eq_zero]; exact hcτ0
      rw [mul_assoc, mul_inv_cancel₀ this, mul_one]
    · rw [hLHS, hsum, hσ, hlogy, heR]
      have hlogc : Real.log (ν c) = Real.log (ν cτL) + (k : ℝ) * Real.log (ν (xc v₀ ī)) + (e : ℝ) * Real.log (ν βL) := by
        have : c = cτL * ((xc v₀ ī) ^ k * βL ^ e) := by
          rw [hcτL, mul_assoc, inv_mul_cancel₀ (mul_ne_zero (pow_ne_zero k hα0) (pow_ne_zero e hβL0)), mul_one]
        have eq1 : ν (cτL * ((xc v₀ ī) ^ k * βL ^ e)) = ν cτL * ((ν (xc v₀ ī)) ^ k * (ν βL) ^ e) := by
          rw [map_mul ν cτL, map_mul ν ((xc v₀ ī) ^ k), map_pow, map_pow]
        rw [this, eq1,
          Real.log_mul ((AbsoluteValue.ne_zero_iff ν).mpr hcτL0)
            (mul_ne_zero (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hα0)) (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hβL0))),
          Real.log_mul (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hα0)) (pow_ne_zero _ ((AbsoluteValue.ne_zero_iff ν).mpr hβL0)),
          Real.log_pow, Real.log_pow]
        ring
      have hlogρ : Real.log (ν (zfib * cτL⁻¹)) = Real.log (ν zfib) - Real.log (ν cτL) := by
        rw [map_mul, map_inv₀, Real.log_mul ((AbsoluteValue.ne_zero_iff ν).mpr hzfib0)
          (inv_ne_zero ((AbsoluteValue.ne_zero_iff ν).mpr hcτL0)), Real.log_inv]; ring
      rw [hlogc, hlogρ]; ring

end P2MJensenF

namespace P2MJensenAssembly

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve ModularCurve IsLocalRing P2MW.S_ModularCurve_JZero_jensen_good_at.P2MRoadD P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenAh P2MW.S_ModularCurve_JZero_jensen_good_at.P2MJensenF"

theorem stub_HPD (N : ℕ) [NeZero N] : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
  ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar ModularCurve.modularPolynomialFamily N

theorem stub_bridge (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L] (ν : NumberField.FinitePlace ↥L) :
    ∃ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime ∧ A.LiesOverPrime ℓ ∧
      ν (ℓ : ↥L) < 1 ∧ ∀ a : ↥L, ν a ≤ 1 ↔ (a : AlgebraicClosure ℚ) ∈ A := by
  obtain ⟨M⟩ := ModularCurve.nonempty_finitePlaceLift L ν
  exact ⟨M.A, M.p, M.pprime, M.lies, M.nu_p_lt_one, fun a => (M.mem_iff a).symm⟩

theorem stub_model (N : ℕ) [NeZero N] {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ), ℓ.Prime → ℓ ∉ S →
      A.LiesOverPrime ℓ →
      ∃ (Fbar : Type) (_ : Field Fbar) (_ : Algebra (ResidueField A) Fbar)
        (R : ConstantReduction A (modularFunctionFieldBar N) Fbar) (hx : ∀ i, s i ∈ R.integers)
        (cQ iQ : Place (ResidueField A) Fbar → Fin r),
        R.IsGood ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), P.IsRational ∧ (R.placeMap P).IsRational) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          R.residue ⟨s (cQ (R.placeMap P)), hx _⟩ ≠ 0 ∧
          (R.placeMap P).ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P))) ∧
        (∀ P : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
          ∀ hmem : s (iQ (R.placeMap P)) * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          (R.placeMap P).ord (R.residue ⟨_, hmem⟩
            - algebraMap (ResidueField A) Fbar ((R.placeMap P).evalAt (R.residue ⟨_, hmem⟩))) = 1) ∧
        (∀ P P' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), R.placeMap P' ≠ R.placeMap P →
          (R.placeMap P').ord (R.residue ⟨s (cQ (R.placeMap P)), hx _⟩)
            = -(Finsupp.mapDomain R.placeMap (embDivisor N) (R.placeMap P')) →
          ∀ hmem : ∀ j, s j * (s (cQ (R.placeMap P)))⁻¹ ∈ R.integers,
          ∃ j, (R.placeMap P).evalAt (R.residue ⟨_, hmem j⟩) ≠ (R.placeMap P').evalAt (R.residue ⟨_, hmem j⟩)) :=
  ModularCurve.exists_constantReduction_chartData_of_isEmbBasis N s hs

theorem embDivisor_nonneg (N : ℕ) [NeZero N] (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    0 ≤ embDivisor N v := by
  classical
  rw [embDivisor, Finsupp.smul_apply, Finsupp.single_apply]
  split_ifs <;> simp

open Classical in
theorem assembly (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        ((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
          = ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m := by
  obtain ⟨S, hSp, hmodel⟩ := stub_model N s hs
  refine ⟨S, hSp, ?_⟩
  intro k u hu0 huE B hB L _ ν hνS x hxB
  haveI := stub_HPD N
  obtain ⟨A, ℓ, hℓp, hAℓ, hνℓ, hA⟩ := stub_bridge L ν
  have hℓS : ℓ ∉ S := fun h => by have := hνS ℓ h; rw [this] at hνℓ; exact lt_irrefl _ hνℓ
  obtain ⟨Fbar, instF, instA, R, hxint, cQ, iQ, -, hrat, hchart, htan, hsep⟩ := hmodel A ℓ hℓp hℓS hAℓ
  obtain ⟨lam, hlamu, hlamres⟩ := R.exists_smul_mem u hu0

  have hs0 : ∀ i, s i ≠ 0 := fun i => hs.1.ne_zero i
  have hsE : ∀ i, s i ∈ riemannRochSpace (embDivisor N) := fun i => by
    rw [← hs.2]; exact Submodule.subset_span ⟨i, rfl⟩
  have hlow : ∀ j z, s j ≠ 0 → -embDivisor N z ≤ z.ord (s j) := fun j z h0 =>
    ((mem_riemannRochSpace_iff.mp (hsE j)) z).resolve_left h0
  have hlowu : ∀ z, -((k : ℤ) * embDivisor N z) ≤ z.ord u := fun z => by
    have := ((mem_riemannRochSpace_iff.mp huE) z).resolve_left hu0
    rwa [Finsupp.smul_apply, smul_eq_mul] at this
  have hB' : ∀ w, B w = w.ord u + (k : ℤ) * embDivisor N w := fun w => by
    rw [hB w, Finsupp.smul_apply, smul_eq_mul]
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · exfalso
      subst h0
      have h1 : (1 : modularFunctionFieldBar N) ∈ riemannRochSpace (embDivisor N) := by
        rw [mem_riemannRochSpace_iff]; intro v; right; rw [Place.ord_one]; linarith [embDivisor_nonneg N v]
      rw [← hs.2] at h1
      have : Set.range s = ∅ := Set.range_eq_empty s
      rw [this, Submodule.span_empty, Submodule.mem_bot] at h1
      exact one_ne_zero h1
    · exact h0

  set ι : ↥L →+* AlgebraicClosure ℚ := algebraMap ↥L (AlgebraicClosure ℚ) with hιdef
  have hι : ∀ a : ↥L, ι a = (a : AlgebraicClosure ℚ) := fun a => rfl
  have hna : IsNonarchimedean ⇑(ν.1) := fun a b => NumberField.FinitePlace.add_le ν a b
  have hA' : ∀ a : ↥L, ν.1 a ≤ 1 ↔ ι a ∈ A := fun a => hA a

  let m : ℝ := if h : ∃ z : ↥L, z ≠ 0 ∧ A.valuation (ι z) = A.valuation lam
    then Real.log (ν (Classical.choose h)) else 0
  refine ⟨m, ?_⟩
  intro v₀ t ht hxv₀ c hc y hy
  obtain ⟨ρ, hρ0, hρval, hid⟩ := per_base_place R ι ν.1 hna hA' hr s hs0 hxint (embDivisor N) hlow cQ iQ hrat
    hchart htan hsep k u hu0 hlowu B hB' lam hlamu hlamres v₀ t ht x (fun w hw i => hxB w hw i) hxv₀ c hc y hy
  have hex : ∃ z : ↥L, z ≠ 0 ∧ A.valuation (ι z) = A.valuation lam := ⟨ρ, hρ0, hρval⟩
  have hm : m = Real.log (ν ρ) := by
    show (if h : ∃ z : ↥L, z ≠ 0 ∧ A.valuation (ι z) = A.valuation lam
      then Real.log (ν (Classical.choose h)) else 0) = Real.log (ν ρ)
    rw [dif_pos hex]
    congr 1
    exact eq_of_valuation_eq ι ν.1 A hA' (Classical.choose_spec hex).1 hρ0
      ((Classical.choose_spec hex).2.trans hρval.symm)
  rw [hm]
  exact hid

end P2MJensenAssembly

end

open _root_.AlgebraicCurve _root_.P2MW.S_ModularCurve_JZero_jensen_good_at.AlgebraicCurve ModularCurve in

theorem solution (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧ ∀ (k : ℕ) (u : modularFunctionFieldBar N), u ≠ 0 →
      u ∈ riemannRochSpace ((k : ℤ) • embDivisor N) →
      ∀ B : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (∀ w, B w = w.ord u + ((k : ℤ) • embDivisor N) w) →
      ∀ (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥L]
        (ν : NumberField.FinitePlace ↥L), (∀ p ∈ S, ν (p : ↥L) = 1) →
      ∀ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) → Fin r → ↥L,
      (∀ w ∈ B.support, ∀ i, ((x w i : ↥L) : AlgebraicClosure ℚ) = evalVec s w i) →
      ∃ m : ℝ, ∀ (v₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
        (t : modularFunctionFieldBar N), (0 < B v₀ → v₀.ord t = 1) →
        (∀ i, ((x v₀ i : ↥L) : AlgebraicClosure ℚ) = evalVec s v₀ i) →
        ∀ c : ↥L, (c : AlgebraicClosure ℚ) = regVal s v₀ t k (B v₀).toNat u →
        ∀ y : Fin r × Fin r → ↥L,
        (0 < B v₀ → ∀ p, ((y p : ↥L) : AlgebraicClosure ℚ)
            = regVal s v₀ t 1 1 (evalVec s v₀ p.1 • s p.2 - evalVec s v₀ p.2 • s p.1)) →
        ((B.erase v₀).sum fun w n => (n : ℝ) * prox ν (x v₀) (x w))
          = ((k : ℝ) - 2 * (B v₀ : ℝ)) * Real.log (⨆ i, ν (x v₀ i))
            + (B v₀ : ℝ) * Real.log (⨆ p, ν (y p)) - Real.log (ν c) - m :=
  P2MJensenAssembly.assembly N s hs

end S_ModularCurve_JZero_jensen_good_at
end P2MW
export P2MW.S_ModularCurve_JZero_jensen_good_at (solution)
