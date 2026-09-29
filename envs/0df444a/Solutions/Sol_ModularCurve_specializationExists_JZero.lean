-- Prove2me | solution 1 for ModularCurve.specializationExists_JZero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d60d7d99-24e4-55ff-9c2d-23488a55eea7

import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_of_liesOverPrime
import Theorems.Thm_ModularCurve_eq_zero_of_torsion_of_mem_specializationKernel_jZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_specializationExists_JZero
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub"
p2m_attr_erase "simp" "CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "heckeOperatorBar HeckeOperatorsCommuteBar heckeModuleBar heckeModuleBar_heckeGen_smul JZero HeckeAlg heckeGen IsSpecialization SpecialFibreRelation SpecializationExists eq_zero_of_torsion_of_mem_specializationKernel_jZero"
namespace RA2Specialization
p2m_open "ModularCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_specializationExists_JZero.ModularCurve"

section GroupTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem mul_inv_mem_inertiaSubgroupIn {A : ValuationSubring L} {q : ℕ} {σ σ' : L ≃ₐ[K] L}
    (hσ : A.IsFrobeniusAt σ q) (hσ' : A.IsFrobeniusAt σ' q) :
    σ' * σ⁻¹ ∈ A.inertiaSubgroupIn K := by
  obtain ⟨h1, e1⟩ := hσ
  obtain ⟨h2, e2⟩ := hσ'
  refine ⟨⟨σ', h2⟩ * ⟨σ, h1⟩⁻¹, ?_, rfl⟩
  show _ ∈ MonoidHom.ker _
  rw [MonoidHom.mem_ker]
  refine RingEquiv.ext fun x => ?_
  rw [MulSemiringAction.toRingAut_apply, MulSemiringAction.toRingEquiv_apply, mul_smul]
  set y := (⟨σ, h1⟩ : A.decompositionSubgroup K)⁻¹ • x with hy
  have hx : (⟨σ, h1⟩ : A.decompositionSubgroup K) • y = x := smul_inv_smul _ _
  rw [e1] at hx
  rw [e2, hx]
  rfl

theorem conj_mem_inertiaSubgroupIn {A : ValuationSubring L} {σ₀ τ : L ≃ₐ[K] L}
    (hσ₀ : σ₀ ∈ A.decompositionSubgroup K) (hτ : τ ∈ A.inertiaSubgroupIn K) :
    σ₀ * τ * σ₀⁻¹ ∈ A.inertiaSubgroupIn K := by
  obtain ⟨d, hd, rfl⟩ := hτ
  refine ⟨⟨σ₀, hσ₀⟩ * d * ⟨σ₀, hσ₀⟩⁻¹, ?_, rfl⟩
  have : (A.inertiaSubgroup K).Normal := by
    unfold ValuationSubring.inertiaSubgroup
    infer_instance
  exact this.conj_mem d hd ⟨σ₀, hσ₀⟩

theorem isFrobeniusAt_conj {A : ValuationSubring L} {q : ℕ} {σ₀ σ : L ≃ₐ[K] L}
    (hσ₀ : σ₀ ∈ A.decompositionSubgroup K) (hσ : A.IsFrobeniusAt σ q) :
    A.IsFrobeniusAt (σ₀ * σ * σ₀⁻¹) q := by
  obtain ⟨h1, e1⟩ := hσ
  refine ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ₀ h1) (Subgroup.inv_mem _ hσ₀), fun x => ?_⟩
  have hrw : (⟨σ₀ * σ * σ₀⁻¹, Subgroup.mul_mem _ (Subgroup.mul_mem _ hσ₀ h1)
      (Subgroup.inv_mem _ hσ₀)⟩ : A.decompositionSubgroup K) =
      ⟨σ₀, hσ₀⟩ * ⟨σ, h1⟩ * ⟨σ₀, hσ₀⟩⁻¹ := rfl
  rw [hrw, mul_smul, mul_smul, e1, smul_pow', smul_inv_smul]

end GroupTheory

section Generic

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {J : Type} [AddCommGroup J] [Module HeckeAlg J]
  [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) HeckeAlg J]

variable (K J) in

def esGenSet (A : ValuationSubring L) (ℓ : ℕ) (hℓ : ℓ.Prime) : Set J :=
  {y : J | ∃ τ ∈ A.inertiaSubgroupIn K, ∃ z : J, y = τ • z - z} ∪
  {y : J | ∃ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ ∧ ∃ z : J,
      y = σ • σ • z - heckeGen ⟨ℓ, hℓ⟩ • σ • z + ℓ • z}

theorem smul_mem_esGenSet {A : ValuationSubring L} {ℓ : ℕ} {hℓ : ℓ.Prime} (t : HeckeAlg)
    {y : J} (hy : y ∈ esGenSet K J A ℓ hℓ) : t • y ∈ esGenSet K J A ℓ hℓ := by
  rcases hy with ⟨τ, hτ, z, rfl⟩ | ⟨σ, hσ, z, rfl⟩
  · refine Or.inl ⟨τ, hτ, t • z, ?_⟩
    rw [smul_sub, smul_comm τ t z]
  · refine Or.inr ⟨σ, hσ, t • z, ?_⟩
    have e1 : t • σ • σ • z = σ • σ • t • z := by
      rw [← smul_comm σ t, ← smul_comm σ t]
    have e2 : t • heckeGen ⟨ℓ, hℓ⟩ • σ • z = heckeGen ⟨ℓ, hℓ⟩ • σ • t • z := by
      rw [smul_smul, mul_comm, ← smul_smul, ← smul_comm σ t]
    have e3 : t • ℓ • z = ℓ • t • z := smul_comm t ℓ z
    rw [smul_add, smul_sub, e1, e2, e3]

theorem galois_smul_mem_esGenSet {A : ValuationSubring L} {ℓ : ℕ} {hℓ : ℓ.Prime}
    {σ₀ : L ≃ₐ[K] L} (hσ₀ : σ₀ ∈ A.decompositionSubgroup K)
    {y : J} (hy : y ∈ esGenSet K J A ℓ hℓ) : σ₀ • y ∈ esGenSet K J A ℓ hℓ := by
  rcases hy with ⟨τ, hτ, z, rfl⟩ | ⟨σ, hσ, z, rfl⟩
  · refine Or.inl ⟨σ₀ * τ * σ₀⁻¹, conj_mem_inertiaSubgroupIn hσ₀ hτ, σ₀ • z, ?_⟩
    rw [smul_sub, mul_smul, mul_smul, inv_smul_smul]
  · refine Or.inr ⟨σ₀ * σ * σ₀⁻¹, isFrobeniusAt_conj hσ₀ hσ, σ₀ • z, ?_⟩
    have e1 : (σ₀ * σ * σ₀⁻¹) • σ₀ • z = σ₀ • σ • z := by
      rw [mul_smul, mul_smul, inv_smul_smul]
    have e2 : (σ₀ * σ * σ₀⁻¹) • σ₀ • σ • z = σ₀ • σ • σ • z := by
      rw [mul_smul, mul_smul, inv_smul_smul]
    rw [e1, e2, smul_add, smul_sub, smul_comm σ₀ (heckeGen _), smul_comm σ₀ ℓ]

variable (K J) in

def esKernel (A : ValuationSubring L) (ℓ : ℕ) (hℓ : ℓ.Prime) : Submodule HeckeAlg J :=
  Submodule.span HeckeAlg (esGenSet K J A ℓ hℓ)

theorem mem_closure_of_mem_span {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (S : Set M) (hS : ∀ (r : R) (s : M), s ∈ S → r • s ∈ S) {x : M}
    (hx : x ∈ Submodule.span R S) : x ∈ AddSubgroup.closure S := by
  let M' : Submodule R M :=
    { carrier := AddSubgroup.closure S
      add_mem' := fun ha hb => AddSubgroup.add_mem _ ha hb
      zero_mem' := AddSubgroup.zero_mem _
      smul_mem' := fun r x hx => by
        change x ∈ AddSubgroup.closure S at hx
        change r • x ∈ AddSubgroup.closure S
        induction hx using AddSubgroup.closure_induction with
        | mem s hs => exact AddSubgroup.subset_closure (hS r s hs)
        | zero => rw [smul_zero]; exact AddSubgroup.zero_mem _
        | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
        | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha }
  have hle : Submodule.span R S ≤ M' := Submodule.span_le.mpr fun s hs =>
    (AddSubgroup.subset_closure hs : s ∈ AddSubgroup.closure S)
  exact hle hx

theorem mem_closure_of_mem_esKernel {A : ValuationSubring L} {ℓ : ℕ} {hℓ : ℓ.Prime} {x : J}
    (hx : x ∈ esKernel K J A ℓ hℓ) : x ∈ AddSubgroup.closure (esGenSet K J A ℓ hℓ) :=
  mem_closure_of_mem_span _ (fun t _ hs => smul_mem_esGenSet t hs) hx

theorem exists_isSpecialization (p : ℕ) (A : ValuationSubring L) (ℓ : ℕ) (hℓ : ℓ.Prime)
    {σ₀ : L ≃ₐ[K] L} (hσ₀ : A.IsFrobeniusAt σ₀ ℓ)
    (hinj : ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) →
      x ∈ AddSubgroup.closure (esGenSet K J A ℓ hℓ) → x = 0) :
    ∃ (J' : Type) (_ : AddCommGroup J') (_ : Module HeckeAlg J') (sp : J →+ J')
      (F : J' →+ J'),
      IsSpecialization (K := K) p J J' A ℓ sp F ∧ SpecialFibreRelation J' ℓ hℓ F := by
  have hD : σ₀ ∈ A.decompositionSubgroup K := hσ₀.mem_decompositionSubgroup
  let M : Submodule HeckeAlg J := esKernel K J A ℓ hℓ
  let f : J →ₗ[HeckeAlg] J := DistribSMul.toLinearMap HeckeAlg J σ₀
  have hf : ∀ x : J, f x = σ₀ • x := fun _ => rfl
  have hle : M ≤ M.comap f := Submodule.span_le.mpr fun s hs =>
    show f s ∈ M from Submodule.subset_span (galois_smul_mem_esGenSet hD hs)
  refine ⟨J ⧸ M, inferInstance, inferInstance, M.mkQ.toAddMonoidHom,
    (M.mapQ M f hle).toAddMonoidHom, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  ·
    intro T x
    exact M.mkQ.map_smul T x
  ·
    intro τ hτ x
    show M.mkQ (τ • x) = M.mkQ x
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
    exact Submodule.subset_span (Or.inl ⟨τ, hτ, x, rfl⟩)
  ·
    intro σ hσ x
    show M.mkQ (σ • x) = M.mapQ M f hle (M.mkQ x)
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.mapQ_apply, hf,
      Submodule.Quotient.eq]
    have e : (σ * σ₀⁻¹) • σ₀ • x - σ₀ • x = σ • x - σ₀ • x := by
      rw [mul_smul, inv_smul_smul]
    rw [← e]
    exact Submodule.subset_span (Or.inl ⟨σ * σ₀⁻¹, mul_inv_mem_inertiaSubgroupIn hσ₀ hσ,
      σ₀ • x, rfl⟩)
  ·
    intro x hx h0
    have hxM : x ∈ M := by
      have h0' : M.mkQ x = 0 := h0
      rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h0'
    exact hinj x hx (mem_closure_of_mem_esKernel hxM)
  ·
    intro y
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective M y
    show M.mapQ M f hle (M.mapQ M f hle (M.mkQ x)) - heckeGen ⟨ℓ, hℓ⟩ • M.mapQ M f hle (M.mkQ x)
      + ℓ • M.mkQ x = 0
    have h1 : M.mapQ M f hle (M.mkQ x) = M.mkQ (σ₀ • x) := by
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hf]; rfl
    have h2 : M.mapQ M f hle (M.mkQ (σ₀ • x)) = M.mkQ (σ₀ • σ₀ • x) := by
      rw [Submodule.mkQ_apply, Submodule.mapQ_apply, hf]; rfl
    rw [h1, h2, ← map_smul, ← map_nsmul, ← map_sub, ← map_add, Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Or.inr ⟨σ₀, hσ₀, x, rfl⟩)

variable (K L J) in

theorem specializationExists_of (N p : ℕ)
    (hfrob : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N * p → ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∃ σ : L ≃ₐ[K] L, A.IsFrobeniusAt σ ℓ)
    (hinj : ∀ ℓ : ℕ, (hℓ : ℓ.Prime) → ¬ ℓ ∣ N * p → ∀ A : ValuationSubring L, A.LiesOverPrime ℓ →
      ∀ x : J, (∃ n : ℕ, p ^ n • x = 0) → x ∈ AddSubgroup.closure (esGenSet K J A ℓ hℓ) → x = 0) :
    SpecializationExists (K := K) (L := L) N p J := by
  intro ℓ hℓ hℓN A hA
  obtain ⟨σ₀, hσ₀⟩ := hfrob ℓ hℓ hℓN A hA
  exact exists_isSpecialization p A ℓ hℓ hσ₀ (hinj ℓ hℓ hℓN A hA)

end Generic

theorem esGenSet_jZero_eq (N : ℕ) [NeZero N] (hcomm : HeckeOperatorsCommuteBar N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ : ℕ) (hℓ : ℓ.Prime) :
    (letI := heckeModuleBar N; esGenSet ℚ (JZero N) A ℓ hℓ) =
      ({y : JZero N | ∃ τ ∈ A.inertiaSubgroupIn ℚ, ∃ z : JZero N, y = τ • z - z} ∪
       {y : JZero N | ∃ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          A.IsFrobeniusAt σ ℓ ∧ ∃ z : JZero N,
            y = σ • σ • z - heckeOperatorBar N ⟨ℓ, hℓ⟩ (σ • z) + ℓ • z}) := by
  letI := heckeModuleBar N
  unfold esGenSet
  congr 1
  ext y
  simp only [Set.mem_setOf_eq, heckeModuleBar_heckeGen_smul hcomm]

end ModularCurve.RA2Specialization

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_specializationExists_JZero.ModularCurve ModularCurve.RA2Specialization in
theorem solution (N p : ℕ) [NeZero N] (hcomm : ModularCurve.HeckeOperatorsCommuteBar N) : letI := ModularCurve.heckeModuleBar N; ∀ (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) ModularCurve.HeckeAlg (ModularCurve.JZero N)), ModularCurve.SpecializationExists (K := ℚ) (L := AlgebraicClosure ℚ) N p (ModularCurve.JZero N) := by
  letI := ModularCurve.heckeModuleBar N
  intro hsc
  refine specializationExists_of ℚ (AlgebraicClosure ℚ) (JZero N) N p
    (fun ℓ hℓ _ A hA => ValuationSubring.exists_isFrobeniusAt_of_liesOverPrime hℓ A hA) ?_
  intro ℓ hℓ hℓN A hA x hx hmem
  rw [esGenSet_jZero_eq N hcomm A ℓ hℓ] at hmem
  exact ModularCurve.eq_zero_of_torsion_of_mem_specializationKernel_jZero N p hℓ hℓN A hA x hx hmem

end
end S_ModularCurve_specializationExists_JZero
end P2MW
export P2MW.S_ModularCurve_specializationExists_JZero (solution)
