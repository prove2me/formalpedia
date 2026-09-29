-- Prove2me | solution 1 for ModularCurve.JZero.exists_isRepOf_heightForm_lower
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/092aeb49-ab89-5ad8-ac30-017668d157b1

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_ModularCurve_JZeroHeightFormPositivity
import Theorems.Thm_ModularCurve_JZero_exists_isRepOf_baseMass_le_heightForm
import Theorems.Thm_ModularCurve_JZero_divNaiveHeight_le_baseMass_of_isRepOf
import Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_mul_baseHt
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Definitions.Def_P2M_Util
import Definitions.Def_Compat_Mathlib430

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JZero_exists_isRepOf_heightForm_lower
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.Gamma0Pair.isElliptic WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.jqNModC_one ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix"
p2m_attr_erase "simp" "ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec AlgebraicCurve.Place.taylorRem_zero AlgebraicCurve.jetMatrix_order_zero AlgebraicCurve.Place.taylorCoeff_zero AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂"
p2m_attr_erase "simp" "PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.chowForm_zero AlgebraicCurve.secProd_zero ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one MvPolynomial.logMahlerMeasure_C MvPolynomial.logMahlerMeasure_X MvPolynomial.logMahlerMeasure_zero MvPolynomial.volume_torusBox MvPolynomial.logMahlerMeasure_monomial MvPolynomial.logMahlerMeasure_one MvPolynomial.norm_circleMap_zero_one MvPolynomial.volume_real_torusBox"

set_option autoImplicit false

p2m_open "ModularCurve ModularCurve.JZero AlgebraicCurve~genus"

namespace JZeroPositivity

private theorem exists_neg_le_baseMass_of_isRepOf (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (g' : ℕ) {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      IsRepOf N K g' c D → -B ≤ baseMass N s D := by
  classical
  obtain ⟨C, hC⟩ := ModularCurve.JZero.exists_pointHt_le_mul_baseHt N s hs

  have hdeg : (0 : ℝ) < (embDegree N : ℝ) := by
    have h : 0 < embDegree N := by unfold embDegree; omega
    exact_mod_cast h

  have hpt : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), 0 ≤ pointHt s v := by
    intro v
    unfold pointHt absLogHeight
    haveI := finiteDimensional_adjoin_range (evalVec s v)
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (Height.logHeight_nonneg _)

  have hfloor : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N), v ≠ cuspInftyBar N →
      -(max C 0) ≤ (embDegree N : ℝ) * baseHt s (cuspInftyBar N) v := by
    intro v hv
    have h1 := hC v hv
    have h2 := hpt v
    have h3 := le_max_left C 0
    linarith

  have hdegsum : ∀ D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      Divisor.degree D = D.sum fun _ n => n := by
    intro D
    unfold Divisor.degree
    rw [Finsupp.liftAddHom_apply]
    simp only [Finsupp.sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [AddMonoidHom.mulRight_apply, ModularCurve.deg_eq_one_modularFunctionFieldBar N v,
      Nat.cast_one, mul_one]

  have hmass : ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)),
      IsRepOf N K g' c D →
        (∀ v, 0 ≤ (D.erase (cuspInftyBar N)) v) ∧ (offBaseMass N D : ℝ) ≤ (g' : ℝ) := by
    intro c D hD
    obtain ⟨E, hDeff, hshape, -, -⟩ := hD
    refine ⟨fun v => ?_, ?_⟩
    · by_cases hv : v = cuspInftyBar N
      · rw [hv, Finsupp.erase_same]
      · rw [Finsupp.erase_ne hv]; exact hDeff v
    · have hsm : ((g' : ℤ) • Finsupp.single (cuspInftyBar N) (1 : ℤ)
            : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
          = Finsupp.single (cuspInftyBar N) (g' : ℤ) := by
        ext v
        rw [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply, Finsupp.single_apply]
        split_ifs <;> simp
      have hdegD : Divisor.degree D = (g' : ℤ) := by
        rw [← hshape, map_add, hsm, Divisor.degree_single, (Divisor.mem_degZero).mp E.2,
          ModularCurve.deg_eq_one_modularFunctionFieldBar N (cuspInftyBar N), Nat.cast_one, mul_one,
          zero_add]
      have hsplit : Divisor.degree D = D (cuspInftyBar N) + offBaseMass N D := by
        rw [hdegsum D]
        unfold offBaseMass
        exact (Finsupp.add_sum_erase' D (cuspInftyBar N) (fun _ n => n) fun _ => rfl).symm
      have h0 := hDeff (cuspInftyBar N)
      have hle : offBaseMass N D ≤ (g' : ℤ) := by omega
      exact_mod_cast hle

  refine ⟨max C 0 * (g' : ℝ) / (embDegree N : ℝ),
    div_nonneg (mul_nonneg (le_max_right C 0) (Nat.cast_nonneg g')) hdeg.le, fun c D hD => ?_⟩
  obtain ⟨hD', hoffle⟩ := hmass c D hD
  have hsum : (embDegree N : ℝ) * baseMass N s D
      = ∑ v ∈ (D.erase (cuspInftyBar N)).support,
          ((D.erase (cuspInftyBar N)) v : ℝ) * ((embDegree N : ℝ) * baseHt s (cuspInftyBar N) v) := by
    unfold baseMass
    rw [Finsupp.sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun v _ => by ring
  have hterm : ∀ v ∈ (D.erase (cuspInftyBar N)).support,
      ((D.erase (cuspInftyBar N)) v : ℝ) * (-(max C 0))
        ≤ ((D.erase (cuspInftyBar N)) v : ℝ) * ((embDegree N : ℝ) * baseHt s (cuspInftyBar N) v) := by
    intro v hv
    have hvne : v ≠ cuspInftyBar N := by
      rintro rfl
      exact (Finsupp.mem_support_iff.mp hv) Finsupp.erase_same
    exact mul_le_mul_of_nonneg_left (hfloor v hvne) (by exact_mod_cast hD' v)
  have hoffR : (∑ v ∈ (D.erase (cuspInftyBar N)).support, ((D.erase (cuspInftyBar N)) v : ℝ))
      = (offBaseMass N D : ℝ) := by
    have h : offBaseMass N D
        = ∑ v ∈ (D.erase (cuspInftyBar N)).support, (D.erase (cuspInftyBar N)) v := rfl
    rw [h, Int.cast_sum]
  have key : -(max C 0 * (g' : ℝ)) ≤ (embDegree N : ℝ) * baseMass N s D :=
    calc -(max C 0 * (g' : ℝ))
        ≤ -(max C 0 * (offBaseMass N D : ℝ)) :=
          neg_le_neg (mul_le_mul_of_nonneg_left hoffle (le_max_right C 0))
      _ = (∑ v ∈ (D.erase (cuspInftyBar N)).support, ((D.erase (cuspInftyBar N)) v : ℝ))
            * (-(max C 0)) := by rw [hoffR]; ring
      _ = ∑ v ∈ (D.erase (cuspInftyBar N)).support,
            ((D.erase (cuspInftyBar N)) v : ℝ) * (-(max C 0)) := Finset.sum_mul _ _ _
      _ ≤ ∑ v ∈ (D.erase (cuspInftyBar N)).support,
            ((D.erase (cuspInftyBar N)) v : ℝ) * ((embDegree N : ℝ) * baseHt s (cuspInftyBar N) v) :=
          Finset.sum_le_sum hterm
      _ = (embDegree N : ℝ) * baseMass N s D := hsum.symm
  have hdiv : -(max C 0 * (g' : ℝ)) / (embDegree N : ℝ) ≤ baseMass N s D := by
    rw [div_le_iff₀ hdeg]; linarith [key]
  calc -(max C 0 * (g' : ℝ) / (embDegree N : ℝ))
      = -(max C 0 * (g' : ℝ)) / (embDegree N : ℝ) := (neg_div _ _).symm
    _ ≤ baseMass N s D := hdiv

private theorem heightFormAux_eq_mul_of {F : Type} [Field F] [Algebra (AlgebraicClosure ℚ) F] {r : ℕ}
    (s : Fin r → F) (γ : ℤ) (b : Place (AlgebraicClosure ℚ) F) (D : Divisor (AlgebraicClosure ℚ) F)
    (hoff : ∀ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2 = 0)
    (hself : ∀ v ∈ D.support, ((D v : ℝ) * ((D v : ℝ) - 1) / 2) * baseHt s b v = 0)
    (hlin : ((D.sum fun _ n => (n : ℝ)) - 1) * (D.sum fun v n => (n : ℝ) * baseHt s b v) = 0) :
    heightFormAux s γ b D = (γ : ℝ) * (D.sum fun v n => (n : ℝ) * baseHt s b v) := by
  have h1 : (∑ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2) = 0 :=
    Finset.sum_eq_zero hoff
  have h2 : (D.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v) = 0 :=
    Finset.sum_eq_zero hself
  have h3 : ((γ : ℝ) + (D.sum fun _ n => (n : ℝ)) - 1) * (D.sum fun v n => (n : ℝ) * baseHt s b v)
      - (∑ p ∈ D.support.offDiag, ((D p.1 : ℝ) * (D p.2 : ℝ)) * pairHt s p.1 p.2) / 2
      - (2 - 2 * (γ : ℝ)) * (D.sum fun v n => ((n : ℝ) * ((n : ℝ) - 1) / 2) * baseHt s b v)
      = (γ : ℝ) * (D.sum fun v n => (n : ℝ) * baseHt s b v)
        + ((D.sum fun _ n => (n : ℝ)) - 1) * (D.sum fun v n => (n : ℝ) * baseHt s b v) := by
    rw [h1, h2]; ring
  unfold heightFormAux
  rw [h3, hlin, add_zero]

private theorem heightForm_of_offBaseMass_le_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N)
    (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hD : ∀ v, 0 ≤ D v) :
    0 ≤ offBaseMass N D ∧
    (offBaseMass N D ≤ 1 →
      heightForm N s D
        = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) * baseMass N s D) ∧
    (offBaseMass N D = 0 → baseMass N s D = 0) := by
  classical

  have hD' : ∀ v, 0 ≤ (D.erase (cuspInftyBar N)) v := by
    intro v
    by_cases hv : v = cuspInftyBar N
    · rw [hv, Finsupp.erase_same]
    · rw [Finsupp.erase_ne hv]; exact hD v
  have hoff : offBaseMass N D
      = ∑ v ∈ (D.erase (cuspInftyBar N)).support, (D.erase (cuspInftyBar N)) v := rfl
  have hnn : 0 ≤ offBaseMass N D := by
    rw [hoff]; exact Finset.sum_nonneg fun v _ => hD' v

  have hpos : ∀ v ∈ (D.erase (cuspInftyBar N)).support, 1 ≤ (D.erase (cuspInftyBar N)) v := by
    intro v hv
    have h1 := Finsupp.mem_support_iff.mp hv
    have h2 := hD' v
    omega
  have hle : ∀ v ∈ (D.erase (cuspInftyBar N)).support,
      (D.erase (cuspInftyBar N)) v ≤ offBaseMass N D := by
    intro v hv
    rw [hoff]
    exact Finset.single_le_sum (fun w _ => hD' w) hv

  have hcast : ((D.erase (cuspInftyBar N)).sum fun _ n => (n : ℝ)) = (offBaseMass N D : ℝ) := by
    rw [hoff, Int.cast_sum]; rfl

  have hzero : offBaseMass N D = 0 → baseMass N s D = 0 := by
    intro h0
    have hz : ∀ v ∈ (D.erase (cuspInftyBar N)).support, (D.erase (cuspInftyBar N)) v = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun v _ => hD' v).mp (by rw [← hoff]; exact h0)
    unfold baseMass
    exact Finset.sum_eq_zero fun v hv => by rw [hz v hv]; simp
  refine ⟨hnn, ?_, hzero⟩
  intro hm

  have hoffDiag : ∀ p ∈ (D.erase (cuspInftyBar N)).support.offDiag,
      (((D.erase (cuspInftyBar N)) p.1 : ℝ) * ((D.erase (cuspInftyBar N)) p.2 : ℝ))
        * pairHt s p.1 p.2 = 0 := by
    intro p hp
    rw [Finset.mem_offDiag] at hp
    obtain ⟨h1, h2, h12⟩ := hp
    exfalso
    have e1 : ∑ v ∈ (D.erase (cuspInftyBar N)).support.erase p.1, (D.erase (cuspInftyBar N)) v
          + (D.erase (cuspInftyBar N)) p.1
        = ∑ v ∈ (D.erase (cuspInftyBar N)).support, (D.erase (cuspInftyBar N)) v :=
      Finset.sum_erase_add _ _ h1
    have e2 : (D.erase (cuspInftyBar N)) p.2
        ≤ ∑ v ∈ (D.erase (cuspInftyBar N)).support.erase p.1, (D.erase (cuspInftyBar N)) v :=
      Finset.single_le_sum (f := fun v => (D.erase (cuspInftyBar N)) v) (fun w _ => hD' w)
        (Finset.mem_erase.mpr ⟨Ne.symm h12, h2⟩)
    have e3 := hpos p.1 h1
    have e4 := hpos p.2 h2
    have e5 : ∑ v ∈ (D.erase (cuspInftyBar N)).support, (D.erase (cuspInftyBar N)) v ≤ 1 := by
      rw [← hoff]; exact hm
    omega

  have hself : ∀ v ∈ (D.erase (cuspInftyBar N)).support,
      (((D.erase (cuspInftyBar N)) v : ℝ) * (((D.erase (cuspInftyBar N)) v : ℝ) - 1) / 2)
        * baseHt s (cuspInftyBar N) v = 0 := by
    intro v hv
    have h1 : (D.erase (cuspInftyBar N)) v = 1 := by
      have := hpos v hv; have := hle v hv; omega
    rw [h1]; simp

  have hlin : (((D.erase (cuspInftyBar N)).sum fun _ n => (n : ℝ)) - 1)
      * ((D.erase (cuspInftyBar N)).sum fun v n => (n : ℝ) * baseHt s (cuspInftyBar N) v) = 0 := by
    rw [hcast]
    rcases (show offBaseMass N D = 0 ∨ offBaseMass N D = 1 by omega) with h0 | h1
    · have hb : baseMass N s D = 0 := hzero h0
      unfold baseMass at hb
      rw [hb, mul_zero]
    · rw [h1]; simp
  unfold JZero.heightForm AlgebraicCurve.heightForm baseMass
  rw [heightFormAux_eq_mul_of s _ (cuspInftyBar N) (D.erase (cuspInftyBar N)) hoffDiag hself hlin,
    Int.cast_natCast]

end JZeroPositivity

theorem solution (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K] (g' : ℕ)
    {r : ℕ} (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ η C : ℝ, 0 < η ∧ ∀ (c : ↥(JZero N ^+ ↥K.fixingSubgroup))
      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)), JZero.IsRepOf N K g' c D →
      ∃ D₂ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N), JZero.IsRepOf N K g' c D₂ ∧
        η * divNaiveHeight N K g' D₂ - C ≤ JZero.heightForm N s D₂ := by
  obtain ⟨γ, hγ⟩ : ∃ x : ℝ, x = (genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) : ℝ) :=
    ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [hγ]; exact Nat.cast_nonneg _
  obtain ⟨κ, C₁, hκ, h1⟩ := ModularCurve.JZero.divNaiveHeight_le_baseMass_of_isRepOf N K g' s hs
  obtain ⟨B, hB0, hB⟩ := JZeroPositivity.exists_neg_le_baseMass_of_isRepOf N K g' s hs
  obtain ⟨η, C₃, hη, h3⟩ :=
    ModularCurve.JZero.exists_isRepOf_baseMass_le_heightForm N K g' s hs (γ + 1) (by linarith)
  rw [← hγ] at h3

  obtain ⟨m₁, hm₁⟩ : ∃ x : ℝ, x = min η 1 := ⟨_, rfl⟩
  have hm0 : 0 < m₁ := by rw [hm₁]; exact lt_min hη one_pos
  have hm1 : m₁ ≤ η := by rw [hm₁]; exact min_le_left _ _
  have hm1' : m₁ ≤ 1 := by rw [hm₁]; exact min_le_right _ _
  have hκ1 : 0 < κ + 1 := by linarith
  have hκ1' : κ + 1 ≠ 0 := hκ1.ne'
  obtain ⟨q, hq⟩ : ∃ x : ℝ, x = m₁ / (κ + 1) := ⟨_, rfl⟩
  have hq0 : 0 < q := by rw [hq]; exact div_pos hm0 hκ1
  have hqm : q * (κ + 1) = m₁ := by rw [hq]; field_simp
  have hqk : q * κ ≤ 1 := by linarith
  refine ⟨q, max C₃ 0 + q * C₁ + (η + 1 + γ) * B, hq0, ?_⟩
  intro c D hD
  by_cases hguard : γ ≤ (γ + 1) * ((offBaseMass N D : ℝ) - 1)
  ·
    obtain ⟨D₂, hD₂, hQ⟩ := h3 c D hD hguard
    refine ⟨D₂, hD₂, ?_⟩
    have hh := h1 c D₂ hD₂
    have hb := hB c D₂ hD₂
    have e1 := mul_le_mul_of_nonneg_left hh hq0.le
    have e2 := mul_le_mul_of_nonneg_left hb hq0.le
    have e3 := mul_le_mul_of_nonneg_left hb (sub_nonneg.mpr hm1)
    have e4 : m₁ * baseMass N s D₂ = q * (κ * baseMass N s D₂) + q * baseMass N s D₂ := by
      rw [← hqm]; ring
    have hqκ : 0 ≤ q * κ := mul_nonneg hq0.le hκ
    have e5 : (η - m₁ + q) * B ≤ (η + 1 + γ) * B :=
      mul_le_mul_of_nonneg_right (by linarith) hB0
    have e8 := le_max_left C₃ 0
    linarith [e1, e2, e3, e4, e5, e8, hQ]
  ·
    have hlt : (γ + 1) * ((offBaseMass N D : ℝ) - 1) < γ := not_le.mp hguard
    have hD' := hD
    obtain ⟨_E, hDeff, -, -, -⟩ := hD'
    obtain ⟨hmass0, hQeq, hbm0⟩ := JZeroPositivity.heightForm_of_offBaseMass_le_one N s D hDeff
    have hm2 : offBaseMass N D ≤ 1 := by
      by_contra hcon
      have h2 : (2 : ℤ) ≤ offBaseMass N D := by omega
      have h2r : (2 : ℝ) ≤ (offBaseMass N D : ℝ) := by exact_mod_cast h2
      have e := mul_le_mul_of_nonneg_left (show (1 : ℝ) ≤ (offBaseMass N D : ℝ) - 1 by linarith)
        (show (0 : ℝ) ≤ γ + 1 by linarith)
      linarith [e, hlt]
    have hQ : heightForm N s D = γ * baseMass N s D := by rw [hγ]; exact hQeq hm2
    refine ⟨D, hD, ?_⟩
    have hh := h1 c D hD
    have hb := hB c D hD
    have e8 := le_max_right C₃ 0
    rw [hQ]
    rcases (show offBaseMass N D = 0 ∨ offBaseMass N D = 1 by omega) with h0 | h1m
    ·
      have hbm : baseMass N s D = 0 := hbm0 h0
      rw [hbm] at hh ⊢
      have e1 := mul_le_mul_of_nonneg_left hh hq0.le
      have e9 : 0 ≤ (η + 1 + γ) * B := by positivity
      linarith [e1, e8, e9]
    ·
      have hγpos : 0 < γ := by
        have := hlt
        rw [h1m] at this
        push_cast at this
        linarith
      have hγ1 : 1 ≤ γ := by
        rw [hγ] at hγpos ⊢
        have : 0 < genusFF (AlgebraicClosure ℚ) (modularFunctionFieldBar N) := by
          exact_mod_cast hγpos
        exact_mod_cast this
      have e1 := mul_le_mul_of_nonneg_left hh hq0.le
      have e6 := mul_le_mul_of_nonneg_left hb (show 0 ≤ γ - q * κ by linarith)
      have e7 : 0 ≤ q * κ * B := by positivity
      have e9 : 0 ≤ (η + 1) * B := by positivity
      linarith [e1, e6, e7, e8, e9]

#print axioms solution

end S_ModularCurve_JZero_exists_isRepOf_heightForm_lower
end P2MW
export P2MW.S_ModularCurve_JZero_exists_isRepOf_heightForm_lower (solution)
