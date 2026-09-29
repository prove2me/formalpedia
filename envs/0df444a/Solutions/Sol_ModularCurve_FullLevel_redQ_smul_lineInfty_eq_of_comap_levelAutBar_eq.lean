-- Prove2me | solution 1 for ModularCurve.FullLevel.redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/92f2e866-36af-5bb3-ae68-affbe5401a09

import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_ne_of_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ"
p2m_attr_erase "simp" "KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun"
p2m_attr_erase "simp" "KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one"
p2m_attr_erase "simp" "TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut"
p2m_attr_erase "simp" "ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false
set_option linter.unusedSectionVars false

p2m_open "AlgebraicCurve ModularCurve P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq.ModularCurve ModularCurve.FullLevel P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq.ModularCurve.FullLevel IsLocalRing CongruenceSubgroup"
open scoped MatrixGroups

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap FullLevel.levelAutBar_mul"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty fieldBar Idx levelAutBar redQ levelAutBar_mul comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq comap_levelAutBar_ne_of_dvd"
namespace W1a
namespace Lift
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ)

private theorem natCast_M'_ne_zero (hqM' : ¬ q ∣ M') : ((M' : ℕ) : ZMod q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact hqM'

private noncomputable def crt (r : ZMod q) : ℤ := ((r * ((M' : ℕ) : ZMod q)⁻¹).val : ℤ) * (M' : ℤ)

private theorem crt_cast (hqM' : ¬ q ∣ M') (r : ZMod q) : ((crt q M' r : ℤ) : ZMod q) = r := by
  unfold crt
  push_cast
  rw [ZMod.natCast_zmod_val, inv_mul_cancel_right₀ (natCast_M'_ne_zero q M' hqM')]

private theorem crt_dvd (r : ZMod q) : (M' : ℤ) ∣ crt q M' r := ⟨_, by unfold crt; ring⟩

private theorem crt_castM' (r : ZMod q) : ((crt q M' r : ℤ) : ZMod M') = 0 := by
  obtain ⟨k, hk⟩ := crt_dvd q M' r
  rw [hk]; push_cast; simp

private def Tz (a : ℤ) : SL(2, ℤ) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def Lz (b : ℤ) : SL(2, ℤ) := ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

private theorem Tz_mem_gamma0 (a : ℤ) : Tz a ∈ Gamma0 M' := by
  rw [Gamma0_mem]; simp [Tz]

private theorem Lz_mem_gamma0 {b : ℤ} (hb : ((b : ℤ) : ZMod M') = 0) : Lz b ∈ Gamma0 M' := by
  rw [Gamma0_mem]; simpa [Lz] using hb

variable {q}

private def Tq (a : ZMod q) : SL(2, ZMod q) := ⟨!![1, a; 0, 1], by simp [Matrix.det_fin_two_of]⟩

private def Lq (b : ZMod q) : SL(2, ZMod q) := ⟨!![1, 0; b, 1], by simp [Matrix.det_fin_two_of]⟩

local notation "red" => Matrix.SpecialLinearGroup.map (n := Fin 2) (Int.castRingHom (ZMod q))

private theorem red_Tz (a : ℤ) : red (Tz a) = Tq (a : ZMod q) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [Tz, Tq]

private theorem red_Lz (b : ℤ) : red (Lz b) = Lq (b : ZMod q) := by
  ext i j
  rw [Matrix.SpecialLinearGroup.map_apply_coe]
  fin_cases i <;> fin_cases j <;> simp [Lz, Lq]

private theorem coe_Tq_Lq_Tq (x c y : ZMod q) :
    ((Tq x * Lq c * Tq y : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      !![1 + x * c, (1 + x * c) * y + x; c, c * y + 1] := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Tq, Lq, Matrix.mul_apply, Fin.sum_univ_two]

private theorem eq_Tq_Lq_Tq (g : SL(2, ZMod q)) (hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0) :
    g = Tq (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) *
      Lq ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) *
      Tq (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 -
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 1 := by
    have h := g.det_coe
    rw [Matrix.det_fin_two] at h
    exact h
  have hx : 1 + ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 *
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 := by
    rw [div_mul_cancel₀ _ hc]; ring
  have hy : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 *
      (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) + 1 =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 := by
    rw [mul_div_cancel₀ _ hc]; ring
  have hb : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 *
      (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0) +
      ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 =
      (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 := by
    field_simp
    linear_combination hdet
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  rw [coe_Tq_Lq_Tq, hx]
  fin_cases i <;> fin_cases j
  · simp
  · simpa using hb.symm
  · simp
  · simpa using hy.symm

variable (q)

private theorem exists_mem_gamma0_map_eq (hqM' : ¬ q ∣ M') (g : SL(2, ZMod q)) :
    ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ red γ = g := by

  have key : ∀ g : SL(2, ZMod q), (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 →
      ∃ γ : SL(2, ℤ), γ ∈ Gamma0 M' ∧ red γ = g := by
    intro g hc
    refine ⟨Tz (crt q M' (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)) *
        Lz (crt q M' ((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)) *
        Tz (crt q M' (((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 - 1) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0)), ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Tz_mem_gamma0 M' _)
        (Lz_mem_gamma0 M' (crt_castM' q M' _))) (Tz_mem_gamma0 M' _)
    · rw [map_mul, map_mul, red_Tz, red_Lz, red_Tz, crt_cast q M' hqM', crt_cast q M' hqM',
        crt_cast q M' hqM']
      exact (eq_Tq_Lq_Tq g hc).symm
  by_cases hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0
  · exact key g hc
  · push Not at hc

    have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 -
        (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 * (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 1 := by
      have h := g.det_coe
      rw [Matrix.det_fin_two] at h
      exact h
    have ha : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 ≠ 0 := by
      intro h0; rw [h0, hc] at hdet; simp at hdet
    have hc' : ((Lq (1 : ZMod q) * g : SL(2, ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      simp [Lq, Matrix.mul_apply, Fin.sum_univ_two, hc, ha]
    obtain ⟨γ', hγ', hred'⟩ := key _ hc'
    refine ⟨(Lz (crt q M' 1))⁻¹ * γ', Subgroup.mul_mem _ (Subgroup.inv_mem _ (Lz_mem_gamma0 M' (crt_castM' q M' _))) hγ', ?_⟩
    rw [map_mul, map_inv, hred', red_Lz, crt_cast q M' hqM', inv_mul_cancel_left]

private def swapElem (t : ZMod q) : SL(2, ZMod q) := ⟨!![t, -t ^ 2 - 1; 1, -t], by
  rw [Matrix.det_fin_two_of]; ring⟩

private theorem swapElem_mulVec_inf (t : ZMod q) :
    (swapElem q t : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0] = ![t, 1] := by
  ext i; fin_cases i <;> simp [swapElem, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem swapElem_mulVec_pt (t : ZMod q) :
    (swapElem q t : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![t, 1] = ![-1, 0] := by
  ext i; fin_cases i <;> simp [swapElem, Matrix.mulVec, dotProduct, Fin.sum_univ_two] <;> ring

end ModularCurve.FullLevel.W1a.Lift

namespace ModularCurve
p2m_export "ModularCurve" "coeffMap FullLevel.levelAutBar_mul"
namespace FullLevel
p2m_export "ModularCurve.FullLevel" "lineInfty fieldBar Idx levelAutBar redQ levelAutBar_mul comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq comap_levelAutBar_ne_of_dvd"
namespace W1a
p2m_open "ModularCurve.FullLevel ModularCurve"

variable (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']

section ProjLine

variable {q M'}

private theorem redQ_coe (γ : SL(2, ℤ)) :
    ((redQ q γ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) := rfl

private theorem mulVec_ne_zero (g : CuspidalType.GL2 q) {v : Fin 2 → ZMod q} (hv : v ≠ 0) :
    (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v ≠ 0 := by
  intro h0
  apply hv
  have h1 := congrArg ((g⁻¹ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec h0
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_zero, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mulVec] at h1
  exact h1

private theorem redQ_smul_mk (γ : SL(2, ℤ)) (v : Fin 2 → ZMod q) (hv : v ≠ 0) :
    redQ q γ • Projectivization.mk (ZMod q) v hv =
      Projectivization.mk (ZMod q)
        (((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ : SL(2, ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec v)
        (mulVec_ne_zero (redQ q γ) hv) := by
  rw [Projectivization.smul_mk]
  rfl

private theorem mk_neg_one_zero :
    Projectivization.mk (ZMod q) (![-1, 0] : Fin 2 → ZMod q) (by simp) = lineInfty q := by
  rw [lineInfty, Projectivization.mk_eq_mk_iff']
  exact ⟨-1, by ext i; fin_cases i <;> simp⟩

end ProjLine

end ModularCurve.FullLevel.W1a

open _root_.ModularCurve.FullLevel _root_.P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq.ModularCurve.FullLevel in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) (ζ : Idx q)
    (O : ValuationSubring (fieldBar q M'))
    (hO : ∀ f : fieldBar q M', f ∈ O ↔
      ∃ x y : LaurentSeries A, coeffMap (IsLocalRing.residue A) y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x)
    (δ : SL(2, ℤ)) (hδ : δ ∈ Gamma0 M')
    (h : O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom = O) :
    redQ q δ • lineInfty q = lineInfty q  := by
  classical
  by_contra hne

  set g : SL(2, ZMod q) := Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) δ with hg
  have hcol : redQ q δ • lineInfty q =
      Projectivization.mk (ZMod q) ((g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0])
        (W1a.mulVec_ne_zero (redQ q δ) (by simp)) := by
    rw [lineInfty, W1a.redQ_smul_mk]
  have hmv : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).mulVec ![1, 0] =
      ![(g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0, (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0] := by
    ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

  have hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 ≠ 0 := by
    intro hc
    apply hne
    have ha0 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 ≠ 0 := by
      intro ha0
      have hdet := g.det_coe
      rw [Matrix.det_fin_two, ha0, hc] at hdet
      simp at hdet
    rw [hcol, lineInfty, Projectivization.mk_eq_mk_iff']
    refine ⟨(g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0, ?_⟩
    rw [hmv, hc]
    ext i; fin_cases i <;> simp

  obtain ⟨b, hb, hbred⟩ := W1a.Lift.exists_mem_gamma0_map_eq q M' hqM'
    (W1a.Lift.Tq (-((g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) / (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0))
  have hbfix : redQ q b • lineInfty q = lineInfty q := by
    rw [lineInfty, W1a.redQ_smul_mk]
    simp_rw [hbred]
    congr 1
    ext i; fin_cases i <;> simp [W1a.Lift.Tq, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  have hK1 := comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq q hq M' hqM' A hA ζ O hO b hb hbfix

  have hstab : O.comap (levelAutBar q M' ζ (b * δ)).toAlgHom.toRingHom = O := by
    rw [ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ b δ hb hδ]
    have : O.comap ((levelAutBar q M' ζ b).trans (levelAutBar q M' ζ δ)).toAlgHom.toRingHom =
        (O.comap (levelAutBar q M' ζ δ).toAlgHom.toRingHom).comap (levelAutBar q M' ζ b).toAlgHom.toRingHom := by
      ext x; simp [ValuationSubring.mem_comap]
    rw [this, h, hK1]

  have ha : (q : ℤ) ∣ ((b * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have h1 : ((((b * δ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 : ℤ) : ZMod q) =
        ((Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) (b * δ) : SL(2, ZMod q)) :
          Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 := by
      rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, eq_intCast]
    rw [h1, map_mul, hbred, ← hg, Matrix.SpecialLinearGroup.coe_mul]
    simp [W1a.Lift.Tq, Matrix.mul_apply, Fin.sum_univ_two]
    field_simp
    ring
  exact comap_levelAutBar_ne_of_dvd q hq M' hqM' A hA ζ O hO (b * δ) (Subgroup.mul_mem _ hb hδ) ha hstab

end

end S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq
end P2MW
export P2MW.S_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq (solution)
