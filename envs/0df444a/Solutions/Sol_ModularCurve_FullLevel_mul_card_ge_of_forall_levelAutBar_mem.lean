-- Prove2me | solution 1 for ModularCurve.FullLevel.mul_card_ge_of_forall_levelAutBar_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/8f7c1a63-bf84-5553-bfc1-7b69ba7c4d36

import Theorems.Thm_ModularCurve_FullLevel_exists_igusaValuationSubrings
import Theorems.Thm_ModularCurve_FullLevel_redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_CongruenceSubgroup_exists_mem_Gamma_map_eq_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.qExpandAlgHomC_apply CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg"
p2m_attr_erase "simp" "KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄"
p2m_attr_erase "simp" "TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel CongruenceSubgroup
open scoped MatrixGroups

namespace IgCount

theorem exists_mem_Gamma0_redQ_inv_smul_lineInfty_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (hqM' : ¬ q ∣ M') (ℓ : CuspidalType.ProjLine q) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' ∧
      (ModularCurve.FullLevel.redQ q γ)⁻¹ • ModularCurve.FullLevel.lineInfty q = ℓ := by
  have key : ∃ g : SL(2, ZMod q), (Matrix.SpecialLinearGroup.toGL g : CuspidalType.GL2 q) • ℓ =
      ModularCurve.FullLevel.lineInfty q := by
    induction ℓ using Projectivization.ind with
    | h v hv =>
      by_cases ha : v 0 = 0
      · have hb : v 1 ≠ 0 := by
          intro hb; apply hv; ext i; fin_cases i <;> simp [ha, hb]
        refine ⟨⟨!![0, (v 1)⁻¹; -(v 1), 0], by rw [Matrix.det_fin_two_of, zero_mul, mul_neg, zero_sub, neg_neg, inv_mul_cancel₀ hb]⟩, ?_⟩
        rw [Projectivization.smul_mk]
        show Projectivization.mk (ZMod q) (Matrix.mulVec !![0, (v 1)⁻¹; -(v 1), 0] v) _ = _
        congr 1
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, ha, hb, ModularCurve.FullLevel.lineInfty]
      · refine ⟨⟨!![(v 0)⁻¹, 0; -(v 1), v 0], by rw [Matrix.det_fin_two_of, zero_mul, sub_zero, inv_mul_cancel₀ ha]⟩, ?_⟩
        rw [Projectivization.smul_mk]
        show Projectivization.mk (ZMod q) (Matrix.mulVec !![(v 0)⁻¹, 0; -(v 1), v 0] v) _ = _
        congr 1
        ext i; fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.vecHead, Matrix.vecTail, ha, ModularCurve.FullLevel.lineInfty]; ring
  obtain ⟨g, hg⟩ := key
  obtain ⟨γ, hγ, hmap⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 g
  refine ⟨γ, ?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1
  · have : ModularCurve.FullLevel.redQ q γ = Matrix.SpecialLinearGroup.toGL g := by
      change Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q)) γ) = _
      rw [hmap]
    rw [this, inv_smul_eq_iff, hg]

theorem eq_one_or_eq_neg_one_of_forall_smul_eq (q : ℕ) [Fact q.Prime] (g : SL(2, ZMod q))
    (h : ∀ ℓ : CuspidalType.ProjLine q, (Matrix.SpecialLinearGroup.toGL g : CuspidalType.GL2 q) • ℓ = ℓ) :
    g = 1 ∨ g = -1 := by

  have hline : ∀ (v : Fin 2 → ZMod q) (hv : v ≠ 0), ∃ a : ZMod q, a • v = Matrix.mulVec (g : Matrix (Fin 2) (Fin 2) (ZMod q)) v := by
    intro v hv
    have h1 := h (Projectivization.mk (ZMod q) v hv)
    rw [Projectivization.smul_mk, Projectivization.mk_eq_mk_iff'] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩
  have e0 : (![1, 0] : Fin 2 → ZMod q) ≠ 0 := by intro h0; have := congr_fun h0 0; simp at this
  have e1 : (![0, 1] : Fin 2 → ZMod q) ≠ 0 := by intro h0; have := congr_fun h0 1; simp at this
  have e2 : (![1, 1] : Fin 2 → ZMod q) ≠ 0 := by intro h0; have := congr_fun h0 0; simp at this
  obtain ⟨a0, ha0⟩ := hline _ e0
  obtain ⟨a1, ha1⟩ := hline _ e1
  obtain ⟨a2, ha2⟩ := hline _ e2
  have h00 := congr_fun ha0 0; have h10 := congr_fun ha0 1
  have h01 := congr_fun ha1 0; have h11 := congr_fun ha1 1
  have h02 := congr_fun ha2 0; have h12 := congr_fun ha2 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h00 h10 h01 h11 h02 h12

  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod q)).det = 1 := g.det_coe
  rw [Matrix.det_fin_two] at hdet
  have hc : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 0 = 0 := h10.symm
  have hb : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 1 = 0 := h01.symm
  have had : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 := by
    rw [hb, add_zero] at h02; rw [hc, zero_add] at h12; rw [← h02, ← h12]
  rw [hb, hc, mul_zero, sub_zero, ← had] at hdet
  have h11 : (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 1 1 = (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0 := had.symm
  rcases mul_self_eq_one_iff.mp hdet with h1 | h1
  · left; apply Matrix.SpecialLinearGroup.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, hb, hc, h11]
  · right; apply Matrix.SpecialLinearGroup.ext; intro i j
    fin_cases i <;> fin_cases j <;> simp [h1, hb, hc, h11]

theorem natCard_SL2 (q : ℕ) [hq : Fact q.Prime] : Nat.card (SL(2, ZMod q)) = q * (q ^ 2 - 1) := by
  have hq' : q.Prime := hq.out

  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) = (q ^ 2 - 1) * (q ^ 2 - q) := by
    rw [Matrix.card_GL_field, Fin.prod_univ_two, ZMod.card]
    simp

  set det := (Matrix.GeneralLinearGroup.det : Matrix.GeneralLinearGroup (Fin 2) (ZMod q) →* (ZMod q)ˣ) with hdet
  have hsurj : Function.Surjective det := by
    intro u
    refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero !![(u : ZMod q), 0; 0, 1] (by rw [Matrix.det_fin_two_of]; simp [u.ne_zero]), ?_⟩
    apply Units.ext
    show Matrix.det !![(u : ZMod q), 0; 0, 1] = (u : ZMod q)
    rw [Matrix.det_fin_two_of]; simp
  have hker : Nat.card ↥det.ker = Nat.card (SL(2, ZMod q)) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨((x : Matrix.GeneralLinearGroup (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)), ?_⟩
        invFun := fun g => ⟨Matrix.SpecialLinearGroup.toGL g, ?_⟩
        left_inv := fun x => Subtype.ext (Units.ext rfl)
        right_inv := fun g => Subtype.ext rfl }
    · have hx := x.2
      rw [MonoidHom.mem_ker] at hx
      exact congrArg Units.val hx
    · rw [MonoidHom.mem_ker]; exact Units.ext g.det_coe
  have hidx : det.ker.index = q - 1 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have hmul := Subgroup.card_mul_index det.ker
  rw [hker, hidx, hGL] at hmul

  have hpos : 0 < q - 1 := by have := hq'.two_le; omega
  have h2 : (q ^ 2 - 1) * (q ^ 2 - q) = q * (q ^ 2 - 1) * (q - 1) := by
    have h1 : q ^ 2 - q = q * (q - 1) := by
      rw [Nat.mul_sub_one, pow_two]
    rw [h1]; ring
  rw [h2] at hmul
  exact Nat.eq_of_mul_eq_mul_right hpos hmul

end IgCount

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : Idx q)
    (G : Subgroup (fieldBar q M' ≃ₐ[AlgebraicClosure ℚ] fieldBar q M')) [Finite ↥G]
    (hG : ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M' → levelAutBar q M' ζ γ ∈ G) :
    q * (q ^ 2 - 1) ≤ 2 * Nat.card ↥G := by
  classical
  have hq' : q.Prime := Fact.out

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨q, hq'⟩
  obtain ⟨OIg, R, -, hpres, -⟩ := exists_igusaValuationSubrings q hq M' hqM' A hA ζ

  let ρ : ↥(Gamma0 M') →* ↥G := MonoidHom.mk' (fun γ => ⟨levelAutBar q M' ζ (γ : SL(2, ℤ))⁻¹, hG _ (inv_mem γ.2)⟩)
    (by
      intro α β
      apply Subtype.ext
      show levelAutBar q M' ζ ((α : SL(2, ℤ)) * β)⁻¹ = levelAutBar q M' ζ (α : SL(2, ℤ))⁻¹ * levelAutBar q M' ζ (β : SL(2, ℤ))⁻¹
      rw [mul_inv_rev, levelAutBar_mul q M' hqM' ζ _ _ (inv_mem β.2) (inv_mem α.2)]
      rfl)
  have hρ : ∀ γ : ↥(Gamma0 M'), ((ρ γ : ↥G) : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M')) =
      levelAutBar q M' ζ (γ : SL(2, ℤ))⁻¹ := fun _ => rfl

  let σ : ↥(Gamma0 M') →* SL(2, ZMod q) :=
    (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod q))).comp (Gamma0 M').subtype
  have hσ : ∀ γ : ↥(Gamma0 M'), redQ q (γ : SL(2, ℤ)) = Matrix.SpecialLinearGroup.toGL (σ γ) := fun _ => rfl
  have hσsurj : Function.Surjective σ := by
    intro g
    obtain ⟨γ, hγ, hmap⟩ := (CongruenceSubgroup.exists_mem_Gamma_map_eq_of_not_dvd M' q hqM').1 g
    refine ⟨⟨γ, ?_⟩, hmap⟩
    rw [CongruenceSubgroup.Gamma0_mem]
    exact (CongruenceSubgroup.Gamma_mem.mp hγ).2.2.1

  let Z : Subgroup (SL(2, ZMod q)) := Subgroup.zpowers (-1)
  have hneg : (-1 : SL(2, ZMod q)) ≠ 1 := by
    haveI : Fact (2 < q) := ⟨by omega⟩
    intro h
    have h1 := congrArg (fun g : SL(2, ZMod q) => (g : Matrix (Fin 2) (Fin 2) (ZMod q)) 0 0) h
    simp at h1
    exact ZMod.neg_one_ne_one h1
  have hZcard : Nat.card ↥Z = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_zpowers]
    exact (orderOf_eq_prime_iff (p := 2)).2 ⟨by simp, hneg⟩
  let K : Subgroup ↥(Gamma0 M') := Z.comap σ

  have hkerK : ρ.ker ≤ K := by
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ

    have hfix : ∀ ℓ : CuspidalType.ProjLine q, Matrix.SpecialLinearGroup.toGL (σ γ) • ℓ = ℓ := by
      intro ℓ
      obtain ⟨δ, hδ, hδℓ⟩ := IgCount.exists_mem_Gamma0_redQ_inv_smul_lineInfty_eq q M' hqM' ℓ
      have htriv : ρ (⟨δ, hδ⟩ * γ * ⟨δ, hδ⟩⁻¹) = 1 := by rw [map_mul, map_mul, hγ, mul_one, map_inv, mul_inv_cancel]
      have htriv' : levelAutBar q M' ζ (δ * (γ : SL(2, ℤ))⁻¹ * δ⁻¹) = 1 := by
        have := congrArg (fun x : ↥G => (x : ↥(fieldBar q M') ≃ₐ[AlgebraicClosure ℚ] ↥(fieldBar q M'))) htriv
        simp only [hρ] at this
        rw [show ((⟨δ, hδ⟩ * γ * ⟨δ, hδ⟩⁻¹ : ↥(Gamma0 M')) : SL(2, ℤ))⁻¹ = δ * (γ : SL(2, ℤ))⁻¹ * δ⁻¹ by
          simp [mul_inv_rev, mul_assoc]] at this
        exact this
      have hmem : δ * (γ : SL(2, ℤ))⁻¹ * δ⁻¹ ∈ Gamma0 M' := mul_mem (mul_mem hδ (inv_mem γ.2)) (inv_mem hδ)
      have hcomap : (OIg (lineInfty q)).comap (levelAutBar q M' ζ (δ * (γ : SL(2, ℤ))⁻¹ * δ⁻¹)).toAlgHom.toRingHom =
          OIg (lineInfty q) := by
        rw [htriv']; ext f; simp [ValuationSubring.mem_comap]
      have h9 := redQ_smul_lineInfty_eq_of_comap_levelAutBar_eq q hq M' hqM' A hA ζ (OIg (lineInfty q)) hpres _ hmem hcomap
      rw [map_mul, map_mul, map_inv, map_inv, mul_smul, mul_smul, smul_eq_iff_eq_inv_smul, hδℓ, inv_smul_eq_iff] at h9
      rw [← hσ]
      exact h9.symm
    have hpm := IgCount.eq_one_or_eq_neg_one_of_forall_smul_eq q (σ γ) hfix
    show σ γ ∈ Z
    rcases hpm with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact Subgroup.mem_zpowers _

  have hK : K.index = Z.index := Subgroup.index_comap_of_surjective Z hσsurj
  have hZ : Z.index * 2 = q * (q ^ 2 - 1) := by
    have := Subgroup.index_mul_card Z
    rw [hZcard, IgCount.natCard_SL2] at this
    exact this
  have hrange : ρ.ker.index = Nat.card ↥ρ.range := Subgroup.index_ker ρ
  have hfin : ρ.ker.index ≠ 0 := by
    rw [hrange]; exact Nat.card_pos.ne'
  have hle1 : K.index ≤ ρ.ker.index := Nat.le_of_dvd (Nat.pos_of_ne_zero hfin) (Subgroup.index_dvd_of_le hkerK)
  have hle2 : Nat.card ↥ρ.range ≤ Nat.card ↥G := Subgroup.card_le_card_group ρ.range
  calc q * (q ^ 2 - 1) = Z.index * 2 := hZ.symm
    _ = 2 * K.index := by rw [hK, mul_comm]
    _ ≤ 2 * ρ.ker.index := Nat.mul_le_mul_left 2 hle1
    _ = 2 * Nat.card ↥ρ.range := by rw [hrange]
    _ ≤ 2 * Nat.card ↥G := Nat.mul_le_mul_left 2 hle2

end S_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_mul_card_ge_of_forall_levelAutBar_mem (solution)
