-- Prove2me | solution 1 for ModularCurve.FullLevel.comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/ad096a0d-a462-55a3-85cc-e26843724506

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_FullLevelSemistableCovering
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_FullLevel_comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Theorems.Thm_ModularCurve_comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply
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

open scoped MatrixGroups
p2m_open "ModularCurve~coeffMap_qExpand~coeffMap_injective ModularCurve.FullLevel CongruenceSubgroup IsLocalRing"

namespace StabElem

variable (q : ℕ) [Fact q.Prime]

theorem coe_redQ_apply (δ : SL(2, ℤ)) (i j : Fin 2) :
    ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j = ((δ i j : ℤ) : ZMod q) := by
  simp [redQ, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]

theorem redQ_smul_lineInfty_eq_iff (δ : SL(2, ℤ)) :
    redQ q δ • lineInfty q = lineInfty q ↔ ((δ 1 0 : ℤ) : ZMod q) = 0 := by
  have hsm : (redQ q δ) • (![1, 0] : Fin 2 → ZMod q) = ![((δ 0 0 : ℤ) : ZMod q), ((δ 1 0 : ℤ) : ZMod q)] := by
    show ((redQ q δ : CuspidalType.GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) • (![1, 0] : Fin 2 → ZMod q) = _
    ext i
    rw [Matrix.smul_eq_mulVec]
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, coe_redQ_apply]
  rw [lineInfty, Projectivization.smul_mk, Projectivization.mk_eq_mk_iff]
  simp only [hsm]
  constructor
  · rintro ⟨a, ha⟩
    have := congr_fun ha 1
    simpa using this.symm
  · intro h
    have hdet : ((δ 0 0 : ℤ) : ZMod q) * ((δ 1 1 : ℤ) : ZMod q) = 1 := by
      have hd := Matrix.det_fin_two (δ : Matrix (Fin 2) (Fin 2) ℤ)
      rw [δ.prop] at hd
      have := congrArg (Int.cast : ℤ → ZMod q) hd
      push_cast at this
      rw [h, mul_zero, sub_zero] at this
      exact this.symm
    refine ⟨Units.mkOfMulEqOne _ _ hdet, ?_⟩
    ext i
    fin_cases i <;> simp [h, Units.smul_def]

theorem coeffMap_qExpand {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) :
    coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext n
  by_cases h : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := h
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

theorem coeffMap_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (coeffMap f : LaurentSeries R → LaurentSeries S) := fun x y h =>
  HahnSeries.ext (funext fun n => hf (by
    have := congrArg (fun z : LaurentSeries S => z.coeff n) h
    simpa using this))

end StabElem

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (L : Type) [Field L] [CharZero L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (hι : ∃ ι : L →+* ℂ, ι ζ = Complex.exp (2 * Real.pi * Complex.I / q))
    [Algebra.IsAlgebraic ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAq : (q : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ x : A, algebraMap A L x = ζ)
    (W₀ : ValuationSubring ↥K)
    (hW₀ : ∀ f : ↥K, f ∈ W₀ ↔ ∃ x y : PowerSeries A, y.map (IsLocalRing.residue A) ≠ 0 ∧
      (f : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)))
    (τ : SL(2, ℤ) → (↥K ≃ₐ[L] ↥K))
    (hτ : ∀ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma0 M' →
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') γ⁻¹ K (τ γ))

    (e : L →+* AlgebraicClosure ℚ)
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime q)
    (ζ' : ModularCurve.FullLevel.Idx q) (hζ' : ζ'.val = e ζ)
    (ιK : ↥K →+* ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hιK : ∀ x : ↥K, ((ιK x : ↥(ModularCurve.FullLevel.fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.coeffMap e (x : LaurentSeries L))
    (O : ValuationSubring ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hO : ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A', ModularCurve.coeffMap (IsLocalRing.residue ↥A') y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A'.subtype y = ModularCurve.coeffMap A'.subtype x)
    (hOW : ∀ f : ↥K, ιK f ∈ O ↔ f ∈ W₀)
    (hIT : ∀ ε : SL(2, ℤ), ε ∈ CongruenceSubgroup.Gamma0 M' → ∀ σ : ↥K ≃ₐ[L] ↥K,
      ModularCurve.FullLevel.IsLevelAutAt L q ζ q (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') ε K σ →
      ∀ x : ↥K, ιK (σ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x))
    (φ : ↥K ≃ₐ[L] ↥K) (ε : SL(2, ℤ)) (hε : ε ∈ CongruenceSubgroup.Gamma0 M')
    (hφ : ∀ x : ↥K, ιK (φ x) = ModularCurve.FullLevel.levelAutBar q M' ζ' ε (ιK x)) :
    W₀.comap φ.toAlgHom.toRingHom = W₀ ↔
      ModularCurve.FullLevel.redQ q ε • ModularCurve.FullLevel.lineInfty q = ModularCurve.FullLevel.lineInfty q := by
  classical
  haveI hqne : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  subst hK

  have fix : ∀ (ψ : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) ≃ₐ[L]
      ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M')))) (ρ : SL(2, ℤ)),
      ρ ∈ Gamma0 M' → (∀ x, ιK (ψ x) = levelAutBar q M' ζ' ρ (ιK x)) →
      redQ q ρ • lineInfty q = lineInfty q → W₀.comap ψ.toAlgHom.toRingHom = W₀ := by
    intro ψ ρ hρ hψ hfixρ
    have hO' := ModularCurve.FullLevel.comap_levelAutBar_eq_of_redQ_smul_lineInfty_eq
      q hq M' hqM' A' hA' ζ' O hO ρ hρ hfixρ
    ext f
    rw [ValuationSubring.mem_comap]
    change ψ f ∈ W₀ ↔ f ∈ W₀
    rw [← hOW (ψ f), ← hOW f, hψ f]
    conv_rhs => rw [← hO', ValuationSubring.mem_comap]
    rfl
  refine ⟨fun hW => ?_, fix φ ε hε hφ⟩
  by_contra hne

  have hc : ((ε 1 0 : ℤ) : ZMod q) ≠ 0 := fun h => hne ((StabElem.redQ_smul_lineInfty_eq_iff q ε).2 h)
  set a : ZMod q := ((ε 0 0 : ℤ) : ZMod q) with ha
  set c : ZMod q := ((ε 1 0 : ℤ) : ZMod q) with hcdef
  set xz : ℤ := (((-a * c⁻¹ : ZMod q).val : ℕ) : ℤ) with hxz
  have hxzq : ((xz : ℤ) : ZMod q) = -a * c⁻¹ := by
    rw [hxz, Int.cast_natCast, ZMod.natCast_zmod_val]
  let βM : Matrix (Fin 2) (Fin 2) ℤ := !![1, xz; 0, 1]
  have hβdet : βM.det = 1 := by simp [βM, Matrix.det_fin_two_of]
  let β : SL(2, ℤ) := ⟨βM, hβdet⟩
  have hβ10 : ((β 1 0 : ℤ) : ZMod q) = 0 := by
    show (((βM 1 0 : ℤ)) : ZMod q) = 0
    simp [βM]
  have hβ0 : β ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    show (((βM 1 0 : ℤ)) : ZMod M') = 0
    simp [βM]
  have hβfix : redQ q β • lineInfty q = lineInfty q := (StabElem.redQ_smul_lineInfty_eq_iff q β).2 hβ10
  have hprod : (q : ℤ) ∣ ((β * ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have hentry : ((β * ε : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = (ε 0 0 : ℤ) + xz * (ε 1 0 : ℤ) := by
      rw [Matrix.SpecialLinearGroup.coe_mul]
      show (βM * (ε : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 = _
      simp [βM, Matrix.mul_apply, Fin.sum_univ_two]
    rw [hentry]
    push_cast
    rw [hxzq, ← ha, ← hcdef]
    rw [mul_assoc, inv_mul_cancel₀ hc, mul_one, add_neg_cancel]

  have hτβ : IsLevelAutAt L q ζ q (q ^ 2 * M') (levelH q M') β
      (laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) (τ β⁻¹) := by
    have := hτ β⁻¹ (inv_mem hβ0)
    rwa [inv_inv] at this
  have hφβ : ∀ x, ιK (τ β⁻¹ x) = levelAutBar q M' ζ' β (ιK x) := hIT β hβ0 (τ β⁻¹) hτβ
  have hWβ : W₀.comap (τ β⁻¹).toAlgHom.toRingHom = W₀ := fix (τ β⁻¹) β hβ0 hφβ hβfix
  set χ := (τ β⁻¹).trans φ with hχdef
  have hχ : ∀ x, ιK (χ x) = levelAutBar q M' ζ' (β * ε) (ιK x) := by
    intro x
    rw [hχdef, AlgEquiv.trans_apply, hφ, hφβ,
      ModularCurve.FullLevel.levelAutBar_mul q M' hqM' ζ' β ε hβ0 hε, AlgEquiv.trans_apply]
  have e1 : ∀ g, φ g ∈ W₀ ↔ g ∈ W₀ := fun g => by
    have := SetLike.ext_iff.mp hW g
    rwa [ValuationSubring.mem_comap] at this
  have e2 : ∀ g, τ β⁻¹ g ∈ W₀ ↔ g ∈ W₀ := fun g => by
    have := SetLike.ext_iff.mp hWβ g
    rwa [ValuationSubring.mem_comap] at this
  have hWχ : W₀.comap χ.toAlgHom.toRingHom = W₀ := by
    ext f
    rw [ValuationSubring.mem_comap]
    change χ f ∈ W₀ ↔ f ∈ W₀
    rw [hχdef, AlgEquiv.trans_apply, e1, e2]

  have hjQ : jqModC ℚ ∈ xHFunctionField (q ^ 2 * M') (levelH q M') :=
    intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
  set jK : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M'))) :=
    ⟨coeffEmb L (jqModC ℚ), coeffEmb_mem_laurentBaseChange L hjQ⟩ with hjKdef
  have hjcoe : (jK : LaurentSeries L) = jqModC L := map_jqModC (algebraMap ℚ L)
  have hιKj : ((ιK jK : ↥(fieldBar q M')) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) := by
    rw [hιK, hjcoe]; exact map_jqModC e
  have hgmem : jqModC (AlgebraicClosure ℚ) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (Gamma0 M')) := by
    have h0 : jqModC ℚ ∈ qExpFunctionFieldC ℚ (Gamma0 M') :=
      intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)
    have h1 := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) h0
    have h2 : coeffEmb (AlgebraicClosure ℚ) (jqModC ℚ) = jqModC (AlgebraicClosure ℚ) := map_jqModC _
    rwa [h2] at h1
  have hLj := ModularCurve.FullLevel.coe_levelAutBar_apply_eq_qExpand_sq_of_dvd_of_mem_laurentBaseChange_gamma0
    q M' hqM' ζ' (β * ε) (mul_mem hβ0 hε) hprod (jqModC (AlgebraicClosure ℚ)) hgmem (ιK jK) hιKj
  have hχj : ((χ jK : ↥(laurentBaseChange L (xHFunctionField (q ^ 2 * M') (levelH q M')))) : LaurentSeries L) =
      qExpand L (q ^ 2) (jqModC L) := by
    apply StabElem.coeffMap_injective e e.injective
    rw [← hιK, hχ jK, hLj, StabElem.coeffMap_qExpand, ← hjcoe, ← hιK, hιKj]
  exact ModularCurve.comap_gauss_ne_of_coe_apply_eq_qExpand_sq_jqModC q L _ A hAq W₀ hW₀ χ jK hjcoe hχj hWχ

end S_ModularCurve_FullLevel_comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply
end P2MW
export P2MW.S_ModularCurve_FullLevel_comap_gauss_eq_iff_redQ_smul_lineInfty_eq_of_levelAutBar_apply (solution)
