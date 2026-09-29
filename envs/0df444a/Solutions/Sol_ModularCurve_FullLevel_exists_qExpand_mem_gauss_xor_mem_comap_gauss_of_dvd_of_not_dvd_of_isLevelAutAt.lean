-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/11f6e9d9-b351-5eea-8914-d744ed8045f8

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Definitions.Def_ModularCurve_KroneckerTransport
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FrobeniusModL
import Theorems.Thm_ModularCurve_FullLevel_exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap
import Theorems.Thm_ModularCurve_qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_exists_qExpand_jqInt_sub_pow_eq_natCast_mul
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_IsLocalRing_charP_residueField_of_natCast_mem_maximalIdeal
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd
import Theorems.Thm_ModularCurve_FullLevel_exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
import Theorems.Thm_ModularCurve_FullLevel_levelAutBar_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt
p2m_attr_erase "instance" "ModularCurve.FullLevel.SemistableCovering.instAlgebraSS ModularCurve.FullLevel.SemistableCovering.instFieldIg ModularCurve.FullLevel.SemistableCovering.instFieldSS ModularCurve.FullLevel.SemistableCovering.instAlgebraIg AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine"
p2m_attr_erase "instance" "ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "instance" "CuspForm.instModuleZModIntTwoCuspForms CuspForm.instAddCommGroupIntTwoCuspForms ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent CuspForm.instModuleTwoCuspForms CuspForm.instIsScalarTowerTwoCuspForms CuspForm.instAddCommGroupTwoCuspForms CuspForm.instIsScalarTowerSelfTwoCuspForms CuspForm.instModuleQuotientTwoCuspForms CuspForm.GammaH_finiteIndex"
p2m_attr_erase "simp" "ModularCurve.FullLevel.SemistableCovering.mk.sizeOf_spec ModularCurve.FullLevel.SemistableCovering.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_integers AlgebraicCurve.ComponentChart.mk.sizeOf_spec AlgebraicCurve.ComponentChart.ofConstantReduction_placeMap AlgebraicCurve.ComponentChart.ofConstantReduction_nodes AlgebraicCurve.ComponentChart.mk.injEq AlgebraicCurve.ComponentChart.ofConstantReduction_dom AlgebraicCurve.Annulus.mk.sizeOf_spec AlgebraicCurve.Annulus.mk.injEq ModularCurve.FinitePlaceLift.traceHom_coe ModularCurve.FinitePlaceLift.mk.injEq ModularCurve.FinitePlaceLift.mk.sizeOf_spec WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.JZeroSemistableSpecialization.mk.sizeOf_spec ModularCurve.JZeroSemistableSpecialization.mk.injEq AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.coe_admissibleMap AlgebraicCurve.SemilinearAut.gluingMap_apply AlgebraicCurve.GluedPic0.glueMap_mk AlgebraicCurve.SemilinearAut.nodePerm_apply AlgebraicCurve.SemilinearAut.baseAutUnitsHom_apply ModularCurve.widthPairing_apply ModularCurve.gramMap_apply ModularCurve.degreeOn_apply AlgebraicCurve.ComponentChart.comap_placeMap AlgebraicCurve.ComponentChart.comap_residue_apply AlgebraicCurve.ComponentChart.coe_comapIntegersEquiv AlgebraicCurve.ComponentChart.comapResidue_apply AlgebraicCurve.ComponentChart.comap_integers AlgebraicCurve.ComponentChart.comap_dom AlgebraicCurve.ComponentChart.mem_comapIntegers AlgebraicCurve.Annulus.comap_param AlgebraicCurve.Annulus.comap_dom AlgebraicCurve.Annulus.comap_modulus AlgebraicCurve.ComponentChart.mem_comap_integers AlgebraicCurve.ComponentChart.comap_nodes AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe"
p2m_attr_erase "simp" "AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk"
p2m_attr_erase "simp" "ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.coe_heckeBetaModLHOf ModularCurve.pairDiagModL_apply ModularCurve.coe_heckeAlphaModLH ModularCurve.pairUpModL_apply ModularCurve.coeff_qDecimate ModularCurve.coe_qExpFrobeniusModL ModularCurve.coe_qExpFrobeniusDegZeroPullbackModL ModularCurve.coe_qExpFrobeniusDegZeroPushforwardModL ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.gluedPolarDifferentials.coe_fst_apply AlgebraicCurve.gluedPolarDifferentials.coe_snd_apply CuspForm.heckeGenH_T CuspForm.coe_twoCuspEnd_apply CuspForm.twoCuspEndMod_reduce CuspForm.heckeGenH_U CuspForm.heckeGenH_dia ModularForm.AtkinLehnerDatum.mk.injEq ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open scoped MatrixGroups

namespace N1Beta

p2m_open "ModularCurve~coeffMap_injective ModularCurve.FullLevel CongruenceSubgroup"
open scoped MatrixGroups

theorem sigma (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M') (ζ : ModularCurve.FullLevel.Idx q)
    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M') (hc : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) = ζ.val)
    (X₀ X₁ X₂ : ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hX₀ : (X₀ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ))
    (hX₁ : (X₁ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.qExpand (AlgebraicClosure ℚ) q (ModularCurve.jqModC (AlgebraicClosure ℚ)))
    (hX₂ : (X₂ : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.qExpand (AlgebraicClosure ℚ) (q ^ 2) (ModularCurve.jqModC (AlgebraicClosure ℚ)))
    (hJ : ModularCurve.jqModC (AlgebraicClosure ℚ) ∈
      ModularCurve.laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M'))) :
    ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹ X₁ = X₁ ∧
    ∃ k : ℤ, ((ModularCurve.FullLevel.levelAutBar q M' ζ γ⁻¹ X₂ : ↥(ModularCurve.FullLevel.fieldBar q M')) :
        LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qTwist (u ^ k) (ModularCurve.jqModC (AlgebraicClosure ℚ)) := by
  have hγ' : γ⁻¹ ∈ Gamma0 M' := inv_mem hγ
  refine ⟨levelAutBar_apply_eq_self_of_coe_eq_qExpand_of_mem_laurentBaseChange_gamma0 q M' hqM' ζ γ⁻¹ hγ' _ hJ X₁ hX₁, ?_⟩

  have hcop : IsCoprime (q : ℤ) (M' : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (((Fact.out : q.Prime).coprime_iff_not_dvd).mpr hqM')
  obtain ⟨t, v, htv⟩ := hcop

  let w : SL(2, ℤ) := ⟨!![(q : ℤ), -v; (M' : ℤ), t], by
    rw [Matrix.det_fin_two_of]; linear_combination htv⟩
  have hw10 : (w : Matrix (Fin 2) (Fin 2) ℤ) 1 0 = M' := rfl
  have hw00 : (w : Matrix (Fin 2) (Fin 2) ℤ) 0 0 = q := rfl
  have hw01 : (w : Matrix (Fin 2) (Fin 2) ℤ) 0 1 = -v := rfl
  have hw : w ∈ Gamma0 M' := by
    rw [Gamma0_mem]
    show (((w : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod M') = 0
    rw [hw10, Int.cast_natCast, ZMod.natCast_self]
  have hwq : (q : ℤ) ∣ (w : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by rw [hw00]

  have hwX₀ : levelAutBar q M' ζ w X₀ = X₂ := Subtype.ext (by
    rw [coe_levelAutBar_apply_eq_qExpand_sq_jqModC_of_dvd q M' hqM' ζ w hw hwq X₀ hX₀, hX₂])
  have hmul : levelAutBar q M' ζ γ⁻¹ X₂ = levelAutBar q M' ζ (w * γ⁻¹) X₀ := by
    rw [← hwX₀, levelAutBar_mul q M' hqM' ζ w γ⁻¹ hw hγ', AlgEquiv.trans_apply]

  have h00 : ((w * γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 =
      q * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 + v * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, hw00, hw01]
    simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, Matrix.empty_val']
    ring
  have hp : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp Fact.out
  have ha : ¬ (q : ℤ) ∣ ((w * γ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) 0 0 := by
    rw [h00]
    intro hd
    have hd' : (q : ℤ) ∣ v * (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by
      have h3 := dvd_sub hd (dvd_mul_right (q : ℤ) ((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1))
      rwa [add_sub_cancel_left] at h3
    rcases hp.dvd_or_dvd hd' with hv | h10
    · apply hp.not_unit
      rw [isUnit_iff_dvd_one, ← htv]
      exact dvd_add (dvd_mul_left _ _) (dvd_mul_of_dvd_left hv _)
    · exact hc h10
  obtain ⟨k, hk⟩ := exists_coe_levelAutBar_apply_eq_qTwist_of_not_dvd_of_mem_laurentBaseChange_gamma0
    q M' hqM' ζ (w * γ⁻¹) (mul_mem hw hγ') ha u hu
  exact ⟨k, by rw [hmul]; exact hk _ hJ X₀ hX₀⟩

end N1Beta

namespace N1Beta

p2m_open "ModularCurve~coeffMap_injective"

theorem coeffMap_qTwist {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (v : Rˣ)
    (x : LaurentSeries R) :
    coeffMap f (qTwist v x) = qTwist (Units.map (f : R →* S) v) (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff, qTwist_coeff, qTwist_coeff, map_mul, coeffMap_coeff, ← map_zpow (Units.map (f : R →* S)) v n,
    Units.coe_map]
  rfl

theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk, map_zero]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Injective f) : Function.Injective (coeffMap f) := by
  intro x y h
  ext k
  apply hf
  rw [← coeffMap_coeff, ← coeffMap_coeff, h]

theorem eq_one_of_pow_char_eq_one {κ : Type*} [Field κ] (q : ℕ) [Fact q.Prime] [CharP κ q]
    (x : κ) (hx : x ^ q = 1) : x = 1 := by
  have h : (x - 1) ^ q = 0 := by rw [sub_pow_char, hx, one_pow, sub_self]
  exact sub_eq_zero.mp (pow_eq_zero_iff (Fact.out : q.Prime).ne_zero |>.mp h)

set_option maxHeartbeats 3200000 in

theorem not_mem_of_natCast_mul_eq (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A' : ValuationSubring (AlgebraicClosure ℚ)) (hA' : A'.LiesOverPrime q)
    (O : ValuationSubring ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hO : ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A', ModularCurve.coeffMap (IsLocalRing.residue ↥A') y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A'.subtype y = ModularCurve.coeffMap A'.subtype x)
    (u : (AlgebraicClosure ℚ)ˣ) (hu : (u : AlgebraicClosure ℚ) ^ q = 1) (k : ℤ)
    (y : ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hy : (q : LaurentSeries (AlgebraicClosure ℚ)) * (y : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qTwist (u ^ k) (ModularCurve.jqModC (AlgebraicClosure ℚ)) -
        (ModularCurve.qExpand (AlgebraicClosure ℚ) q (ModularCurve.jqModC (AlgebraicClosure ℚ))) ^ q) :
    y ∉ O := by
  classical
  intro hyO
  obtain ⟨X, Y, hY, hXY⟩ := (hO y).mp hyO
  have hq0 : (Fact.out : q.Prime).ne_zero = (Fact.out : q.Prime).ne_zero := rfl

  have hqm : ((q : ↥A') : ↥A') ∈ IsLocalRing.maximalIdeal ↥A' := by
    rw [← ValuationSubring.coe_mem_nonunits_iff]; push_cast; exact hA'
  haveI : CharP (IsLocalRing.ResidueField ↥A') q :=
    IsLocalRing.charP_residueField_of_natCast_mem_maximalIdeal ↥A' q hqm

  have hmemA : ∀ z : AlgebraicClosure ℚ, z ^ q = 1 → z ∈ A' := by
    intro z hz
    rw [← A'.valuation_le_one_iff]
    by_contra hlt
    rw [not_le] at hlt
    have h1 : A'.valuation (z ^ q) = 1 := by rw [hz, map_one]
    rw [map_pow] at h1
    exact absurd h1 (ne_of_gt (one_lt_pow₀ hlt (Fact.out : q.Prime).ne_zero))
  have huA : (u : AlgebraicClosure ℚ) ∈ A' := hmemA _ hu
  have huinvA : ((u⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A' :=
    hmemA _ (by rw [Units.val_inv_eq_inv_val, inv_pow, hu, inv_one])
  let u₀ : (↥A')ˣ := ⟨⟨u, huA⟩, ⟨_, huinvA⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  have hu₀ : Units.map (A'.subtype : ↥A' →* AlgebraicClosure ℚ) u₀ = u := Units.ext rfl

  set J₀ : LaurentSeries ↥A' := jqModC ↥A' with hJ₀
  set N₀ : LaurentSeries ↥A' := qTwist (u₀ ^ k) J₀ - (qExpand ↥A' q J₀) ^ q with hN₀
  have hN₀c : coeffMap A'.subtype N₀ = qTwist (u ^ k) (jqModC (AlgebraicClosure ℚ)) -
      (qExpand (AlgebraicClosure ℚ) q (jqModC (AlgebraicClosure ℚ))) ^ q := by
    rw [hN₀, map_sub, map_pow, coeffMap_qTwist, coeffMap_qExpand', hJ₀, coeffMap_jqModC, map_zpow, hu₀]

  have heq : N₀ * Y = (q : LaurentSeries ↥A') * X := by
    apply coeffMap_injective A'.subtype Subtype.val_injective
    rw [map_mul, map_mul, map_natCast, hN₀c, ← hy, mul_assoc, hXY]

  set red := coeffMap (IsLocalRing.residue ↥A') with hred
  have hredq : red (q : LaurentSeries ↥A') = 0 := by
    rw [map_natCast, ← map_natCast (HahnSeries.C (Γ := ℤ) (R := IsLocalRing.ResidueField ↥A')), CharP.cast_eq_zero, map_zero]
  have hzero : red N₀ * red Y = 0 := by rw [← map_mul, heq, map_mul, hredq, zero_mul]
  have hN₀red : red N₀ ≠ 0 := by

    have hbar : Units.map (IsLocalRing.residue ↥A' : ↥A' →* IsLocalRing.ResidueField ↥A') u₀ = 1 := by
      apply Units.ext
      apply eq_one_of_pow_char_eq_one q
      rw [Units.coe_map, MonoidHom.coe_coe, ← map_pow]
      have : ((u₀ : ↥A') : ↥A') ^ q = 1 := Subtype.ext (by push_cast; exact hu)
      rw [this, map_one]
    have hform : red N₀ = jqModC (IsLocalRing.ResidueField ↥A') -
        qExpand (IsLocalRing.ResidueField ↥A') q (qExpand (IsLocalRing.ResidueField ↥A') q (jqModC (IsLocalRing.ResidueField ↥A'))) := by
      rw [hred, hN₀, map_sub, map_pow, coeffMap_qTwist, coeffMap_qExpand', hJ₀, coeffMap_jqModC, map_zpow, hbar,
        one_zpow, qTwist_one_apply, ← qExpand_ell_qExpand_jqModC_eq_pow]
    intro h0
    have h1 := congrArg (fun s : LaurentSeries (IsLocalRing.ResidueField ↥A') => s.coeff (-1)) hform
    have hndvd : ¬ ((q : ℤ) ∣ (-1 : ℤ)) := by
      intro hd
      have := Int.le_of_dvd one_pos ((Int.dvd_neg).mp hd)
      have hq2 := (Fact.out : q.Prime).two_le
      omega
    simp only [h0, HahnSeries.coeff_zero, HahnSeries.coeff_sub, coeff_jqModC_neg_one,
      qExpand_coeff_of_not_dvd q _ hndvd, sub_zero] at h1
    exact zero_ne_one h1
  exact (mul_ne_zero hN₀red hY) hzero

end N1Beta

namespace N1Beta

p2m_open "ModularCurve~coeffMap_injective ModularCurve.FullLevel HahnSeries IsLocalRing"

end N1Beta

namespace N1Beta

p2m_open "ModularCurve~coeffMap_injective ModularCurve.FullLevel"

theorem coeffMap_eq_laurentMap {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (z : LaurentSeries R) :
    ModularCurve.coeffMap f z = ModularCurve.laurentMap f z := rfl

theorem mem_of_coe_eq_qExpand_laurentMap (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (A' : ValuationSubring (AlgebraicClosure ℚ))
    (O : ValuationSubring ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hO : ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), f ∈ O ↔
      ∃ x y : LaurentSeries ↥A', ModularCurve.coeffMap (IsLocalRing.residue ↥A') y ≠ 0 ∧
        (f : LaurentSeries (AlgebraicClosure ℚ)) * ModularCurve.coeffMap A'.subtype y = ModularCurve.coeffMap A'.subtype x)
    (S : LaurentSeries ℤ) (y : ↥(ModularCurve.FullLevel.fieldBar q M'))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) =
      ModularCurve.qExpand (AlgebraicClosure ℚ) q (ModularCurve.laurentMap (Int.castRingHom (AlgebraicClosure ℚ)) S)) :
    y ∈ O := by
  rw [hO]
  refine ⟨ModularCurve.qExpand (↥A') q (ModularCurve.laurentMap (Int.castRingHom ↥A') S), 1, ?_, ?_⟩
  · rw [map_one]; exact one_ne_zero
  · rw [map_one, mul_one, hy, coeffMap_eq_laurentMap, laurentMap_qExpand, laurentMap_laurentMap]
    congr 2

end N1Beta

p2m_open "ModularCurve~coeffMap_injective" in open N1Beta ModularCurve.FullLevel HahnSeries IsLocalRing in
set_option maxHeartbeats 6400000 in

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

    (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma0 M')
    (hb : (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 0 1) (hc : ¬ (q : ℤ) ∣ (γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0) :
    ∃ (g : LaurentSeries L) (x : ↥K),
      g ∈ ModularCurve.laurentBaseChange L (ModularCurve.qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) ∧
      (x : LaurentSeries L) = ModularCurve.qExpand L q g ∧
      ¬ (x ∈ W₀.comap (τ γ).toAlgHom.toRingHom ↔ x ∈ W₀) := by
  classical
  set Qb := AlgebraicClosure ℚ with hQb
  have hq0 : 0 < q := (Fact.out : q.Prime).pos
  haveI : NeZero q := ⟨hq0.ne'⟩

  obtain ⟨S, hS⟩ := ModularCurve.exists_qExpand_jqInt_sub_pow_eq_natCast_mul q
  set Gℚ : LaurentSeries ℚ := laurentMap (Int.castRingHom ℚ) S with hGℚ
  have hGℚq : (q : LaurentSeries ℚ) * Gℚ = qExpand ℚ q jq - jq ^ q := by
    have := congrArg (laurentMap (Int.castRingHom ℚ)) hS
    rw [map_sub, map_pow, laurentMap_qExpand, laurentMap_jqInt, map_mul, map_natCast] at this
    rw [hGℚ, ← this]
  have hCnat : ∀ (R : Type) [CommRing R], ((q : ℕ) : LaurentSeries R) = HahnSeries.C (q : R) := fun R _ =>
    (map_natCast (HahnSeries.C : R →+* LaurentSeries R) q).symm
  have hqℚ : (q : LaurentSeries ℚ) ≠ 0 := by
    rw [hCnat]; exact HahnSeries.C_ne_zero (by exact_mod_cast hq0.ne')
  have hGℚmem : Gℚ ∈ modularFunctionFieldFull q := by
    have h1 : jq ∈ modularFunctionFieldFull q := by
      have := jqd_mem_full q (d := 1) (one_dvd q); rwa [qExpand_one_apply] at this
    have h2 : qExpand ℚ q jq ∈ modularFunctionFieldFull q := jqd_mem_full q dvd_rfl
    have hq' : (q : LaurentSeries ℚ) ∈ modularFunctionFieldFull q := by
      have : (q : LaurentSeries ℚ) = algebraMap ℚ (LaurentSeries ℚ) (q : ℚ) := by rw [map_natCast]
      rw [this]; exact (modularFunctionFieldFull q).algebraMap_mem _
    have : Gℚ = (q : LaurentSeries ℚ)⁻¹ * (qExpand ℚ q jq - jq ^ q) := by
      rw [← hGℚq, ← mul_assoc, inv_mul_cancel₀ hqℚ, one_mul]
    rw [this]
    exact mul_mem (inv_mem hq') (sub_mem h2 (pow_mem h1 q))

  refine ⟨coeffEmb L Gℚ, ?_⟩
  have hgmem : coeffEmb L Gℚ ∈ laurentBaseChange L (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M'))) := by
    apply coeffEmb_mem_laurentBaseChange
    have hle : qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 q) ≤ qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 (q * M')) :=
      qExpFunctionFieldC_mono ℚ (fun δ hδ => by
        rw [CongruenceSubgroup.Gamma0_mem] at hδ ⊢
        rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hδ ⊢
        exact (Int.natCast_dvd_natCast.mpr (Nat.dvd_mul_right q M')).trans hδ)
    apply hle
    rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    exact hGℚmem
  have hxK : qExpand L q (coeffEmb L Gℚ) ∈ K := by
    rw [hK]
    exact qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull L q q (q ^ 2 * M')
      (by rw [pow_two]; exact Nat.dvd_mul_right _ _) _ Gℚ hGℚmem
  refine ⟨⟨_, hxK⟩, hgmem, rfl, ?_⟩
  set x : ↥K := ⟨_, hxK⟩ with hxdef

  obtain ⟨e, A', hA'q, ζ', ιK, O, hζ', hιK, hO, hOW⟩ :=
    exists_ringHom_fieldBar_comap_gauss_iff_of_isAlgebraic q hq M' hqM' L ζ hζ hι K hK A hAq hζA W₀ hW₀
  have hγinv : γ⁻¹ ∈ CongruenceSubgroup.Gamma0 M' := inv_mem hγ
  have hint : ιK ((τ γ) x) = levelAutBar q M' ζ' γ⁻¹ (ιK x) :=
    levelAutBar_apply_eq_of_isLevelAutAt_of_coe_eq_coeffMap q hq M' hqM' L ζ hζ hι K hK e ζ' hζ' ιK hιK γ⁻¹ hγinv (τ γ)
      (hτ γ hγ) x

  have heℚ : e.comp (algebraMap ℚ L) = algebraMap ℚ Qb := Subsingleton.elim _ _
  have hcoeffEmb : ∀ z : LaurentSeries ℚ, coeffMap e (coeffEmb L z) = coeffEmb Qb z := fun z => by
    rw [coeffEmb, coeffEmb, coeffMap_coeffMap, heℚ]
  have hJbar : coeffEmb Qb jq = jqModC Qb := by
    rw [coeffEmb, ← jqModC_rat]; exact map_jqModC _
  set Gb : LaurentSeries Qb := coeffEmb Qb Gℚ with hGb
  have hGbq : (q : LaurentSeries Qb) * Gb = qExpand Qb q (jqModC Qb) - (jqModC Qb) ^ q := by
    have := congrArg (coeffEmb Qb) hGℚq
    rw [map_mul, map_natCast, map_sub, map_pow, coeffEmb, coeffMap_qExpand, ← coeffEmb, hJbar] at this
    rw [hGb, this]
  have hιKx : ((ιK x : ↥(fieldBar q M')) : LaurentSeries Qb) = qExpand Qb q Gb := by
    rw [hιK, hxdef]
    show coeffMap e (qExpand L q (coeffEmb L Gℚ)) = _
    rw [coeffMap_qExpand, hcoeffEmb]

  have hjfull : jq ∈ modularFunctionFieldFull 1 := by
    have := jqd_mem_full 1 (d := 1) (one_dvd 1); rwa [qExpand_one_apply] at this
  have hmemF : ∀ (d : ℕ) [NeZero d], d ∣ q ^ 2 → qExpand Qb d (jqModC Qb) ∈ fieldBar q M' := by
    intro d _ hd
    rw [← hJbar]
    exact qExpand_coeffEmb_mem_laurentBaseChange_xHFunctionField_of_mem_modularFunctionFieldFull Qb 1 d (q ^ 2 * M')
      (by rw [one_mul]; exact hd.trans (Dvd.intro _ rfl)) _ jq hjfull
  have hX₀mem : jqModC Qb ∈ fieldBar q M' := by
    have := hmemF 1 (one_dvd _); rwa [qExpand_one_apply] at this
  have hX₁mem : qExpand Qb q (jqModC Qb) ∈ fieldBar q M' := hmemF q (dvd_pow_self q two_ne_zero)
  have hX₂mem : qExpand Qb (q ^ 2) (jqModC Qb) ∈ fieldBar q M' := hmemF (q ^ 2) dvd_rfl
  have hJ : jqModC Qb ∈ laurentBaseChange Qb (qExpFunctionFieldC ℚ (CongruenceSubgroup.Gamma0 M')) := by
    rw [← hJbar]
    apply coeffEmb_mem_laurentBaseChange
    rw [qExpFunctionFieldC_rat_gamma0_eq_modularFunctionFieldFull]
    have := jqd_mem_full M' (d := 1) (one_dvd M'); rwa [qExpand_one_apply] at this
  set X₀ : ↥(fieldBar q M') := ⟨_, hX₀mem⟩
  set X₁ : ↥(fieldBar q M') := ⟨_, hX₁mem⟩
  set X₂ : ↥(fieldBar q M') := ⟨_, hX₂mem⟩

  have hιKx' : (q : ↥(fieldBar q M')) * ιK x = X₂ - X₁ ^ q := by
    apply Subtype.ext
    show (((q : ↥(fieldBar q M')) * ιK x : ↥(fieldBar q M')) : LaurentSeries Qb) = ((X₂ - X₁ ^ q : ↥(fieldBar q M')) : LaurentSeries Qb)
    push_cast
    rw [hιKx]
    show (q : LaurentSeries Qb) * qExpand Qb q Gb = qExpand Qb (q ^ 2) (jqModC Qb) - (qExpand Qb q (jqModC Qb)) ^ q
    rw [qExpand_congr (pow_two q), ← qExpand_qExpand, ← map_pow, ← map_sub, ← hGbq, map_mul, map_natCast]

  have hζ'unit : IsUnit (ζ'.val) := (Idx.isPrimitiveRoot ζ').isUnit hq0.ne'
  obtain ⟨hfix, k, htwist⟩ := sigma q M' hqM' ζ' γ hγ hc hζ'unit.unit (by simp) X₀ X₁ X₂ rfl rfl rfl hJ
  set σ := levelAutBar q M' ζ' γ⁻¹ with hσ
  have hσN : (q : LaurentSeries Qb) * ((σ (ιK x) : ↥(fieldBar q M')) : LaurentSeries Qb) =
      qTwist (hζ'unit.unit ^ k) (jqModC Qb) - (qExpand Qb q (jqModC Qb)) ^ q := by
    have h1 : σ ((q : ↥(fieldBar q M')) * ιK x) = (q : ↥(fieldBar q M')) * σ (ιK x) := by
      rw [map_mul, map_natCast]
    have h2 : σ ((q : ↥(fieldBar q M')) * ιK x) = σ X₂ - (σ X₁) ^ q := by
      rw [hιKx', map_sub, map_pow]
    rw [hfix] at h2
    have h3 := congrArg (fun t : ↥(fieldBar q M') => (t : LaurentSeries Qb)) (h1.symm.trans h2)
    push_cast at h3
    rw [htwist] at h3
    exact h3

  have hnot : σ (ιK x) ∉ O :=
    not_mem_of_natCast_mul_eq q M' A' hA'q O hO hζ'unit.unit
      (by rw [IsUnit.unit_spec]; exact (Idx.isPrimitiveRoot ζ').pow_eq_one) k (σ (ιK x)) hσN

  have hGbS : Gb = laurentMap (Int.castRingHom Qb) S := by
    rw [hGb, hGℚ, coeffEmb]
    show laurentMap (algebraMap ℚ Qb) (laurentMap (Int.castRingHom ℚ) S) = _
    rw [laurentMap_laurentMap]
    congr 1
  have hxO : ιK x ∈ O := mem_of_coe_eq_qExpand_laurentMap q M' A' O hO S (ιK x) (by rw [hιKx, hGbS])
  have hxW : x ∈ W₀ := (hOW x).mp hxO

  intro hiff
  have h1 : (τ γ) x ∈ W₀ := by
    have := hiff.mpr hxW
    rwa [ValuationSubring.mem_comap] at this
  exact hnot (by rw [hσ, ← hint]; exact (hOW _).mpr h1)

end S_ModularCurve_FullLevel_exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_qExpand_mem_gauss_xor_mem_comap_gauss_of_dvd_of_not_dvd_of_isLevelAutAt (solution)
