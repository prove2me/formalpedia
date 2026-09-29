-- Prove2me | solution 1 for ModularCurve.finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ef04ab3c-9eb5-5388-a3ed-35c129322393

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C
import Theorems.Thm_ModularCurve_finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C
import Theorems.Thm_ModularCurve_finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem
import Theorems.Thm_ModularCurve_finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le
import Theorems.Thm_ModularCurve_jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd
import Theorems.Thm_ModularCurve_jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd
import Theorems.Thm_ModularCurve_finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd
import Theorems.Thm_ModularCurve_adjoin_image_coeffMap_igusaFunctionFieldX1C_eq
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_mul
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_CharPModel_relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq
p2m_attr_erase "instance" "TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite ModularCurve.Gamma0Pair.isElliptic CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule"
p2m_attr_erase "instance" "KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero"
p2m_attr_erase "simp" "AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single"
p2m_attr_erase "simp" "ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false

namespace D3GluePen14

p2m_open "ModularCurve~dedekindPsi_pos~qTwist_qExpand_of_pow_eq_one P2MW.S_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq.ModularCurve IntermediateField"

variable {k : Type*} [Field k] {K : Type*} [Field K] [Algebra k K]

local notation "ι" => ModularCurve.coeffMap (algebraMap k K)

theorem coeffMap_algebraMap (a : k) :
    (ι) (algebraMap k (LaurentSeries k) a) = algebraMap K (LaurentSeries K) (algebraMap k K a) := by
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem adjoin_image_coe_adjoin (T : Set (LaurentSeries k)) :
    adjoin K ((ι) '' (adjoin k T : Set (LaurentSeries k))) = adjoin K ((ι) '' T) := by
  apply le_antisymm
  · rw [adjoin_le_iff]

    have hcoe : ((adjoin k T : IntermediateField k (LaurentSeries k)) : Set (LaurentSeries k)) =
        (Subfield.closure (Set.range (algebraMap k (LaurentSeries k)) ∪ T) : Set (LaurentSeries k)) := by
      rw [← coe_toSubfield, adjoin_toSubfield]
    rw [hcoe, ← Subfield.coe_map, RingHom.map_field_closure]
    show (Subfield.closure ((ι) '' (Set.range (algebraMap k (LaurentSeries k)) ∪ T)) : Set (LaurentSeries K)) ⊆
      ((adjoin K ((ι) '' T)).toSubfield : Set (LaurentSeries K))
    rw [SetLike.coe_subset_coe, Subfield.closure_le, Set.image_union]
    refine Set.union_subset ?_ (subset_adjoin K _)
    rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
    rw [coeffMap_algebraMap]
    exact (adjoin K _).algebraMap_mem _
  · exact adjoin.mono K _ _ (Set.image_mono (subset_adjoin k T))

theorem adjoin_image_restrictScalars_adjoin (E : IntermediateField k (LaurentSeries k)) (S : Set (LaurentSeries k)) :
    adjoin K ((ι) '' ((adjoin ↥E S).restrictScalars k : Set (LaurentSeries k))) =
      (adjoin ↥(adjoin K ((ι) '' (E : Set (LaurentSeries k)))) ((ι) '' S)).restrictScalars K := by
  have hL : (((adjoin ↥E S).restrictScalars k : IntermediateField k (LaurentSeries k)) : Set (LaurentSeries k)) =
      ((adjoin k ((E : Set (LaurentSeries k)) ∪ S) : IntermediateField k (LaurentSeries k)) : Set (LaurentSeries k)) := by
    have := IntermediateField.restrictScalars_adjoin (F := k) E S
    exact congrArg SetLike.coe this
  have hR : ((adjoin ↥(adjoin K ((ι) '' (E : Set (LaurentSeries k)))) ((ι) '' S)).restrictScalars K : IntermediateField K (LaurentSeries K)) =
      adjoin K ((ι) '' (E : Set (LaurentSeries k)) ∪ (ι) '' S) := by
    have h1 := IntermediateField.restrictScalars_adjoin (F := K) (adjoin K ((ι) '' (E : Set (LaurentSeries k)))) ((ι) '' S)
    have h2 := IntermediateField.adjoin_adjoin_left K ((ι) '' (E : Set (LaurentSeries k))) ((ι) '' S)
    exact h2
  rw [hL, adjoin_image_coe_adjoin, Set.image_union, hR]

theorem finrank_adjoin_simple_coeffMap_eq (E : IntermediateField k (LaurentSeries k)) (x : LaurentSeries k)
    (hfin : 0 < Module.finrank ↥E ↥(adjoin ↥E ({x} : Set (LaurentSeries k)))) :
    Module.finrank ↥(adjoin K ((ι) '' (E : Set (LaurentSeries k))))
        ↥(adjoin ↥(adjoin K ((ι) '' (E : Set (LaurentSeries k)))) ({(ι) x} : Set (LaurentSeries K))) =
      Module.finrank ↥E ↥(adjoin ↥E ({x} : Set (LaurentSeries k))) := by

  set E' : IntermediateField k (LaurentSeries k) := (adjoin ↥E ({x} : Set (LaurentSeries k))).restrictScalars k with hE'
  have hEE' : E ≤ E' := fun y hy => (adjoin ↥E ({x} : Set (LaurentSeries k))).algebraMap_mem ⟨y, hy⟩
  have hext : extendScalars hEE' = adjoin ↥E ({x} : Set (LaurentSeries k)) :=
    IntermediateField.ext fun _ => Iff.rfl
  have h1 : relfinrank E E' = Module.finrank ↥E ↥(adjoin ↥E ({x} : Set (LaurentSeries k))) := by
    rw [relfinrank_eq_finrank_of_le hEE', hext]

  set Et := adjoin K ((ι) '' (E : Set (LaurentSeries k))) with hEt
  set Et' : IntermediateField K (LaurentSeries K) := (adjoin ↥Et ({(ι) x} : Set (LaurentSeries K))).restrictScalars K with hEt'
  have hle : Et ≤ Et' := fun y hy => (adjoin ↥Et ({(ι) x} : Set (LaurentSeries K))).algebraMap_mem ⟨y, hy⟩
  have hext' : extendScalars hle = adjoin ↥Et ({(ι) x} : Set (LaurentSeries K)) :=
    IntermediateField.ext fun _ => Iff.rfl
  have hG0 : adjoin K ((ι) '' (E' : Set (LaurentSeries k))) = Et' := by
    rw [hE', adjoin_image_restrictScalars_adjoin, Set.image_singleton]

  have hLD := ModularCurve.relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le k K E E' hEE' (h1 ▸ hfin)
  rw [hG0, h1, relfinrank_eq_finrank_of_le hle, hext'] at hLD
  exact hLD

end D3GluePen14

namespace ModularCurve
p2m_export "ModularCurve" "intSeriesC qExpFunctionFieldC qExpFunctionFieldC_mono x1FunctionFieldC qExpand qExpand_coeff_mul qExpand_injective qExpand_one_apply qExpand_congr qExpand_qExpand dedekindPsi coeffMap coeffMap_coeff coeffMap_single algebraMap_laurentSeries_eq_single coeffMap_algebraMap IntegralWeightOneForm igusaFunctionFieldX1C x1FunctionFieldC_le_igusaFunctionFieldX1C jqModC jqNModC modularFunctionFieldC jqModC_mem jqNModC_mem coeffMap_ofPowerSeries coeffMap_jqModC coeffMap_jqNModC qExpandAlgHomC modularFunctionFieldFullC jqModCd_mem_full coeffMap_qExpand coeff_jqModC_neg_one qTwist qTwist_coeff qTwist_one_apply qTwist_qExpand exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd adjoin_image_coeffMap_igusaFunctionFieldX1C_eq modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 isIntegral_jqNModC_mul relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi CharPModel.relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm modularPolynomialFamily"
p2m_open "ModularCurve~dedekindPsi_pos~qTwist_qExpand_of_pow_eq_one"
namespace D3Assembly

open IntermediateField Polynomial

theorem qExpand_jqModC_mem_igusa (K : Type*) [Field K] (M : ℕ) [NeZero M]
    (w : IntegralWeightOneForm K M) (d : ℕ) [NeZero d] (hd : d ∣ M) :
    qExpand K d (jqModC K) ∈ igusaFunctionFieldX1C K M w := by
  have h1 : qExpand K d (jqModC K) ∈ modularFunctionFieldFullC K M := jqModCd_mem_full K M hd
  have h2 := modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0 K M h1
  have h3 : qExpFunctionFieldC K (CongruenceSubgroup.Gamma0 M) ≤ x1FunctionFieldC K M :=
    qExpFunctionFieldC_mono K (CongruenceSubgroup.Gamma1_in_Gamma0 M)
  exact x1FunctionFieldC_le_igusaFunctionFieldX1C K M w (h3 h2)

theorem mem_map_iff {F L L' : Type*} [Field F] [Field L] [Field L'] [Algebra F L] [Algebra F L']
    (f : L →ₐ[F] L') (S : IntermediateField F L) (y : L') : y ∈ S.map f ↔ ∃ x ∈ S, f x = y := by
  rw [← SetLike.mem_coe, IntermediateField.coe_map, Set.mem_image]
  simp only [SetLike.mem_coe]

section Twist

variable {K : Type*} [Field K]

theorem units_pow_eq_one_of_isPrimitiveRoot {ℓ : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) :
    ζ ^ ℓ = 1 :=
  Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact hζ.pow_eq_one)

theorem qTwist_qExpand_of_pow_eq_one {ℓ : ℕ} [NeZero ℓ] {ζ : Kˣ} (hζ : ζ ^ ℓ = 1)
    (f : LaurentSeries K) : qTwist ζ (qExpand K ℓ f) = qExpand K ℓ f := by
  rw [qTwist_qExpand, zpow_natCast, hζ, qTwist_one_apply]

theorem forall_mem_map_qExpandAlgHomC_qTwist_eq {ℓ : ℕ} [NeZero ℓ] {ζ : Kˣ} (hζ : ζ ^ ℓ = 1)
    (F : IntermediateField K (LaurentSeries K)) :
    ∀ f : LaurentSeries K, f ∈ F.map (qExpandAlgHomC K ℓ) → qTwist ζ f = f := by
  intro f hf
  rw [mem_map_iff] at hf
  obtain ⟨g, -, rfl⟩ := hf
  exact qTwist_qExpand_of_pow_eq_one hζ g

theorem qTwist_qExpand_jqModC_ne {ℓ : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (M : ℕ) [NeZero M] (hℓM : ¬ ℓ ∣ M) :
    qTwist ζ (qExpand K M (jqModC K)) ≠ qExpand K M (jqModC K) := by
  intro h
  have hc := congrArg (fun f : LaurentSeries K => f.coeff ((M : ℤ) * (-1))) h
  simp only [qTwist_coeff, qExpand_coeff_mul, coeff_jqModC_neg_one, mul_one] at hc
  have hu : ζ ^ ((M : ℤ) * (-1)) = 1 := Units.ext (by rw [Units.val_one]; exact hc)
  rw [mul_neg_one, zpow_neg, inv_eq_one, zpow_natCast] at hu
  have hK : (ζ : K) ^ M = 1 := by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one]
  exact hℓM ((hζ.pow_eq_one_iff_dvd M).mp hK)

theorem qTwist_jqModC_ne {ℓ : ℕ} {ζ : Kˣ} (hζ : IsPrimitiveRoot (ζ : K) ℓ) (hℓ : 1 < ℓ) :
    qTwist ζ (jqModC K) ≠ jqModC K := by
  have h := qTwist_qExpand_jqModC_ne (K := K) hζ 1 (fun h1 => by
    have := Nat.le_of_dvd Nat.one_pos h1; omega)
  rwa [qExpand_one_apply] at h

end Twist

section Core

theorem core_alpha (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (M : ℕ) [NeZero M]
    (hM : 5 ≤ M) (hpM : ¬ p ∣ M) (w : IntegralWeightOneForm K M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ)
    (hℓM : ¬ ℓ ∣ M) [NeZero ℓ] [NeZero (M * ℓ)] :
    Module.finrank ↥(igusaFunctionFieldX1C K M w)
      ↥(IntermediateField.adjoin ↥(igusaFunctionFieldX1C K M w)
        ({jqNModC K (M * ℓ)} : Set (LaurentSeries K))) = ℓ + 1 := by
  set Ig := igusaFunctionFieldX1C K M w with hIg
  set Igt : IntermediateField K (LaurentSeries K) := Ig.map (qExpandAlgHomC K ℓ) with hIgt
  have hcoe : (Igt : Set (LaurentSeries K)) = qExpand K ℓ '' (Ig : Set (LaurentSeries K)) :=
    IntermediateField.coe_map _ _

  rw [← finrank_adjoin_qExpand_eq_finrank_adjoin_of_coe_eq_image K ℓ Ig Igt hcoe (jqNModC K (M * ℓ))]

  have hx_eq : qExpand K ℓ (jqNModC K (M * ℓ)) = qExpand K (ℓ * (ℓ * M)) (jqModC K) := by
    rw [jqNModC, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  rw [hx_eq]
  have hζℓ : ζ ^ ℓ = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hjM : qExpand K M (jqModC K) ∈ Ig := qExpand_jqModC_mem_igusa K M w M dvd_rfl
  have hmem : qExpand K (ℓ * M) (jqModC K) ∈ Igt := by
    rw [← qExpand_qExpand]
    exact (mem_map_iff _ _ _).mpr ⟨_, hjM, rfl⟩
  obtain ⟨P, -, -, hP⟩ :=
    exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C K ℓ ζ hζ M hℓM Igt hmem
  refine finrank_adjoin_eq_succ_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C_of_not_mem K ℓ ζ hζ Igt
    (forall_mem_map_qExpandAlgHomC_qTwist_eq hζℓ Ig) (qExpand K (ℓ * (ℓ * M)) (jqModC K))
    (qExpand K M (jqModC K)) (qTwist_qExpand_jqModC_ne hζ M hℓM) ?_ ?_ P hP
  ·
    rw [← hx_eq]
    exact qTwist_qExpand_of_pow_eq_one hζℓ _
  ·
    rw [← hx_eq]
    intro hx
    obtain ⟨g, hg, hgx⟩ := (mem_map_iff _ _ _).mp hx
    have hg' : g = jqNModC K (M * ℓ) := qExpand_injective ℓ hgx
    exact jqNModC_mul_not_mem_igusaFunctionFieldX1C_of_not_dvd p K M hM hpM w ℓ hℓp hℓM (hg' ▸ hg)

theorem core_beta (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (M : ℕ) [NeZero M]
    (hM : 5 ≤ M) (hpM : ¬ p ∣ M) (w : IntegralWeightOneForm K M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) [NeZero ℓ] :
    Module.finrank ↥((igusaFunctionFieldX1C K M w).map (qExpandAlgHomC K ℓ))
      ↥(IntermediateField.adjoin ↥((igusaFunctionFieldX1C K M w).map (qExpandAlgHomC K ℓ))
        ({jqModC K} : Set (LaurentSeries K))) = if ℓ ∣ M then ℓ else ℓ + 1 := by
  set Ig := igusaFunctionFieldX1C K M w with hIg
  set Ig' : IntermediateField K (LaurentSeries K) := Ig.map (qExpandAlgHomC K ℓ) with hIg'
  have hℓ1 : 1 < ℓ := (Fact.out : ℓ.Prime).one_lt
  have hζℓ : ζ ^ ℓ = 1 := units_pow_eq_one_of_isPrimitiveRoot hζ
  have hj : jqModC K ∈ Ig := by
    have := qExpand_jqModC_mem_igusa K M w 1 (one_dvd M)
    rwa [qExpand_one_apply] at this
  have hmem : qExpand K (ℓ * 1) (jqModC K) ∈ Ig' := by
    rw [qExpand_congr (mul_one ℓ)]
    exact (mem_map_iff _ _ _).mpr ⟨_, hj, rfl⟩
  obtain ⟨P, -, -, hP⟩ :=
    exists_monic_map_eq_prod_X_sub_C_qTwist_qExpand_jqModC_mul_X_sub_C K ℓ ζ hζ 1
      (fun h1 => by have := Nat.le_of_dvd Nat.one_pos h1; omega) Ig' hmem
  simp only [qExpand_one_apply] at hP
  have hL3 := finrank_adjoin_eq_of_map_eq_prod_X_sub_C_qTwist_mul_X_sub_C K ℓ ζ hζ Ig'
    (forall_mem_map_qExpandAlgHomC_qTwist_eq hζℓ Ig) (jqModC K)
    (qExpand K (ℓ * (ℓ * 1)) (jqModC K)) (qTwist_jqModC_ne hζ hℓ1) P hP
  have hr : qExpand K (ℓ * (ℓ * 1)) (jqModC K) = qExpand K ℓ (qExpand K ℓ (jqModC K)) := by
    rw [qExpand_qExpand]
    exact qExpand_congr (by ring) _
  by_cases hℓM : ℓ ∣ M
  · rw [if_pos hℓM]
    refine hL3.2 ?_
    rw [hr]
    exact (mem_map_iff _ _ _).mpr ⟨_, qExpand_jqModC_mem_igusa K M w ℓ hℓM, rfl⟩
  · rw [if_neg hℓM]
    refine hL3.1 ?_
    rw [hr]
    intro hx
    obtain ⟨g, hg, hgx⟩ := (mem_map_iff _ _ _).mp hx
    have hg' : g = jqNModC K ℓ := qExpand_injective ℓ hgx
    exact jqNModC_not_mem_igusaFunctionFieldX1C_of_not_dvd p K M hM hpM w ℓ hℓp hℓM (hg' ▸ hg)

end Core

theorem finrank_adjoin_pos_of_isIntegral {κ : Type*} [Field κ]
    (E : IntermediateField κ (LaurentSeries κ)) {x : LaurentSeries κ} (hx : IsIntegral ↥E x) :
    0 < Module.finrank ↥E ↥(IntermediateField.adjoin ↥E ({x} : Set (LaurentSeries κ))) := by
  haveI := IntermediateField.adjoin.finiteDimensional hx
  exact Module.finrank_pos

theorem dedekindPsi_pos (N : ℕ) (hN : N ≠ 0) : 0 < dedekindPsi N := by
  unfold dedekindPsi
  have h1 : (1 : ℕ) ∈ N.divisors.filter (fun d => Squarefree d) :=
    Finset.mem_filter.mpr ⟨Nat.one_mem_divisors.mpr hN, squarefree_one⟩
  have h2 := Finset.single_le_sum (s := N.divisors.filter (fun d => Squarefree d)) (f := fun d => N / d)
    (fun _ _ => Nat.zero_le _) h1
  simp only [Nat.div_one] at h2
  omega

theorem isIntegral_jqModC_of_jqNModC_mem (p : ℕ) [Fact p.Prime] (κ : Type*) [Field κ] [CharP κ p]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) [NeZero ℓ]
    (F : IntermediateField κ (LaurentSeries κ)) (hF : jqNModC κ ℓ ∈ F) : IsIntegral ↥F (jqModC κ) := by
  obtain ⟨data, hsym⟩ := modularPolynomialFamily ℓ Fact.out
  have hpl : ¬ p ∣ ℓ := fun h =>
    hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp h).symm
  have hdeg := relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi κ ℓ p hpl
  have hN := CharPModel.relfinrank_adjoin_jqNModC_eq_dedekindPsi_of_evalSymm ℓ κ data hsym hdeg
  set A : IntermediateField κ (LaurentSeries κ) :=
    IntermediateField.adjoin κ ({(jqNModC κ ℓ : LaurentSeries κ)} : Set (LaurentSeries κ)) with hA
  have hAB : A ≤ modularFunctionFieldC κ ℓ :=
    IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr (jqNModC_mem κ ℓ))
  have hpos : 0 < Module.finrank ↥A ↥(IntermediateField.extendScalars hAB) := by
    rw [← IntermediateField.relfinrank_eq_finrank_of_le hAB, hN]
    exact dedekindPsi_pos ℓ (NeZero.ne ℓ)
  haveI : FiniteDimensional ↥A ↥(IntermediateField.extendScalars hAB) := FiniteDimensional.of_finrank_pos hpos
  have hjB : (jqModC κ) ∈ IntermediateField.extendScalars hAB := jqModC_mem κ ℓ
  have hint : IsIntegral ↥A (⟨jqModC κ, hjB⟩ : IntermediateField.extendScalars hAB) :=
    IsIntegral.of_finite ↥A _
  have hint' : IsIntegral ↥A (jqModC κ) := IntermediateField.isIntegral_iff.mp hint
  have hAF : A ≤ F := IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hF)
  letI : Algebra ↥A ↥F := (IntermediateField.inclusion hAF).toRingHom.toAlgebra
  haveI : IsScalarTower ↥A ↥F (LaurentSeries κ) := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  exact hint'.tower_top

def IntegralWeightOneForm.baseChange {κ : Type*} [Field κ] (K : Type*) [Field K] [Algebra κ K]
    {M : ℕ} (w : IntegralWeightOneForm κ M) : IntegralWeightOneForm K M where
  form := w.form
  series := w.series
  isIntegralQExp := w.isIntegralQExp
  intSeriesC_ne_zero := by
    intro h
    apply w.intSeriesC_ne_zero
    have hmap : coeffMap (algebraMap κ K) (intSeriesC κ w.series) = intSeriesC K w.series := by
      rw [intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
      congr 1
      ext n
      simp only [PowerSeries.coeff_map, eq_intCast, map_intCast]
    ext k
    have hk := congrArg (fun f : LaurentSeries K => f.coeff k) (hmap.trans h)
    simp only [coeffMap_coeff] at hk
    apply (algebraMap κ K).injective
    rw [hk]
    simp

theorem exists_units_isPrimitiveRoot (p : ℕ) [Fact p.Prime] (K : Type*) [Field K] [CharP K p] [IsAlgClosed K]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) : ∃ ζ : Kˣ, IsPrimitiveRoot (ζ : K) ℓ := by
  have hℓK : (ℓ : K) ≠ 0 := by
    intro h
    rw [CharP.cast_eq_zero_iff K p] at h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mp h).symm
  haveI : NeZero (ℓ : K) := ⟨hℓK⟩
  have hpos : 0 < ℓ := (Fact.out : ℓ.Prime).pos
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic ℓ K)
    (Polynomial.degree_cyclotomic_pos ℓ K hpos).ne'
  rw [Polynomial.isRoot_cyclotomic_iff] at hz
  exact ⟨(hz.isUnit hpos.ne').unit, by rw [IsUnit.unit_spec]; exact hz⟩

end D3Assembly
end ModularCurve

p2m_open "ModularCurve~dedekindPsi_pos~qTwist_qExpand_of_pow_eq_one" in open _root_.P2MW.S_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq.ModularCurve ModularCurve.D3Assembly IntermediateField in

theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : ℓ.Prime).ne_zero⟩
    Module.finrank ↥(ModularCurve.igusaFunctionFieldX1C κ M w)
        ↥(IntermediateField.adjoin ↥(ModularCurve.igusaFunctionFieldX1C κ M w)
          ({ModularCurve.jqNModC κ (M * ℓ)} : Set (LaurentSeries κ))) = (if ℓ ∣ M then ℓ else ℓ + 1) ∧
    ∃ Ig' : IntermediateField κ (LaurentSeries κ),
      (Ig' : Set (LaurentSeries κ)) = ModularCurve.qExpand κ ℓ '' (ModularCurve.igusaFunctionFieldX1C κ M w : Set (LaurentSeries κ)) ∧
      Module.finrank ↥Ig' ↥(IntermediateField.adjoin ↥Ig' ({ModularCurve.jqModC κ} : Set (LaurentSeries κ))) =
        (if ℓ ∣ M then ℓ else ℓ + 1) := by
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  haveI : NeZero (M * ℓ) := ⟨mul_ne_zero (NeZero.ne M) (Fact.out : ℓ.Prime).ne_zero⟩

  let K : Type := AlgebraicClosure κ
  obtain ⟨ζ, hζ⟩ := exists_units_isPrimitiveRoot p K ℓ hℓp
  let w' : IntegralWeightOneForm K M := D3Assembly.IntegralWeightOneForm.baseChange K w
  set Ig := igusaFunctionFieldX1C κ M w with hIg
  have hIgK : IntermediateField.adjoin K (⇑(coeffMap (algebraMap κ K)) '' (Ig : Set (LaurentSeries κ))) =
      igusaFunctionFieldX1C K M w' :=
    adjoin_image_coeffMap_igusaFunctionFieldX1C_eq κ K M w w'
  obtain ⟨dataℓ, -⟩ := modularPolynomialFamily ℓ Fact.out
  refine ⟨?_, ?_⟩
  ·
    by_cases hℓM : ℓ ∣ M
    · rw [if_pos hℓM]
      exact finrank_adjoin_jqNModC_mul_igusaFunctionFieldX1C_eq_of_dvd p κ M hM hpM w ℓ hℓp hℓM
    · rw [if_neg hℓM]

      have hint : IsIntegral ↥Ig (jqNModC κ (M * ℓ)) :=
        isIntegral_jqNModC_mul Ig dataℓ M (qExpand_jqModC_mem_igusa κ M w M dvd_rfl)
      have hdesc := D3GluePen14.finrank_adjoin_simple_coeffMap_eq (K := K) Ig (jqNModC κ (M * ℓ))
        (finrank_adjoin_pos_of_isIntegral Ig hint)
      rw [← hdesc, coeffMap_jqNModC]
      rw [hIgK]
      exact core_alpha p K M hM hpM w' ℓ hℓp ζ hζ hℓM
  ·
    refine ⟨Ig.map (qExpandAlgHomC κ ℓ), IntermediateField.coe_map _ _, ?_⟩
    set Ig' : IntermediateField κ (LaurentSeries κ) := Ig.map (qExpandAlgHomC κ ℓ) with hIg'
    have hjℓ : jqNModC κ ℓ ∈ Ig' := by
      have hj : jqModC κ ∈ Ig := by
        have := qExpand_jqModC_mem_igusa κ M w 1 (one_dvd M)
        rwa [qExpand_one_apply] at this
      exact (mem_map_iff _ _ _).mpr ⟨_, hj, rfl⟩
    have hint : IsIntegral ↥Ig' (jqModC κ) := isIntegral_jqModC_of_jqNModC_mem p κ ℓ hℓp Ig' hjℓ
    have hdesc := D3GluePen14.finrank_adjoin_simple_coeffMap_eq (K := K) Ig' (jqModC κ)
      (finrank_adjoin_pos_of_isIntegral Ig' hint)
    rw [← hdesc, coeffMap_jqModC]

    have hIgK' : IntermediateField.adjoin K (⇑(coeffMap (algebraMap κ K)) '' (Ig' : Set (LaurentSeries κ))) =
        (igusaFunctionFieldX1C K M w').map (qExpandAlgHomC K ℓ) := by
      rw [← hIgK, IntermediateField.adjoin_map, hIg', IntermediateField.coe_map, Set.image_image,
        Set.image_image]
      congr 1
      refine Set.image_congr' fun f => ?_
      show coeffMap (algebraMap κ K) (qExpand κ ℓ f) = qExpand K ℓ (coeffMap (algebraMap κ K) f)
      exact coeffMap_qExpand _ ℓ f
    rw [hIgK']
    exact core_beta p K M hM hpM w' ℓ hℓp ζ hζ

end S_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq
end P2MW
export P2MW.S_ModularCurve_finrank_adjoin_jqNModC_igusaFunctionFieldX1C_eq (solution)
