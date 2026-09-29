-- Prove2me | solution 1 for ModularCurve.nonempty_igusaDiamondDataX1C
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/7bfd1792-57ca-5ede-bdb4-52af5d810951

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_IgusaFunctionField
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_x1FunctionFieldC
import Theorems.Thm_ModularCurve_isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C
import Theorems.Thm_ModularCurve_hasseRootFn_notMem_x1FunctionFieldC_charThree
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_nonempty_igusaDiamondDataX1C
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instFinite CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub"
p2m_attr_erase "instance" "KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq"
p2m_attr_erase "simp" "GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ"
p2m_attr_erase "simp" "ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring"
p2m_attr_erase "simp" "ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero"
p2m_attr_erase "simp" "compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

set_option maxHeartbeats 6400000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (k : Type) [Field k] [IsAlgClosed k] [CharP k p]
    (w : ModularCurve.IntegralWeightOneForm k M) :
    Nonempty (ModularCurve.IgusaDiamondDataX1C k M w p) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hnpos, ha0, hhmem⟩ := ModularCurve.isKummerGenerator_hasseRootFn_x1FunctionFieldC p M hM hpM k w

  set K₀ : IntermediateField k (LaurentSeries k) := ModularCurve.x1FunctionFieldC k M with hK₀
  set a : LaurentSeries k := w.hasseRootFn with ha
  set n : ℕ := p - 1 with hn

  let hK : ↥K₀ := ⟨a ^ n, hhmem⟩
  let P : Polynomial ↥K₀ := Polynomial.X ^ n - Polynomial.C hK
  have hPmonic : P.Monic := Polynomial.monic_X_pow_sub_C hK hnpos.ne'
  have hPdeg : P.natDegree = n := Polynomial.natDegree_X_pow_sub_C
  have hPa : Polynomial.aeval a P = 0 := by
    simp only [P, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, IntermediateField.algebraMap_apply]
    exact sub_self _
  have hint : IsIntegral (↥K₀) a := ⟨P, hPmonic, by rwa [← Polynomial.aeval_def]⟩
  have hdvd : minpoly (↥K₀) a ∣ P := minpoly.dvd _ _ hPa
  have hdegle : (minpoly (↥K₀) a).natDegree ≤ n :=
    hPdeg ▸ Polynomial.natDegree_le_of_dvd hdvd hPmonic.ne_zero
  have hdegpos : 0 < (minpoly (↥K₀) a).natDegree := minpoly.natDegree_pos hint

  let E : IntermediateField (↥K₀) (LaurentSeries k) := IntermediateField.adjoin (↥K₀) {a}
  have hE : E.restrictScalars k = ModularCurve.IgusaCover.igusaFunctionField K₀ a := by
    exact IntermediateField.restrictScalars_adjoin (F := k) K₀ ({a} : Set (LaurentSeries k))
  have hfinrankE : Module.finrank (↥K₀) ↥E = (minpoly (↥K₀) a).natDegree := IntermediateField.adjoin.finrank hint

  have hdeg : (minpoly (↥K₀) a).natDegree = n := by
    rcases Nat.lt_or_ge p 5 with hp5 | hp5
    ·
      have hp23 : p = 2 ∨ p = 3 := by
        rcases hp.eq_two_or_odd' with h2 | hodd
        · exact Or.inl h2
        · right
          have := hp.two_le
          rcases hodd with ⟨m, rfl⟩
          omega
      rcases hp23 with rfl | rfl
      ·
        have : n = 1 := by rw [hn]
        omega
      ·
        have hn2 : n = 2 := by rw [hn]
        haveI : CharP k 3 := inferInstance
        have hnot : a ∉ K₀ := ModularCurve.hasseRootFn_notMem_x1FunctionFieldC_charThree M hM hpM k w
        have hne1 : (minpoly (↥K₀) a).natDegree ≠ 1 := by
          intro h1
          apply hnot
          rw [minpoly.natDegree_eq_one_iff] at h1
          obtain ⟨x, hx⟩ := h1
          rw [← hx]
          exact x.2
        omega
    ·
      have hrel := (ModularCurve.isKummerGenerator_hasseRootFn_and_relfinrank_igusaFunctionFieldX1C p hp5 k M hM hpM w).2
      have hle : K₀ ≤ ModularCurve.igusaFunctionFieldX1C k M w := ModularCurve.IgusaCover.le_igusaFunctionField K₀ a
      rw [IntermediateField.relfinrank_eq_finrank_of_le hle] at hrel
      have hEq : IntermediateField.extendScalars hle = E := by
        apply IntermediateField.restrictScalars_injective k
        rw [hE]
        rfl
      rw [hEq, hfinrankE] at hrel
      exact hrel
  have hmin : minpoly (↥K₀) a = P :=
    (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hPmonic hdvd (by rw [hPdeg, hdeg])).symm

  haveI : FiniteDimensional (↥K₀) ↥E := IntermediateField.adjoin.finiteDimensional hint
  let pb : PowerBasis (↥K₀) ↥E := IntermediateField.adjoin.powerBasis hint
  have hpbgen : pb.gen = IntermediateField.AdjoinSimple.gen (↥K₀) a := IntermediateField.adjoin.powerBasis_gen hint
  have hpbgen' : ((pb.gen : ↥E) : LaurentSeries k) = a := by rw [hpbgen]; rfl

  let ι : k →+* ↥K₀ := algebraMap k ↥K₀
  have hι : ∀ c : k, ((ι c : ↥K₀) : LaurentSeries k) = algebraMap k (LaurentSeries k) c := fun c => rfl
  have hmem_ca : ∀ c : k, algebraMap k (LaurentSeries k) c * a ∈ E := fun c =>
    mul_mem (E.algebraMap_mem (ι c)) (IntermediateField.mem_adjoin_simple_self (↥K₀) a)
  let ya : k → ↥E := fun c => ⟨algebraMap k (LaurentSeries k) c * a, hmem_ca c⟩
  have hya : ∀ c : k, ((ya c : ↥E) : LaurentSeries k) = algebraMap k (LaurentSeries k) c * a := fun c => rfl
  have hyaK : ∀ c : k, ya c = ι c • pb.gen := by
    intro c
    apply Subtype.ext
    rw [hya, Algebra.smul_def, MulMemClass.coe_mul, hpbgen']
    rfl
  have hroot : ∀ c : k, c ^ n = 1 → Polynomial.aeval (ya c) (minpoly (↥K₀) pb.gen) = 0 := by
    intro c hc
    rw [hpbgen, IntermediateField.minpoly_gen (↥K₀) a, hmin]
    simp only [P, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C]
    rw [sub_eq_zero]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, hya, mul_pow, ← map_pow, hc, map_one, one_mul]
    rfl
  let σ : ∀ c : k, c ^ n = 1 → (↥E →ₐ[↥K₀] ↥E) := fun c hc => pb.lift (ya c) (hroot c hc)
  have hσgen : ∀ (c : k) (hc : c ^ n = 1), σ c hc pb.gen = ya c := fun c hc => pb.lift_gen _ _
  have hσcomp : ∀ (c₁ : k) (hc₁ : c₁ ^ n = 1) (c₂ : k) (hc₂ : c₂ ^ n = 1) (h12 : (c₁ * c₂) ^ n = 1),
      σ (c₁ * c₂) h12 = (σ c₁ hc₁).comp (σ c₂ hc₂) := by
    intro c₁ hc₁ c₂ hc₂ h12
    apply pb.algHom_ext
    rw [hσgen _ h12, AlgHom.comp_apply, hσgen _ hc₂, hyaK, hyaK, map_smul, hσgen _ hc₁, hyaK, smul_smul, ← map_mul, mul_comm]
  have hσone : ∀ h1 : (1 : k) ^ n = 1, σ 1 h1 = AlgHom.id (↥K₀) ↥E := by
    intro h1
    apply pb.algHom_ext
    rw [hσgen _ h1, AlgHom.id_apply, hyaK, map_one, one_smul]
  have hσcongr : ∀ (c₁ : k) (hc₁ : c₁ ^ n = 1) (c₂ : k) (hc₂ : c₂ ^ n = 1), c₁ = c₂ → σ c₁ hc₁ = σ c₂ hc₂ := by
    intro c₁ hc₁ c₂ hc₂ h
    subst h
    rfl
  let τ : ∀ c : k, c ^ n = 1 → (↥E ≃ₐ[↥K₀] ↥E) := fun c hc =>
    AlgEquiv.ofBijective (σ c hc) (Algebra.IsAlgebraic.algHom_bijective (σ c hc))
  have hτ : ∀ (c : k) (hc : c ^ n = 1) (x : ↥E), τ c hc x = σ c hc x := fun c hc x => rfl

  let χ : (ZMod p)ˣ → k := fun b => ZMod.castHom (dvd_refl p) k ((b⁻¹ : (ZMod p)ˣ) : ZMod p)
  have hχmul : ∀ b₁ b₂, χ (b₁ * b₂) = χ b₁ * χ b₂ := by
    intro b₁ b₂
    show ZMod.castHom (dvd_refl p) k (((b₁ * b₂)⁻¹ : (ZMod p)ˣ) : ZMod p) = _
    rw [mul_inv_rev, Units.val_mul, map_mul, mul_comm]
  have hχone : χ 1 = 1 := by
    show ZMod.castHom (dvd_refl p) k (((1 : (ZMod p)ˣ)⁻¹ : (ZMod p)ˣ) : ZMod p) = 1
    rw [inv_one, Units.val_one, map_one]
  have hχn : ∀ b, χ b ^ n = 1 := by
    intro b
    show ZMod.castHom (dvd_refl p) k ((b⁻¹ : (ZMod p)ˣ) : ZMod p) ^ (p - 1) = 1
    rw [← map_pow, ← Units.val_pow_eq_pow_val, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, map_one]

  let e : ↥(E.restrictScalars k) ≃ₐ[k] ↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a) := IntermediateField.equivOfEq hE
  have he : ∀ x : ↥(E.restrictScalars k), ((e x : ↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a)) : LaurentSeries k) = (x : LaurentSeries k) :=
    fun x => rfl
  have he' : ∀ y : ↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a), ((e.symm y : ↥(E.restrictScalars k)) : LaurentSeries k) = (y : LaurentSeries k) :=
    fun y => rfl
  let ρ : (ZMod p)ˣ → (↥E ≃ₐ[k] ↥E) := fun b => (τ (χ b) (hχn b)).restrictScalars k
  let act : (ZMod p)ˣ → (↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a) ≃ₐ[k] ↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a)) :=
    fun b => (e.symm.trans (ρ b)).trans e
  have hact : ∀ b y, act b y = e (ρ b (e.symm y)) := fun b y => rfl
  have hρ : ∀ b (x : ↥E), ρ b x = σ (χ b) (hχn b) x := fun b x => rfl
  refine ⟨{ act := { toFun := act, map_one' := ?_, map_mul' := ?_ }, act_apply_of_mem := ?_, act_gen := ?_ }⟩
  ·
    apply AlgEquiv.ext
    intro y
    change e (ρ 1 (e.symm y)) = y
    rw [hρ]
    have : σ (χ 1) (hχn 1) = AlgHom.id (↥K₀) ↥E := by
      have h1 : (1 : k) ^ n = 1 := one_pow n
      rw [hσcongr _ (hχn 1) _ h1 hχone]
      exact hσone h1
    rw [this, AlgHom.id_apply]
    exact e.apply_symm_apply y
  ·
    intro b₁ b₂
    apply AlgEquiv.ext
    intro y
    change act (b₁ * b₂) y = act b₁ (act b₂ y)
    rw [hact, hact, hact, hρ, hρ, hρ, AlgEquiv.symm_apply_apply]
    have : σ (χ (b₁ * b₂)) (hχn (b₁ * b₂)) = (σ (χ b₁) (hχn b₁)).comp (σ (χ b₂) (hχn b₂)) := by
      have h12 : (χ b₁ * χ b₂) ^ n = 1 := by rw [mul_pow, hχn, hχn, one_mul]
      rw [hσcongr _ (hχn (b₁ * b₂)) _ h12 (hχmul b₁ b₂)]
      exact hσcomp _ (hχn b₁) _ (hχn b₂) h12
    rw [this, AlgHom.comp_apply]
  ·
    intro b y hy
    show act b y = y
    rw [hact, hρ]
    have hx : (e.symm y : ↥E) = algebraMap (↥K₀) ↥E ⟨(y : LaurentSeries k), hy⟩ := Subtype.ext rfl
    apply Subtype.ext
    rw [he]
    show ((σ (χ b) (hχn b) (e.symm y) : ↥E) : LaurentSeries k) = y
    rw [hx, AlgHom.commutes]
    rfl
  ·
    intro b
    rw [zpow_neg_one]
    show ((act b ⟨a, _⟩ : ↥(ModularCurve.IgusaCover.igusaFunctionField K₀ a)) : LaurentSeries k) = _
    rw [hact, he, hρ]
    have hx : (e.symm ⟨a, ModularCurve.IgusaCover.mem_igusaFunctionField K₀ a⟩ : ↥E) = pb.gen := by
      apply Subtype.ext
      rw [hpbgen']
      rfl
    show ((σ (χ b) (hχn b) (e.symm ⟨a, _⟩) : ↥E) : LaurentSeries k) = _
    rw [hx, hσgen _ (hχn b), hya, Algebra.smul_def]

end S_ModularCurve_nonempty_igusaDiamondDataX1C
end P2MW
export P2MW.S_ModularCurve_nonempty_igusaDiamondDataX1C (solution)
