-- Prove2me | solution 1 for ModularCurve.twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/86e6e51b-f1ca-5224-a4ea-b61a9f16ef0b

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental
import Theorems.Thm_ModularCurve_nonempty_integralWeightOneForm
import Theorems.Thm_ModularCurve_exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le
import Theorems.Thm_AlgebraicCurve_mul_apply_eq_mul_sub_min_ord_of_eq_floor_of_mul_degree_eq_finrank
import Theorems.Thm_AlgebraicCurve_ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable
import Theorems.Thm_AlgebraicCurve_ell_le_degree_add_ellZero
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace
import Theorems.Thm_AlgebraicCurve_finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental
import Theorems.Thm_ModularCurve_two_mul_genusFF_x1FunctionFieldC_add_natCard_doubleCoset_eq_index_add_two
import Theorems.Thm_ModularCurve_finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed
import Theorems.Thm_CongruenceSubgroup_index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul
import Theorems.Thm_ModularCurve_exists_isIntegralQExp_linearIndependent_intSeriesC_gamma1_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
p2m_attr_erase "instance" "CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy TateModule.instModule TateModule.instSMul GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg"
p2m_attr_erase "instance" "KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul"
p2m_attr_erase "simp" "KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂"
p2m_attr_erase "simp" "Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_towerInclBar"
p2m_attr_erase "simp" "ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec"

set_option autoImplicit false
set_option maxHeartbeats 8000000

open AlgebraicCurve ModularCurve CongruenceSubgroup ModularForm UpperHalfPlane
open scoped MatrixGroups ModularForm IntermediateField

namespace E97cCover

theorem intSeriesC_pow (K : Type) [Field K] (q : PowerSeries ℤ) (n : ℕ) :
    intSeriesC K (q ^ n) = intSeriesC K q ^ n := by
  induction n with
  | zero => simp [intSeriesC]
  | succ n ih => rw [pow_succ, intSeriesC_mul, ih, pow_succ]

theorem intSeriesC_delta_ne_zero (κ : Type) [Field κ] : intSeriesC κ (PowerSeries.X * dedekindEtaUnit) ≠ 0 := by
  rw [intSeriesC_mul]
  refine mul_ne_zero ?_ ?_
  · rw [intSeriesC, PowerSeries.map_X, HahnSeries.ofPowerSeries_X]
    exact HahnSeries.single_ne_zero one_ne_zero
  · intro h0
    have h1 := HahnSeries.ofPowerSeries_injective (h0.trans (map_zero _).symm)
    have h2 := congrArg (PowerSeries.coeff 0) h1
    rw [PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_dedekindEtaUnit,
      map_one, map_zero] at h2
    exact one_ne_zero h2

section Ord
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_algebraMap {c : K} (hc : c ≠ 0) : v.ord (algebraMap K F c) = 0 := by
  have hmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hmem' : algebraMap K F c⁻¹ ∈ v.toValuationSubring := v.algebraMap_mem' c⁻¹
  let u : v.toValuationSubringˣ :=
    ⟨⟨algebraMap K F c, hmem⟩, ⟨algebraMap K F c⁻¹, hmem'⟩,
      Subtype.ext (by simp [hc]), Subtype.ext (by simp [hc])⟩
  exact v.ord_coe_unit u

theorem ord_neg (f : F) : v.ord (-f) = v.ord f := by
  simp only [Place.ord, Valuation.map_neg]

theorem ord_add_eq_of_lt {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (h : v.ord f < v.ord g) :
    v.ord (f + g) = v.ord f := by
  simp only [Place.ord] at h ⊢
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hlt : v.adicValuation g < v.adicValuation f := by
    rw [← WithZero.log_lt_log hg' hf']
    omega
  rw [Valuation.map_add_eq_of_lt_left _ hlt]

theorem min_ord_le_ord_add {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) (hfg : f + g ≠ 0) :
    min (v.ord f) (v.ord g) ≤ v.ord (f + g) := by
  simp only [Place.ord]
  have h := v.adicValuation.map_add f g
  have hf' := v.adicValuation_ne_zero hf
  have hg' := v.adicValuation_ne_zero hg
  have hfg' := v.adicValuation_ne_zero hfg
  rcases le_max_iff.mp h with h1 | h1
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation f) :=
      (WithZero.log_le_log hfg' hf').mpr h1
    omega
  · have : WithZero.log (v.adicValuation (f + g)) ≤ WithZero.log (v.adicValuation g) :=
      (WithZero.log_le_log hfg' hg').mpr h1
    omega

theorem not_ord_pos_of_ne (f : F) {a b : K} (hab : a ≠ b)
    (ha : 0 < v.ord (f - algebraMap K F a)) (hb : 0 < v.ord (f - algebraMap K F b)) : False := by
  have hfa : f - algebraMap K F a ≠ 0 := by
    intro h; rw [h, Place.ord_zero] at ha; exact lt_irrefl _ ha
  have hfb : -(f - algebraMap K F b) ≠ 0 := by
    intro h; rw [neg_eq_zero] at h; rw [h, Place.ord_zero] at hb; exact lt_irrefl _ hb
  have heq : (f - algebraMap K F a) + -(f - algebraMap K F b) = algebraMap K F (b - a) := by
    rw [map_sub]; ring
  have hne : (f - algebraMap K F a) + -(f - algebraMap K F b) ≠ 0 := by
    rw [heq]; exact (map_ne_zero _).mpr (sub_ne_zero.mpr hab.symm)
  have h := min_ord_le_ord_add v hfa hfb hne
  rw [heq, ord_algebraMap v (sub_ne_zero.mpr hab.symm), ord_neg] at h
  rcases min_le_iff.mp h with h | h <;> omega

end Ord

section Ord2
variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem ord_pow {f : F} (hf : f ≠ 0) (n : ℕ) : v.ord (f ^ n) = n * v.ord f := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Place.ord_mul v (pow_ne_zero n hf) hf, ih]; push_cast; ring

end Ord2

theorem neg_ediv_le_of_mul_ge {a n : ℤ} (m : ℤ) (hm : 0 < m) (h : -a ≤ m * n) : -(a / m) ≤ n := by
  have h1 : a / m * m ≤ a := Int.ediv_mul_le a hm.ne'
  have h2 : a < (a / m + 1) * m := Int.lt_ediv_add_one_mul_self a hm
  nlinarith

theorem twelve_dvd
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (T : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hT : (T : LaurentSeries κ) =
      intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (hx : 0 ≤ x.ord J) :
    (12 : ℤ) ∣ x.ord T := by
  classical

  obtain ⟨t, ht, htr, hfd, hsep⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM κ
  have htJ : t = J := Subtype.ext (ht.trans hJ.symm)
  subst htJ
  haveI := hfd
  haveI := hsep
  haveI : IsCurveOver κ ↥(ModularCurve.x1FunctionFieldC κ M) := AlgebraicCurve.isCurveOver_of_transcendental htr hfd hsep
  obtain ⟨hL0, hell0⟩ :=
    AlgebraicCurve.finiteDimensional_lSpace_zero_and_ell_zero_eq_one_of_isAlgClosed_of_transcendental κ
      (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd
  haveI := hL0

  have hGENK := ModularCurve.two_mul_genusFF_x1FunctionFieldC_add_natCard_doubleCoset_eq_index_add_two p M hM hpM κ
  obtain ⟨h3, h2⟩ :=
    CongruenceSubgroup.index_gamma1_sup_zpowers_neg_one_eq_three_mul_natCard_doubleCoset_and_eq_two_mul M hM
  have hDEGK := ModularCurve.finrank_adjoin_x1FunctionFieldC_eq_index_gamma1_sup_of_isAlgClosed p M hM hpM κ t ht
  have hnpos : 0 < Module.finrank ↥κ⟮(t : ↥(ModularCurve.x1FunctionFieldC κ M))⟯ ↥(ModularCurve.x1FunctionFieldC κ M) := Module.finrank_pos
  set idx : ℕ := (CongruenceSubgroup.Gamma1 M ⊔ Subgroup.zpowers (-1 : SL(2, ℤ))).index with hidx
  set N₃ : ℕ := Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        (Subgroup.zpowers (ModularGroup.S * ModularGroup.T) : Set SL(2, ℤ))) with hN₃
  set N₂ : ℕ := Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        (Subgroup.zpowers ModularGroup.S : Set SL(2, ℤ))) with hN₂
  set c : ℕ := Nat.card (DoubleCoset.Quotient (CongruenceSubgroup.Gamma1 M : Set SL(2, ℤ))
        ((Subgroup.zpowers ModularGroup.T ⊔ Subgroup.zpowers (-1) : Subgroup SL(2, ℤ)) : Set SL(2, ℤ))) with hc
  set gκ : ℕ := genusFF κ ↥(ModularCurve.x1FunctionFieldC κ M) with hgκ

  have hG : ((2 * gκ + N₃ + N₂ + c : ℕ) : ℤ) = ((idx + 2 : ℕ) : ℤ) := by exact_mod_cast hGENK
  have h3' : ((idx : ℕ) : ℤ) = ((3 * N₃ : ℕ) : ℤ) := by exact_mod_cast h3
  have h2' : ((idx : ℕ) : ℤ) = ((2 * N₂ : ℕ) : ℤ) := by exact_mod_cast h2
  have hidx1 : (1 : ℤ) ≤ idx := by rw [← hDEGK]; exact_mod_cast hnpos
  push_cast at hG h3' h2'
  have hgen : 12 * (gκ : ℤ) = idx - 6 * c + 12 := by omega
  have hslack : (36 : ℤ) ≤ 4 * idx + 18 * c := by omega

  have hΔk : ∀ k : ℕ, intSeriesC κ ((PowerSeries.X * ModularCurve.dedekindEtaUnit) ^ k) ≠ 0 := fun k => by
    rw [intSeriesC_pow]; exact pow_ne_zero _ (intSeriesC_delta_ne_zero κ)
  have hp1k : ∀ k : ℕ, intSeriesC κ (w.series ^ k) ≠ 0 := fun k => by
    rw [intSeriesC_pow]; exact pow_ne_zero _ w.intSeriesC_ne_zero
  obtain ⟨T', hTexp, hTord⟩ := ModularCurve.exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
    p κ M hpM t ht 1 w.form w.series w.isIntegralQExp w.intSeriesC_ne_zero
  have hTT : T = T' := Subtype.ext (by rw [hTexp, hT, pow_one])
  subst hTT
  have coe_ne : ∀ {u : ↥(ModularCurve.x1FunctionFieldC κ M)}, ((u : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) ≠ 0 → u ≠ 0 := by
    intro u hu h; apply hu; rw [h]; rfl
  have hT0 : T ≠ 0 := coe_ne (by rw [hTexp]; exact div_ne_zero (hp1k 12) (hΔk 1))
  have hTord' : ∀ v : Place κ ↥(ModularCurve.x1FunctionFieldC κ M), min 0 (v.ord t) ≤ v.ord T := by
    intro v; have := hTord v; simpa using this

  obtain ⟨E, hE, hEdeg⟩ := AlgebraicCurve.exists_divisor_eq_floor_and_mul_degree_le_of_min_ord_le κ
    (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd T hT0 hTord' 7 12 (by norm_num)
  have hE0 : 0 ≤ E := by
    intro v
    rw [Finsupp.coe_zero, Pi.zero_apply, hE v]
    exact Int.ediv_nonneg (mul_nonneg (by norm_num) (sub_nonneg.mpr (hTord' v))) (by norm_num)

  obtain ⟨d, gf, pg, hint, hli, hdim⟩ :=
    ModularCurve.exists_isIntegralQExp_linearIndependent_intSeriesC_gamma1_of_le p κ M hM hpM 7 (by norm_num)

  have hTmem : ModularGroup.T ∈ Gamma1 M := by
    rw [Gamma1_mem]; simp [ModularGroup.T]
  have h1per : (1 : ℝ) ∈ ((Gamma1 M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, hTmem, ?_⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [ModularGroup.T, Matrix.GeneralLinearGroup.upperRightHom]
  have hpow7 : IsIntegralQExp (w.form.pow 7) (w.series ^ 7) := by
    have hf := w.isIntegralQExp
    unfold IsIntegralQExp at hf ⊢
    rw [map_pow, hf, ModularForm.qExpansion_pow one_pos h1per]
  let W7 : ModularForm (Gamma1 M) ((7 : ℕ) : ℤ) := ModularForm.mcast (by norm_num) (w.form.pow 7)
  have hW7 : IsIntegralQExp W7 (w.series ^ 7) := by
    unfold IsIntegralQExp at hpow7 ⊢
    rw [coe_mcast]
    exact hpow7
  have hg0 : ∀ i, intSeriesC κ (pg i) ≠ 0 := fun i => hli.ne_zero i

  let f : Fin d → ↥(ModularCurve.x1FunctionFieldC κ M) := fun i =>
    ⟨intSeriesC κ (pg i) / intSeriesC κ (w.series ^ 7),
      ModularCurve.div_mem_qExpFunctionFieldC (gf i) W7 (hint i) hW7 (hp1k 7)⟩
  have hfexp : ∀ i, ((f i : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = intSeriesC κ (pg i) / intSeriesC κ (w.series ^ 7) :=
    fun _ => rfl
  have hf0 : ∀ i, f i ≠ 0 := fun i => coe_ne (by rw [hfexp]; exact div_ne_zero (hg0 i) (hp1k 7))

  choose Tg hTgexp hTgord using fun i => ModularCurve.exists_coe_eq_div_pow_and_mul_min_ord_le_ord_x1FunctionFieldC
    p κ M hpM t ht 7 (gf i) (pg i) (hint i) (hg0 i)
  have hTg0 : ∀ i, Tg i ≠ 0 := fun i => coe_ne (by
    rw [hTgexp, intSeriesC_pow]; exact div_ne_zero (pow_ne_zero _ (hg0 i)) (hΔk 7))

  have hrel : ∀ i, f i ^ 12 * T ^ 7 = Tg i := by
    intro i
    apply Subtype.ext
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, SubmonoidClass.coe_pow, hfexp, hTexp, hTgexp]
    simp only [intSeriesC_pow, pow_one]
    have hb := w.intSeriesC_ne_zero
    have hD := intSeriesC_delta_ne_zero κ
    field_simp

  have hordrel : ∀ i (v : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)), 12 * v.ord (f i) + 7 * v.ord T = v.ord (Tg i) := by
    intro i v
    rw [← hrel i, Place.ord_mul v (pow_ne_zero 12 (hf0 i)) (pow_ne_zero 7 hT0), ord_pow v (hf0 i), ord_pow v hT0]
    push_cast; ring

  have hfL : ∀ i, (f i : ↥(ModularCurve.x1FunctionFieldC κ M)) ∈ LSpace E := by
    intro i
    rw [mem_lSpace_iff_ord]
    refine Or.inr fun v => ?_
    rw [hE v]
    have h1 := hordrel i v
    have h2 := hTgord i v
    apply neg_ediv_le_of_mul_ge 12 (by norm_num)
    push_cast at h1 h2 ⊢
    nlinarith [h1, h2, min_le_left (0 : ℤ) (v.ord t), hTord' v]

  have hfli : LinearIndependent κ f := by
    rw [linearIndependent_iff']
    intro s cf hs i hi
    refine linearIndependent_iff'.mp hli s cf ?_ i hi

    have hs' : ∑ j ∈ s, algebraMap κ ↥(ModularCurve.x1FunctionFieldC κ M) (cf j) * f j = 0 := by
      rw [← hs]; exact Finset.sum_congr rfl fun j _ => (Algebra.smul_def _ _).symm
    have h1 : ∑ j ∈ s, algebraMap κ (LaurentSeries κ) (cf j) * ((f j : ↥(ModularCurve.x1FunctionFieldC κ M)) : LaurentSeries κ) = 0 := by
      have := congrArg (fun u : ↥(ModularCurve.x1FunctionFieldC κ M) => (u : LaurentSeries κ)) hs'
      simp only [AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul, ZeroMemClass.coe_zero] at this
      exact this
    have h2 := congrArg (fun z : LaurentSeries κ => z * intSeriesC κ (w.series ^ 7)) h1
    simp only [Finset.sum_mul, zero_mul, mul_assoc] at h2
    rw [← h2]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hfexp, div_mul_cancel₀ _ (hp1k 7), HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
      HahnSeries.ofPowerSeries_C, HahnSeries.C_mul_eq_smul]

  haveI : ∀ D : Divisor κ ↥(ModularCurve.x1FunctionFieldC κ M), FiniteDimensional κ ↥(LSpace D) := fun D => AlgebraicCurve.finiteDimensional_lSpace D
  have hdle : d ≤ ell E := by
    have hli' : LinearIndependent κ (fun i => (⟨f i, hfL i⟩ : ↥(LSpace E))) :=
      (LinearIndependent.of_comp (LSpace E).subtype (by exact hfli))
    simpa using hli'.fintype_card_le_finrank
  have hub : (ell E : ℤ) ≤ E.degree + 1 := by
    have := AlgebraicCurve.ell_le_degree_add_ellZero (K := κ) (F := ↥(ModularCurve.x1FunctionFieldC κ M)) hE0
    rw [hell0] at this; exact_mod_cast this
  have hdimZ : 6 * (idx : ℤ) + 6 * c ≤ 12 * d := by
    have := hdim; zify at this; simpa using this
  have hEdegZ : 12 * E.degree ≤ 7 * (idx : ℤ) := by
    have h := hEdeg
    rw [hDEGK] at h
    exact_mod_cast h
  have hdegge : 2 * (gκ : ℤ) - 1 ≤ E.degree - 1 := by
    have hdle' : (d : ℤ) ≤ ell E := by exact_mod_cast hdle
    nlinarith [hdle', hub, hdimZ, hgen, hslack]

  have hRRE := AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable κ
    (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd hsep E (by linarith)

  have hsq : (ell E : ℤ) = d ∧ 12 * E.degree = 7 * (idx : ℤ) := by
    have hdle' : (d : ℤ) ≤ ell E := by exact_mod_cast hdle
    constructor <;> nlinarith [hRRE, hEdegZ, hdimZ, hgen, hdle']

  have hexact := AlgebraicCurve.mul_apply_eq_mul_sub_min_ord_of_eq_floor_of_mul_degree_eq_finrank κ
    (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd T hT0 hTord' 7 12 (by norm_num) E hE (by rw [hDEGK]; exact_mod_cast hsq.2)

  set E' : Divisor κ ↥(ModularCurve.x1FunctionFieldC κ M) := E - Finsupp.single x 1 with hE'
  have hE'v : ∀ v, E' v = E v - if v = x then 1 else 0 := by
    intro v; simp [hE', Finsupp.single_apply, eq_comm]
  have hE'deg : E'.degree = E.degree - 1 := by
    rw [hE', map_sub, Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed x]; simp
  have hRRE' := AlgebraicCurve.ell_eq_degree_add_one_sub_genusFF_of_isAlgClosed_of_isSeparable κ
    (t : ↥(ModularCurve.x1FunctionFieldC κ M)) htr hfd hsep E' (by rw [hE'deg]; exact hdegge)
  have hellE' : (ell E' : ℤ) = d - 1 := by rw [hRRE', hE'deg]; linarith [hRRE, hsq.1]

  obtain ⟨i, hi⟩ : ∃ i, (f i : ↥(ModularCurve.x1FunctionFieldC κ M)) ∉ LSpace E' := by
    by_contra hall
    push Not at hall
    have hli' : LinearIndependent κ (fun i => (⟨f i, hall i⟩ : ↥(LSpace E'))) :=
      (LinearIndependent.of_comp (LSpace E').subtype (by exact hfli))
    have h := hli'.fintype_card_le_finrank
    simp only [Fintype.card_fin] at h
    have h' : (d : ℤ) ≤ ell E' := by exact_mod_cast h
    linarith [hellE']

  have hordx : x.ord (f i) = -E x := by
    rw [mem_lSpace_iff_ord, not_or, not_forall] at hi
    obtain ⟨-, ⟨v, hv⟩⟩ := hi
    have hvE : -E v ≤ v.ord (f i) := ((mem_lSpace_iff_ord.mp (hfL i)).resolve_left (hf0 i)) v
    rw [hE'v] at hv
    by_cases hvx : v = x
    · subst hvx; simp at hv; omega
    · simp [hvx] at hv; exact absurd hvE (not_le.mpr hv)

  have hA : min 0 (x.ord t) = 0 := min_eq_left hx
  have hordTg : x.ord (Tg i) = 0 := by
    have h1 := hordrel i x
    have h2 := hexact x
    rw [hA, sub_zero] at h2
    have h3 := hE x
    rw [hA, sub_zero] at h3
    push_cast at h1 h2 h3
    omega

  have h := hordrel i x
  rw [hordTg] at h
  omega

end E97cCover

open E97cCover in
theorem solution
    (p : ℕ) [Fact p.Prime] (κ : Type) [Field κ] [CharP κ p] [IsAlgClosed κ] [DecidableEq κ]
    (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (w : ModularCurve.IntegralWeightOneForm κ M)
    (J : ↥(ModularCurve.x1FunctionFieldC κ M)) (hJ : (J : LaurentSeries κ) = ModularCurve.jqModC κ)
    (T : ↥(ModularCurve.x1FunctionFieldC κ M))
    (hT : (T : LaurentSeries κ) =
      intSeriesC κ (w.series ^ 12) / intSeriesC κ (PowerSeries.X * ModularCurve.dedekindEtaUnit))
    (x : Place κ ↥(ModularCurve.x1FunctionFieldC κ M)) (hx : 0 ≤ x.ord J) :
    (12 : ℤ) ∣ x.ord T :=
  twelve_dvd p κ M hM hpM w J hJ T hT x hx

end S_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_twelve_dvd_ord_of_coe_eq_div_of_ord_nonneg_x1FunctionFieldC (solution)
