-- Prove2me | solution 1 for ModularCurve.XOne.exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/ba18d27a-155b-5693-be7c-c8194fb4b518

import Mathlib
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_PlacesOverDVR
import Definitions.Def_AlgebraicCurve_CurveModelConstruction
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_exists_gaussValuationSubring_laurentBaseChange_x1FunctionField
import Theorems.Thm_ValuationSubring_exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries
import Theorems.Thm_ModularCurve_XOneP_gaussReduction_mem_x1FunctionFieldC_of_x1
import Theorems.Thm_ModularCurve_exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand
import Theorems.Thm_ModularCurve_XOne_chartRing_le_adjoin_gaussReductions_chartAlg_x1
import Theorems.Thm_ModularCurve_exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOne_exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC
p2m_attr_erase "instance" "GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instFinite CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex TateModule.instModule TateModule.instSMul CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.IntegralWeightOneForm.mk.injEq ModularCurve.IntegralWeightOneForm.mk.sizeOf_spec ModularCurve.IgusaCover.IgusaDiamondData.mk.sizeOf_spec ModularCurve.IgusaCover.coe_incl ModularCurve.IgusaCover.IgusaDiamondData.mk.injEq AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec"
p2m_attr_erase "simp" "ResidualGaloisRep.Equiv.mk.injEq CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.JH.torsionGaloisRep_apply TateModule.smul_apply TateModule.coe_mulP TateModule.proj_apply TateModule.coe_add TateModule.coe_sub WeierstrassCurve.tateModuleRepOfBasis_V TateModule.coe_zero TateModule.rep_apply WeierstrassCurve.tateModuleRep_V WeierstrassCurve.tateModuleRepOfBasis_ρ_apply GaloisRep.padicIntToRingLevel_apply TateModule.coe_neg WeierstrassCurve.tateModuleRep_ρ_apply ModularCurve.qExpandAlgHomC_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec"
p2m_attr_erase "simp" "CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen"
p2m_attr_erase "simp" "HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero"
p2m_attr_erase "simp" "ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun"
p2m_attr_erase "simp" "KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁"
p2m_attr_erase "simp" "TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply"
p2m_attr_erase "simp" "WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve AlgebraicCurve.TwoChartIntegralModel
open scoped TensorProduct
namespace FloorAux

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem evalAt_mul (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f * g) = v.evalAt f * v.evalAt g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_mul, v.algebraMap_evalAt hv (mul_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_mul]
  rfl

theorem evalAt_add (v : Place K F) (hv : v.IsRational) {f g : F}
    (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply (algebraMap K v.ResidueField).injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg,
    ← map_add]
  rfl

theorem evalAt_algebraMap (v : Place K F) (a : K) : v.evalAt (algebraMap K F a) = a := by
  rw [v.evalAt_of_mem (v.algebraMap_mem' a)]
  have ha : (⟨algebraMap K F a, v.algebraMap_mem' a⟩ : v.toValuationSubring)
      = algebraMap K v.toValuationSubring a := Subtype.ext (v.coe_algebraMap a).symm
  rw [ha, ← IsLocalRing.ResidueField.algebraMap_eq,
    ← IsScalarTower.algebraMap_apply K v.toValuationSubring v.ResidueField,
    v.residueInv_algebraMap]

theorem evalAt_eq_zero_iff (v : Place K F) (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring) :
    v.evalAt f = 0 ↔ (⟨f, hf⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal v.toValuationSubring := by
  rw [← (algebraMap K v.ResidueField).injective.eq_iff, v.algebraMap_evalAt hv hf, map_zero,
    IsLocalRing.residue_eq_zero_iff]

noncomputable def evalRingHom (v : Place K F) (hv : v.IsRational) (S : Subring F)
    (hS : ∀ s ∈ S, s ∈ v.toValuationSubring) : S →+* K where
  toFun s := v.evalAt s
  map_one' := by simp
  map_mul' a b := evalAt_mul v hv (hS _ a.2) (hS _ b.2)
  map_zero' := by
    have := evalAt_algebraMap v (0 : K)
    rwa [map_zero] at this
  map_add' a b := evalAt_add v hv (hS _ a.2) (hS _ b.2)

@[scoped simp] theorem evalRingHom_apply (v : Place K F) (hv : v.IsRational) (S : Subring F)
    (hS : ∀ s ∈ S, s ∈ v.toValuationSubring) (s : S) : evalRingHom v hv S hS s = v.evalAt s := rfl

theorem place_eq_of_center_eq {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R F] [IsFractionRing R F]
    (v w : Place K F) (hv : ∀ r : R, algebraMap R F r ∈ v.toValuationSubring)
    (hw : ∀ r : R, algebraMap R F r ∈ w.toValuationSubring)
    (h : Place.center R v hv = Place.center R w hw) : v = w := by
  apply Place.ext
  rw [v.toValuationSubring_eq_of_forall_mem hv, w.toValuationSubring_eq_of_forall_mem hw]
  have : Place.centerHeightOneSpectrum R v hv = Place.centerHeightOneSpectrum R w hw :=
    IsDedekindDomain.HeightOneSpectrum.ext h
  rw [this]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (x : PowerSeries R) :
    ModularCurve.coeffMap f (HahnSeries.ofPowerSeries ℤ R x) = HahnSeries.ofPowerSeries ℤ S (PowerSeries.map f x) := by
  ext i
  rw [ModularCurve.coeffMap_coeff]
  change f (((x : PowerSeries R) : LaurentSeries R).coeff i) = ((PowerSeries.map f x : PowerSeries S) : LaurentSeries S).coeff i
  rw [PowerSeries.coeff_coe, PowerSeries.coeff_coe]
  split_ifs <;> simp [PowerSeries.coeff_map]

theorem coeffMap_intSeriesC {R S : Type*} [Field R] [Field S] (f : R →+* S) (x : PowerSeries ℤ) :
    ModularCurve.coeffMap f (ModularCurve.intSeriesC R x) = ModularCurve.intSeriesC S x := by
  unfold ModularCurve.intSeriesC
  rw [coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map f), ← PowerSeries.map_comp, RingHom.eq_intCast' (f.comp (Int.castRingHom R))]

theorem coeffMap_mem_x1FunctionFieldC {R S : Type*} [Field R] [Field S] (f : R →+* S) (M : ℕ)
    {z : LaurentSeries R} (hz : z ∈ ModularCurve.x1FunctionFieldC R M) :
    ModularCurve.coeffMap f z ∈ ModularCurve.x1FunctionFieldC S M := by
  change z ∈ Subfield.closure (Set.range (algebraMap R (LaurentSeries R)) ∪
    ModularCurve.intFormRatiosC R (CongruenceSubgroup.Gamma1 M)) at hz
  induction hz using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨c, rfl⟩ | ⟨k, F, G, pf, pg, hF, hG, hg0, rfl⟩
      · rw [ModularCurve.algebraMap_laurentSeries_eq_single, ModularCurve.coeffMap_single,
          ← ModularCurve.algebraMap_laurentSeries_eq_single]
        exact IntermediateField.algebraMap_mem _ _
      · rw [map_div₀, coeffMap_intSeriesC, coeffMap_intSeriesC]
        refine ModularCurve.div_mem_qExpFunctionFieldC F G hF hG ?_
        intro h0
        apply hg0
        apply (ModularCurve.coeffMap f).injective
        rw [coeffMap_intSeriesC, h0, map_zero]
  | one => rw [map_one]; exact one_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx
  | inv x _ hx => rw [map_inv₀]; exact inv_mem hx
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

end FloorAux
p2m_reactivate "P2MW.S_ModularCurve_XOne_exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC.FloorAux"

open FloorAux in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K' : IntermediateField L (LaurentSeries L))
    (hK' : K' = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField M))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K'] [IsScalarTower A L ↥K']
    (j' : ↥K') (hj' : ((j' : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j' ≠ 0)]
    (Ω₀ : Type) [Field Ω₀] [CharP Ω₀ p] [IsAlgClosed Ω₀] [DecidableEq Ω₀] [Algebra A Ω₀]
    (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) (hjbar : (jbar : LaurentSeries Ω₀) = ModularCurve.jqModC Ω₀) :
    ∃ Φ : {v : AlgebraicCurve.Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (jbar : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} →
          (Ω₀ ⊗[A] ↥(chartAlgFin A (↥K') j') →ₐ[Ω₀] Ω₀),
      Function.Injective Φ ∧
      ∀ v, Φ v (1 ⊗ₜ jChartFin A (↥K') j') = v.1.evalAt jbar := by
  classical

  have hp0 : (p : A) ≠ 0 := fun h => by
    have := congrArg (algebraMap A L) h
    rw [map_natCast, map_zero] at this
    exact (Fact.out : p.Prime).ne_zero (by exact_mod_cast this)
  have hker : RingHom.ker (algebraMap A Ω₀) = IsLocalRing.maximalIdeal A := by
    have hpker : (p : A) ∈ RingHom.ker (algebraMap A Ω₀) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    have hne : RingHom.ker (algebraMap A Ω₀) ≠ ⊥ := fun h => hp0 (by rw [h] at hpker; exact hpker)
    haveI : (RingHom.ker (algebraMap A Ω₀)).IsPrime := RingHom.ker_isPrime _
    exact IsLocalRing.eq_maximalIdeal (IsPrime.to_maximal_ideal hne)
  let ι : IsLocalRing.ResidueField A →+* Ω₀ :=
    Ideal.Quotient.lift _ (algebraMap A Ω₀) (fun a ha => by rwa [← hker] at ha)
  have hι : ∀ a, ι (IsLocalRing.residue A a) = algebraMap A Ω₀ a := fun a => rfl

  obtain ⟨W₀, hW₀, hAW, hmaxW, hpolW, hnu⟩ :=
    ModularCurve.exists_gaussValuationSubring_laurentBaseChange_x1FunctionField M L K' hK' A j' hj'
  obtain ⟨red, hred, hkerred⟩ :=
    ValuationSubring.exists_ringHom_laurentSeries_residueField_of_forall_mem_iff_exists_powerSeries L K' A W₀ hW₀ hnu

  obtain ⟨⟨xj, yj, hyj, hxyj, hjred⟩, -⟩ :=
    ModularCurve.exists_powerSeries_coeffEmb_jq_mul_eq_and_div_eq_jqModC_and_qExpand p L A hAp
  have hjW : j' ∈ W₀ := (hW₀ j').mpr ⟨xj, yj, hyj, by rw [hj']; exact hxyj⟩

  let S : Subalgebra A ↥K' :=
    { W₀.toSubring with
      algebraMap_mem' := fun a => hAW a }
  have hSmem : ∀ x : ↥K', x ∈ S ↔ x ∈ W₀ := fun _ => Iff.rfl
  have hadjS : Algebra.adjoin A ({j'} : Set ↥K') ≤ S :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr ((hSmem _).mpr hjW))
  have hInt : W₀.valuation.Integers ↥S :=
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => (W₀.valuation_le_one_iff _).mpr x.2
      exists_of_le_one := fun r hr => ⟨⟨r, (W₀.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  have hfinW : ∀ b : ↥(chartAlgFin A (↥K') j'), (b : ↥K') ∈ W₀ := fun b => by
    have hb : IsIntegral (Algebra.adjoin A ({j'} : Set ↥K')) (b : ↥K') := b.2
    have hbS : IsIntegral ↥S (b : ↥K') := by
      have := hb.map_of_comp_eq (Subalgebra.inclusion hadjS).toRingHom (RingHom.id ↥K') (by ext a; rfl)
      simpa using this
    exact (W₀.valuation_le_one_iff _).mp (hInt.isIntegral_iff_v_le_one.mp hbS)

  obtain ⟨t, ht, htr, hfd, hsep⟩ :=
    ModularCurve.exists_coe_eq_jqModC_and_transcendental_and_finiteDimensional_and_isSeparable_x1FunctionFieldC p M hM hpM Ω₀
  have htj : t = jbar := Subtype.ext (by rw [ht, hjbar])
  subst htj
  haveI := hfd
  haveI := hsep
  haveI hCurve : IsCurveOver Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) :=
    AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable Ω₀ _ t htr hfd hsep
  have hrat : ∀ v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M), v.IsRational := fun v => by
    haveI : Module.Finite Ω₀ v.ResidueField := IsCurveOver.finiteResidue v
    haveI : Algebra.IsIntegral Ω₀ v.ResidueField := Algebra.IsIntegral.of_finite Ω₀ _
    exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω₀) (K := v.ResidueField)).surjective

  open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel in
  haveI hDed : IsDedekindDomain ↥(AlgebraicCurve.CurveModel.chartRing Ω₀ ({(t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M))} :
      Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))) :=
    IsIntegralClosure.isDedekindDomain (Algebra.adjoin Ω₀ ({t} : Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M)))
      ↥(IntermediateField.adjoin Ω₀ ({t} : Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))) ↥(ModularCurve.x1FunctionFieldC Ω₀ M) _
  open scoped IntermediateField.algebraAdjoinAdjoin AlgebraicCurve.CurveModel in
  haveI hFrac : IsFractionRing ↥(AlgebraicCurve.CurveModel.chartRing Ω₀ ({(t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M))} :
      Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))) ↥(ModularCurve.x1FunctionFieldC Ω₀ M) :=
    IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin Ω₀ ({t} : Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M)))
      ↥(IntermediateField.adjoin Ω₀ ({t} : Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))) ↥(ModularCurve.x1FunctionFieldC Ω₀ M) _

  let inclW : ↥(chartAlgFin A (↥K') j') →+* ↥W₀ :=
    ((chartAlgFin A (↥K') j').val.toRingHom).codRestrict W₀ hfinW
  let redA : ↥(chartAlgFin A (↥K') j') →+* LaurentSeries Ω₀ :=
    (ModularCurve.coeffMap ι).comp (red.comp inclW)
  have hιc : ι.comp (IsLocalRing.residue A) = algebraMap A Ω₀ := RingHom.ext hι
  have hredA : ∀ (b : ↥(chartAlgFin A (↥K') j')) (x y : PowerSeries A), y.map (IsLocalRing.residue A) ≠ 0 →
      (((b : ↥K') : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
        = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      redA b = HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
               HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀)) := by
    intro b x y hy hxy
    have h1 := hred (inclW b) x y hy hxy
    show ModularCurve.coeffMap ι (red (inclW b)) = _
    rw [h1, map_div₀, coeffMap_ofPowerSeries, coeffMap_ofPowerSeries, ← RingHom.comp_apply (PowerSeries.map ι),
      ← PowerSeries.map_comp, ← RingHom.comp_apply (PowerSeries.map ι), ← PowerSeries.map_comp, hιc]
  have hredAmem : ∀ b, redA b ∈ ModularCurve.x1FunctionFieldC Ω₀ M := by
    intro b
    obtain ⟨x, y, hy, hxy⟩ := (hW₀ _).mp (hfinW b)
    have h1 := hred (inclW b) x y hy hxy
    have hmem := ModularCurve.XOneP.gaussReduction_mem_x1FunctionFieldC_of_x1 p M hM hpM L ζ hζ K' hK' A hAp hζA
      j' hj' (b : ↥K') x y hy hxy
    show ModularCurve.coeffMap ι (red (inclW b)) ∈ _
    rw [h1]
    exact coeffMap_mem_x1FunctionFieldC ι M hmem
  let redK : ↥(chartAlgFin A (↥K') j') →+* ↥(ModularCurve.x1FunctionFieldC Ω₀ M) := redA.codRestrict _ hredAmem
  have hredK : ∀ b, ((redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) : LaurentSeries Ω₀) = redA b := fun _ => rfl

  have hredKj : redK (jChartFin A (↥K') j') = t := by
    apply Subtype.ext
    rw [hredK, ht]
    have h1 := hred (inclW (jChartFin A (↥K') j')) xj yj hyj (by
      show ((j' : ↥K') : LaurentSeries L) * _ = _
      rw [hj']; exact hxyj)
    show ModularCurve.coeffMap ι (red (inclW _)) = _
    rw [h1, hjred]
    exact ModularCurve.map_jqModC ι

  have hredKA : ∀ a : A, redK (algebraMap A _ a) =
      algebraMap Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) (algebraMap A Ω₀ a) := by
    intro a
    apply Subtype.ext
    rw [hredK]
    have hpres : (((algebraMap A ↥(chartAlgFin A (↥K') j') a : ↥(chartAlgFin A (↥K') j')) : ↥K') : LaurentSeries L) *
        HahnSeries.ofPowerSeries ℤ L ((1 : PowerSeries A).map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L ((PowerSeries.C a).map (algebraMap A L)) := by
      rw [map_one, map_one, mul_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
      show ((algebraMap A ↥K' a : ↥K') : LaurentSeries L) = _
      rw [IsScalarTower.algebraMap_apply A L ↥K']
      exact ModularCurve.algebraMap_laurentSeries_eq_single L (algebraMap A L a)
    rw [hredA _ (PowerSeries.C a) 1 (by rw [map_one]; exact one_ne_zero) hpres,
      map_one, map_one, div_one, PowerSeries.map_C, HahnSeries.ofPowerSeries_C]
    exact (ModularCurve.algebraMap_laurentSeries_eq_single Ω₀ (algebraMap A Ω₀ a)).symm

  have hIntv : ∀ v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M),
      v.toValuationSubring.valuation.Integers ↥v.toValuationSubring := fun v =>
    { hom_inj := Subtype.val_injective
      map_le_one := fun x => (v.toValuationSubring.valuation_le_one_iff _).mpr x.2
      exists_of_le_one := fun r hr => ⟨⟨r, (v.toValuationSubring.valuation_le_one_iff r).mp hr⟩, rfl⟩ }
  let incl : ↥(Algebra.adjoin A ({j'} : Set ↥K')) →ₐ[A] ↥(chartAlgFin A (↥K') j') :=
    Subalgebra.inclusion (adjoin_le_chartAlg A (↥K') {j'})
  letI : Algebra ↥(Algebra.adjoin A ({j'} : Set ↥K')) ↥(chartAlgFin A (↥K') j') := incl.toRingHom.toAlgebra
  haveI : IsScalarTower ↥(Algebra.adjoin A ({j'} : Set ↥K')) ↥(chartAlgFin A (↥K') j') ↥K' :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hbint : ∀ b : ↥(chartAlgFin A (↥K') j'), IsIntegral ↥(Algebra.adjoin A ({j'} : Set ↥K')) b := fun b =>
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom ↥(Algebra.adjoin A ({j'} : Set ↥K')) ↥(chartAlgFin A (↥K') j') ↥K')
      Subtype.val_injective).mp b.2
  have hredKmem : ∀ v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M),
      (t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring → ∀ b, redK b ∈ v.toValuationSubring := by
    intro v hv b
    have hgen : ∀ (r : ↥K') (hr : r ∈ Algebra.adjoin A ({j'} : Set ↥K')), redK (incl ⟨r, hr⟩) ∈ v.toValuationSubring := by
      intro r hr
      induction hr using Algebra.adjoin_induction with
      | mem x hx =>
          have h' : incl ⟨x, Algebra.subset_adjoin hx⟩ = jChartFin A (↥K') j' :=
            Subtype.ext (Set.mem_singleton_iff.mp hx)
          rw [h', hredKj]; exact hv
      | algebraMap a =>
          have : incl ⟨algebraMap A ↥K' a, Subalgebra.algebraMap_mem _ a⟩ = algebraMap A _ a := rfl
          rw [this, hredKA]; exact v.algebraMap_mem' _
      | add x y hx hy ihx ihy =>
          have : (⟨x + y, add_mem hx hy⟩ : ↥(Algebra.adjoin A ({j'} : Set ↥K'))) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
          rw [this, map_add, map_add]; exact add_mem ihx ihy
      | mul x y hx hy ihx ihy =>
          have : (⟨x * y, mul_mem hx hy⟩ : ↥(Algebra.adjoin A ({j'} : Set ↥K'))) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
          rw [this, map_mul, map_mul]; exact mul_mem ihx ihy
    let φ : ↥(Algebra.adjoin A ({j'} : Set ↥K')) →+* ↥v.toValuationSubring :=
      (redK.comp incl.toRingHom).codRestrict v.toValuationSubring (fun r => hgen r.1 r.2)
    have hcomp : (algebraMap ↥v.toValuationSubring ↥(ModularCurve.x1FunctionFieldC Ω₀ M)).comp φ =
        redK.comp (algebraMap ↥(Algebra.adjoin A ({j'} : Set ↥K')) ↥(chartAlgFin A (↥K') j')) := RingHom.ext fun _ => rfl
    have hint : IsIntegral ↥v.toValuationSubring (redK b) := (hbint b).map_of_comp_eq φ redK hcomp
    exact (v.toValuationSubring.valuation_le_one_iff _).mp ((hIntv v).isIntegral_iff_v_le_one.mp hint)

  let ψ : {v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} →
      (↥(chartAlgFin A (↥K') j') →+* Ω₀) := fun v =>
    (evalRingHom v.1 (hrat v.1) v.1.toValuationSubring.toSubring (fun _ h => h)).comp
      (redK.codRestrict v.1.toValuationSubring.toSubring (hredKmem v.1 v.2))
  have hψ : ∀ v b, ψ v b = v.1.evalAt (redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := fun v b => rfl
  let ψA : {v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} →
      (↥(chartAlgFin A (↥K') j') →ₐ[A] Ω₀) := fun v =>
    { ψ v with
      commutes' := fun a => by
        show ψ v (algebraMap A _ a) = algebraMap A Ω₀ a
        rw [hψ, hredKA, evalAt_algebraMap] }
  have hψA : ∀ v b, ψA v b = v.1.evalAt (redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := fun v b => rfl
  let Φ : {v : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) //
            (t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ v.toValuationSubring} →
      (Ω₀ ⊗[A] ↥(chartAlgFin A (↥K') j') →ₐ[Ω₀] Ω₀) := fun v =>
    Algebra.TensorProduct.lift (AlgHom.id Ω₀ Ω₀) (ψA v) (fun _ _ => Commute.all _ _)
  have hΦ : ∀ v a b, Φ v (a ⊗ₜ b) = a * v.1.evalAt (redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := fun v a b => by
    show Algebra.TensorProduct.lift _ _ _ (a ⊗ₜ b) = _
    rw [Algebra.TensorProduct.lift_tmul]
    rfl
  refine ⟨Φ, ?_, fun v => by rw [hΦ, one_mul, hredKj]⟩

  intro v w hvw
  have hagree : ∀ b, v.1.evalAt (redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) =
      w.1.evalAt (redK b : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := fun b => by
    have := congrArg (fun φ => φ ((1 : Ω₀) ⊗ₜ b)) hvw
    simpa only [hΦ, one_mul] using this
  have hRv : ∀ (u : Place Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M)),
      (t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ u.toValuationSubring →
      ∀ r : ↥(AlgebraicCurve.CurveModel.chartRing Ω₀ ({(t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M))} :
        Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))),
      algebraMap _ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) r ∈ u.toValuationSubring :=
    fun u hu r => AlgebraicCurve.CurveModel.chartRing_le_valuationSubring u.toValuationSubring u.algebraMap_mem'
      (Set.singleton_subset_iff.mpr hu) r.2
  have hR₀ : ∀ z ∈ Algebra.adjoin Ω₀ (Set.range redK),
      (z ∈ v.1.toValuationSubring ∧ z ∈ w.1.toValuationSubring) ∧ v.1.evalAt z = w.1.evalAt z := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
        obtain ⟨b, rfl⟩ := hx
        exact ⟨⟨hredKmem _ v.2 b, hredKmem _ w.2 b⟩, hagree b⟩
    | algebraMap a =>
        exact ⟨⟨v.1.algebraMap_mem' a, w.1.algebraMap_mem' a⟩, by rw [evalAt_algebraMap, evalAt_algebraMap]⟩
    | add x y _ _ hx hy =>
        exact ⟨⟨add_mem hx.1.1 hy.1.1, add_mem hx.1.2 hy.1.2⟩, by
          rw [evalAt_add _ (hrat _) hx.1.1 hy.1.1, evalAt_add _ (hrat _) hx.1.2 hy.1.2, hx.2, hy.2]⟩
    | mul x y _ _ hx hy =>
        exact ⟨⟨mul_mem hx.1.1 hy.1.1, mul_mem hx.1.2 hy.1.2⟩, by
          rw [evalAt_mul _ (hrat _) hx.1.1 hy.1.1, evalAt_mul _ (hrat _) hx.1.2 hy.1.2, hx.2, hy.2]⟩
  have hGR : ∀ r : ↥(AlgebraicCurve.CurveModel.chartRing Ω₀ ({(t : ↥(ModularCurve.x1FunctionFieldC Ω₀ M))} :
        Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M))),
      (r : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) ∈ Algebra.adjoin Ω₀ (Set.range redK) := by
    intro r
    have hG := (ModularCurve.XOne.chartRing_le_adjoin_gaussReductions_chartAlg_x1 p M hM hpM L ζ hζ K' hK' A hAp hζA
      j' hj' Ω₀ t ht).1 r r.2
    have hsub : {rr : LaurentSeries Ω₀ |
          ∃ (b : ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin A (↥K') j')) (x y : PowerSeries A),
            y.map (IsLocalRing.residue A) ≠ 0 ∧
            (((b : ↥K') : LaurentSeries L)) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L))
              = HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) ∧
            rr = HahnSeries.ofPowerSeries ℤ Ω₀ (x.map (algebraMap A Ω₀)) /
                  HahnSeries.ofPowerSeries ℤ Ω₀ (y.map (algebraMap A Ω₀))} ⊆
        (ModularCurve.x1FunctionFieldC Ω₀ M).val '' ((Algebra.adjoin Ω₀ (Set.range redK) :
          Subalgebra Ω₀ ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) : Set ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := by
      rintro rr ⟨b, x, y, hy, hxy, rfl⟩
      exact ⟨redK b, Algebra.subset_adjoin ⟨b, rfl⟩, by rw [← hredA b x y hy hxy]; rfl⟩
    have hle := Algebra.adjoin_mono (R := Ω₀) hsub
    rw [Algebra.adjoin_image] at hle
    obtain ⟨z, hz, hzr⟩ := Subalgebra.mem_map.mp (hle hG)
    have : z = (r : ↥(ModularCurve.x1FunctionFieldC Ω₀ M)) := Subtype.ext (by rw [← hzr]; rfl)
    rw [← this]; exact Algebra.adjoin_le Set.Subset.rfl hz
  have hcen : Place.center _ v.1 (hRv v.1 v.2) = Place.center _ w.1 (hRv w.1 w.2) := by
    ext r
    have e1 := evalAt_eq_zero_iff v.1 (hrat _) (hRv v.1 v.2 r)
    have e2 := evalAt_eq_zero_iff w.1 (hrat _) (hRv w.1 w.2 r)
    have e3 : v.1.evalAt (algebraMap _ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) r) =
        w.1.evalAt (algebraMap _ ↥(ModularCurve.x1FunctionFieldC Ω₀ M) r) := (hR₀ _ (hGR r)).2
    rw [Place.mem_center_iff, Place.mem_center_iff, ← e1, ← e2, e3]
  exact Subtype.ext (place_eq_of_center_eq v.1 w.1 (hRv v.1 v.2) (hRv w.1 w.2) hcen)

#print axioms solution

end S_ModularCurve_XOne_exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC
end P2MW
export P2MW.S_ModularCurve_XOne_exists_injective_algHom_tensorProduct_chartAlgFin_apply_eq_evalAt_x1FunctionFieldC (solution)
