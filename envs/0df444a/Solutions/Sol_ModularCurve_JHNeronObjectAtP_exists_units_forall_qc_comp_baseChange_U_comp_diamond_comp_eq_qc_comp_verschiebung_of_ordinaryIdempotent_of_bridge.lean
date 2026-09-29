-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bae8a7a4-6b72-5517-a480-2be424bc19bb

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_PDivisibleGroup_Basic
import Definitions.Def_PDivisibleGroup_Points
import Definitions.Def_EllipticCurve_TateModule
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_HopfAlgebra_CartierDualMap
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_PDivisibleGroup_CartierDuality
import Definitions.Def_AlgebraicGeometry_SchemeFrobenius
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Theorems.Thm_AlgebraicGeometry_comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq
import Theorems.Thm_HopfAlgebra_existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp
import Theorems.Thm_PDivisibleGroup_Tower_eq_of_frobenius_comp_eq_zmodp
import Theorems.Thm_HopfAlgebra_comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp
import Theorems.Thm_AlgebraicGeometry_specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.SemilinearAut.crossGluingMap_apply AlgebraicCurve.GluedPic0.crossMap_mk AlgebraicCurve.SemilinearAut.coe_crossAdmissibleMap AlgebraicCurve.SemilinearAut.crossPerm_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero"
p2m_attr_erase "simp" "ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂"
p2m_attr_erase "simp" "PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one"
p2m_attr_erase "simp" "TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply"
p2m_attr_erase "simp" "ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar"

set_option autoImplicit false

open scoped TensorProduct MatrixGroups
p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing AlgebraicCurve~H1 AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.JZeroNeronObjectAtP"

p2m_open "ModularCurve.XHDRLevel~ΓN"

namespace X1R

open AlgebraicGeometry.Scheme

universe u

theorem natCast_eq_zero_Γ_pullback {G S : Scheme.{u}} (g : G ⟶ S) {k : Type u} [CommRing k]
    (s : Spec (CommRingCat.of k) ⟶ S) {p : ℕ} (hk : (p : k) = 0) :
    (p : Γ(pullback g s, ⊤)) = 0 := by
  have h1 : (p : Γ(Spec (CommRingCat.of k), ⊤)) = 0 := natCast_eq_zero_ΓSpec hk
  have h2 := congrArg (fun t => (pullback.snd g s).appTop.hom t) h1
  simpa using h2

theorem frobenius_fst_comp_eq {G S : Scheme.{u}} (g : G ⟶ S) {k : Type u} [CommRing k]
    (s : Spec (CommRingCat.of k) ⟶ S) (p : ℕ) (hp : p.Prime) (hk : (p : k) = 0)
    (hs : (Spec (CommRingCat.of k)).frobenius p 1 hp (natCast_eq_zero_ΓSpec hk) ≫ s = s)
    (h0 : (p : Γ(pullback g s, ⊤)) = 0) :
    ((pullback g s).frobenius p 1 hp h0 ≫ pullback.fst g s) ≫ g = pullback.snd g s ≫ s := by
  rw [Category.assoc, pullback.condition, ← Category.assoc,
    frobenius_comp (pullback.snd g s) p 1 hp h0 (natCast_eq_zero_ΓSpec hk), Category.assoc, hs]

theorem specMap_comp_lift_eq_lift_comp_relFrob {G S : Scheme.{u}} (g : G ⟶ S)
    {k L A : Type u} [CommRing k] [CommRing L] [CommRing A]
    (s : Spec (CommRingCat.of k) ⟶ S) (ι : Spec (CommRingCat.of L) ⟶ G)
    (a : L →+* A) (c : k →+* A)
    (hsq : (Spec.map (CommRingCat.ofHom a) ≫ ι) ≫ g = Spec.map (CommRingCat.ofHom c) ≫ s)
    (p : ℕ) (hp : p.Prime) (h0 : (p : Γ(pullback g s, ⊤)) = 0)
    (hΦ : ((pullback g s).frobenius p 1 hp h0 ≫ pullback.fst g s) ≫ g = pullback.snd g s ≫ s)
    (hA : (p : A) = 0) (eA : A →+* A)
    (hea : eA.comp a = (powCharRingHom A p 1 hp hA).comp a) (hec : eA.comp c = c) :
    Spec.map (CommRingCat.ofHom eA) ≫
        pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq =
      pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι) (Spec.map (CommRingCat.ofHom c)) hsq ≫
        pullback.lift ((pullback g s).frobenius p 1 hp h0 ≫ pullback.fst g s) (pullback.snd g s) hΦ := by
  apply pullback.hom_ext
  · simp only [Category.assoc, pullback.lift_fst]
    rw [← frobenius_comp_assoc (pullback.lift (Spec.map (CommRingCat.ofHom a) ≫ ι)
          (Spec.map (CommRingCat.ofHom c)) hsq) p 1 hp (natCast_eq_zero_ΓSpec hA) h0,
      pullback.lift_fst, frobenius_Spec p 1 hp hA]
    simp only [← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hea]
  · simp only [Category.assoc, pullback.lift_snd]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hec]

theorem paste3 {C : Type*} [Category C] {X Y : C} {a b c : X ⟶ X} {i : X ⟶ Y} {A B D : Y ⟶ Y}
    (ha : a ≫ i = i ≫ A) (hb : b ≫ i = i ≫ B) (hc : c ≫ i = i ≫ D) :
    (a ≫ b ≫ c) ≫ i = i ≫ A ≫ B ≫ D := by
  simp only [Category.assoc]
  rw [hc, ← Category.assoc b, hb, Category.assoc, ← Category.assoc a, ha, Category.assoc]

theorem pow_eq_of_ringHom_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    (g : ModularCurve.XHDRLevel.R p →+* K) (x : ModularCurve.XHDRLevel.R p) : g x ^ p = g x := by
  have hfix : ∀ z : ZMod p, (algebraMap (ZMod p) K z) ^ p = algebraMap (ZMod p) K z := fun z => by
    rw [← map_pow, ZMod.pow_card]
  have hden : (x : ℚ).den.Coprime p := x.2
  have hx : x * ((x : ℚ).den : ModularCurve.XHDRLevel.R p) = (((x : ℚ).num : ℤ) : ModularCurve.XHDRLevel.R p) := by
    apply Subtype.ext
    push_cast
    exact Rat.mul_den_eq_num (x : ℚ)
  have h1 : g x * algebraMap (ZMod p) K ((x : ℚ).den : ZMod p) = algebraMap (ZMod p) K ((x : ℚ).num : ZMod p) := by
    have := congrArg g hx
    rw [map_mul, map_natCast, map_intCast] at this
    rwa [map_natCast, map_intCast]
  have hne : algebraMap (ZMod p) K ((x : ℚ).den : ZMod p) ≠ 0 := by
    rw [map_ne_zero_iff _ (algebraMap (ZMod p) K).injective, Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have h2 : p ∣ Nat.gcd (x : ℚ).den p := Nat.dvd_gcd hdvd dvd_rfl
    rw [hden.gcd_eq_one, Nat.dvd_one] at h2
    exact hp.out.one_lt.ne' h2
  have h2 : g x = algebraMap (ZMod p) K ((x : ℚ).num : ZMod p) * (algebraMap (ZMod p) K ((x : ℚ).den : ZMod p))⁻¹ :=
    (eq_mul_inv_iff_mul_eq₀ hne).mpr h1
  rw [h2, mul_pow, inv_pow, hfix, hfix]

theorem powChar_comp_ringHom_ratLocalizedAt (p : ℕ) [hp : Fact p.Prime] {K : Type} [Field K] [Algebra (ZMod p) K]
    (hK : (p : K) = 0) (g : ModularCurve.XHDRLevel.R p →+* K) :
    (powCharRingHom K p 1 hp.out hK).comp g = g := by
  ext x
  simp only [RingHom.comp_apply, powCharRingHom_apply, pow_one, pow_eq_of_ringHom_ratLocalizedAt]

theorem ringHom_eq_algebraMap_comp (p : ℕ) [Fact p.Prime] {Rh K : Type} [CommRing Rh] [CommRing K] [Algebra (ZMod p) K]
    (π : Rh →+* ZMod p) (φ : Rh →+* K) (h : ∀ x, π x = 0 → φ x = 0) :
    φ = (algebraMap (ZMod p) K).comp π := by
  ext x
  have hn : π (x - (π x).val) = 0 := by simp
  have h2 := h _ hn
  rw [map_sub, map_natCast, sub_eq_zero] at h2
  rw [RingHom.comp_apply, h2, ← map_natCast (algebraMap (ZMod p) K), ZMod.natCast_zmod_val]

theorem endgame (p : ℕ) [Fact p.Prime] (hc : ℕ)
    (B : ℕ → Type) [∀ v, CommRing (B v)] [∀ v, HopfAlgebra (ZMod p) (B v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (B v)] [∀ v, Module.Finite (ZMod p) (B v)]
    (Gc : ℕ → Type) [∀ v, CommRing (Gc v)] [∀ v, HopfAlgebra (ZMod p) (Gc v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)] [∀ v, Module.Finite (ZMod p) (Gc v)]
    (Ge : ℕ → Type) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (tB : ∀ v, B (v + 1) →ₐc[ZMod p] B v)
    (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (qc : ∀ v, B v →ₐc[ZMod p] Gc v) (σ : ∀ v, Ge v →ₐc[ZMod p] B v)
    (hGc : ∀ v, IsLocalRing (Gc v)) (hGe : ∀ v, IsReduced (Ge v)) (hqc : ∀ v, Function.Surjective (qc v))
    (hkerqc : ∀ v, RingHom.ker (qc v : B v →ₐ[ZMod p] Gc v) =
      Ideal.map (σ v : Ge v →ₐ[ZMod p] B v) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v))))
    (hsc : ∀ v, Function.Surjective (sc v))
    (hrankGc : ∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc))
    (hkerGc : ∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v))
    (hqcs : ∀ v, (qc v).comp (tB v) = (sc v).comp (qc (v + 1)))
    (g g' : ∀ v, B v →ₐc[ZMod p] B v)
    (hg : ∀ v, (tB v).comp (g (v + 1)) = (g v).comp (tB v))
    (hg' : ∀ v, (tB v).comp (g' (v + 1)) = (g' v).comp (tB v))
    (hF : ∀ (v : ℕ) (b : B (v + 1)), qc (v + 1) (g (v + 1) (b ^ p)) = qc (v + 1) (g' (v + 1) (b ^ p))) :
    ∀ v, (qc v : B v →ₐ[ZMod p] Gc v).comp (g v : B v →ₐ[ZMod p] B v) =
      (qc v : B v →ₐ[ZMod p] Gc v).comp (g' v : B v →ₐ[ZMod p] B v) := by
  have H := fun v => (HopfAlgebra.existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp
    p (B v) (Gc v) (Ge v) (qc v) (σ v) (hGc v) (hGe v) (hqc v) (hkerqc v) (g v)).exists
  have H' := fun v => (HopfAlgebra.existsUnique_bialgHom_comp_eq_comp_of_surjective_of_isLocalRing_of_isReduced_of_ker_eq_map_zmodp
    p (B v) (Gc v) (Ge v) (qc v) (σ v) (hGc v) (hGe v) (hqc v) (hkerqc v) (g' v)).exists
  choose e he using H
  choose e' he' using H'
  have he1 : ∀ v b, e v (qc v b) = qc v (g v b) := fun v b => by
    simpa using DFunLike.congr_fun (he v) b
  have he'1 : ∀ v b, e' v (qc v b) = qc v (g' v b) := fun v b => by
    simpa using DFunLike.congr_fun (he' v) b
  have hqcs1 : ∀ v b, qc v (tB v b) = sc v (qc (v + 1) b) := fun v b => by
    simpa using DFunLike.congr_fun (hqcs v) b
  have hg1 : ∀ v b, tB v (g (v + 1) b) = g v (tB v b) := fun v b => by
    simpa using DFunLike.congr_fun (hg v) b
  have hg'1 : ∀ v b, tB v (g' (v + 1) b) = g' v (tB v b) := fun v b => by
    simpa using DFunLike.congr_fun (hg' v) b
  have key := PDivisibleGroup.Tower.eq_of_frobenius_comp_eq_zmodp p hc Gc sc hsc hrankGc hkerGc
    (fun v => (e v : Gc v →ₐ[ZMod p] Gc v)) (fun v => (e' v : Gc v →ₐ[ZMod p] Gc v))
    (fun v => by
      apply AlgHom.ext
      intro a
      obtain ⟨b, rfl⟩ := hqc (v + 1) a
      simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
      rw [he1, ← hqcs1 v (g (v + 1) b), hg1, ← he1, hqcs1])
    (fun v => by
      apply AlgHom.ext
      intro a
      obtain ⟨b, rfl⟩ := hqc (v + 1) a
      simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
      rw [he'1, ← hqcs1 v (g' (v + 1) b), hg'1, ← he'1, hqcs1])
    (fun v a => by
      obtain ⟨b, rfl⟩ := hqc (v + 1) a
      simp only [BialgHom.coe_toAlgHom]
      rw [← map_pow (e (v + 1)), ← map_pow (qc (v + 1)), ← map_pow (e' (v + 1)), ← map_pow (qc (v + 1)),
        he1, he'1, hF])
  intro v
  apply AlgHom.ext
  intro b
  have hk := AlgHom.congr_fun (key v) (qc v b)
  simp only [BialgHom.coe_toAlgHom] at hk
  simp only [AlgHom.comp_apply, BialgHom.coe_toAlgHom]
  rw [← he1, ← he'1, hk]

end X1R

open ModularCurve ModularCurve.JHNeronObjectAtP in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 6400000 in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    [CharP (ResidueField ↥Pl) p] [IsAlgClosed (ResidueField ↥Pl)]
    (hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : ModularCurve.XHDRModelAtP p M H hpM hj)
    (Λ : ModularCurve.JHNeronObjectAtP.LevelData p M H hpM Pl)
    (O : ModularCurve.JHNeronObjectAtP p M H hpM Pl hPl Λ)
    (hrep : Nonempty (RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))))

    (Rh : Type) [CommRing Rh] [IsDomain Rh] [HenselianLocalRing Rh]
    [Algebra Rh (AlgebraicClosure ℚ)] [FaithfulSMul Rh (AlgebraicClosure ℚ)]
    (hRA : ∀ x : Rh, algebraMap Rh (AlgebraicClosure ℚ) x ∈ Pl)
    (hRloc : ∀ x : Rh, x ∈ maximalIdeal Rh ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    [Algebra Rh (ZMod p)]
    (hres : ∀ x : Rh, algebraMap Rh (ZMod p) x = 0 ↔ Pl.valuation (algebraMap Rh (AlgebraicClosure ℚ) x) < 1)

    {h : ℕ} (𝒢 : PDivisibleGroup Rh p h)
    (Δ : 𝒢.Points (AlgebraicClosure ℚ) →+ ModularCurve.JH M H) (hΔ : Function.Injective Δ)
    (hfin : ∀ (v : ℕ) (y : ModularCurve.JH M H), y ∈ O.finPts (p ^ v) ↔
      ∃ x : 𝒢.Point (AlgebraicClosure ℚ) v, Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)) = y)
    (ρh : ModularCurve.XHDRLevel.R p →+* Rh) (ι : ∀ v : ℕ, Spec (CommRingCat.of (𝒢.level v)) ⟶ O.G)
    (hS0 : (algebraMap Rh (AlgebraicClosure ℚ)).comp ρh = algebraMap (ModularCurve.XHDRLevel.R p) (AlgebraicClosure ℚ))
    (hS1 : ∀ v : ℕ, ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh))
    (hS2 : ∀ (v : ℕ) (h1 : ι v ≫ O.g = Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          IsClosedImmersion (pullback.lift (f := O.g) (g := Spec.map (CommRingCat.ofHom ρh)) (ι v)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h1))
    (hS3 : ∀ v : ℕ, ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
    (hS4 : ∀ (v : ℕ) (x : 𝒢.Point (AlgebraicClosure ℚ) v),
          (O.pts (Δ (𝒢.pointsMkAdd (AlgebraicClosure ℚ) v (Additive.ofMul x)))).1 =
            Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] (AlgebraicClosure ℚ)) : 𝒢.level v →+* (AlgebraicClosure ℚ))) ≫ ι v)
    (hS5 : ∀ (v : ℕ) (B : Type) [CommRing B] [Algebra Rh B] (x y : 𝒢.Point B v)
          (hx : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom x : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)))
          (hy : (Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom y : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v) ≫ O.g = (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh))),
          Spec.map (CommRingCat.ofHom ((PDivisibleGroup.Point.toAlgHom (x * y) : 𝒢.level v →ₐ[Rh] B) : 𝒢.level v →+* B)) ≫ ι v =
            (O.L.mul (Spec.map (CommRingCat.ofHom (algebraMap Rh B)) ≫ Spec.map (CommRingCat.ofHom ρh)) ⟨_, hx⟩ ⟨_, hy⟩).1)
    (hS6 : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (𝒢.transition v : 𝒢.level (v + 1) →+* 𝒢.level v)) ≫ ι (v + 1) = ι v)

    (hS8 : ∀ (v : ℕ)
          (h3 : ι v ≫ O.L.schemeNsmul (p ^ v) = (ι v ≫ O.g) ≫ (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1)
          (h4 : pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3 ≫
              (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g) =
            Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v))) ≫ Spec.map (CommRingCat.ofHom ρh)),
          let jv := pullback.lift
            (f := pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
            (g := Spec.map (CommRingCat.ofHom ρh))
            (pullback.lift (f := O.L.schemeNsmul (p ^ v)) (g := (O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) (ι v) (ι v ≫ O.g) h3)
            (Spec.map (CommRingCat.ofHom (algebraMap Rh (𝒢.level v)))) h4
          IsOpenImmersion jv ∧ IsClosedImmersion jv ∧
          ∀ x : ↥(Limits.pullback (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
                  (Spec.map (CommRingCat.ofHom ρh))),
            (pullback.snd (pullback.fst (O.L.schemeNsmul (p ^ v)) ((O.L.one (𝟙 (ModularCurve.JZeroNeronObjectAtP.base p))).1) ≫ O.g)
                (Spec.map (CommRingCat.ofHom ρh))).base x = IsLocalRing.closedPoint Rh →
              x ∈ Set.range jv.base)

    (S : Set ℕ) (u : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hu : ∀ v : ℕ, (𝒢.transition v).comp (u (v + 1)) = (u v).comp (𝒢.transition v))
    (huι : ∀ v : ℕ, Spec.map (CommRingCat.ofHom (u v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
      ι v ≫ (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1)

    [NeZero (M / p)]
    (ρ : R p →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))
    (hσA : Λ.σA = Spec.map (CommRingCat.ofHom ρ))

    (hsp : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₁.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (P₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₁.1 = uκ₁.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (_ : Set.range u₂.1.base ⊆ (𝔛.smoothLocus : Set (X p (ΓM M H) hj)))
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (P₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ ≫ 𝔛.comp Pl hPl ρ hρ i).base P₂.1 = uκ₂.base (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (x : ↥(GluingData.admissible O.ssFinset))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (if i = 0 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        (if i = 1 then Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P₂) 1 else 0))
      (_ : (x : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0),
      ∃ s : SchemeHomOver Λ.σA O.g,
        (O.pts (Pic0.mk Dv)).1 = barPt Pl ≫ s.1 ∧
        O.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s) = GluedPic0.mk O.ssFinset x)

    (hspΛ : ∀ (i : Fin 2)
      (y₁ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₁.1 = y₁.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₁ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₁ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₁.1)
      (_ : uκ₁ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₁ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₁.1 =
        (uκ₁ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (y₂ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
      (u₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
      (_ : barPt Pl ≫ u₂.1 = y₂.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
      (uκ₂ : Spec (CommRingCat.of (ResidueField ↥Pl)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥Pl).comp ρ))
      (_ : uκ₂ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥Pl)) ≫ u₂.1)
      (_ : uκ₂ ≫ pullback.snd _ _ = 𝟙 _)
      (Q₂ : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C)
      (_ : (𝔛.efib Pl hPl ρ hρ).base Q₂.1 =
        (uκ₂ ≫ fibreMap (if i = 0 then 𝔛.π else 𝔛.πw) ((IsLocalRing.residue ↥Pl).comp ρ)).base
          (IsLocalRing.closedPoint (ResidueField ↥Pl)))
      (Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
      (_ : (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
        Finsupp.single (𝔛.Meta.pointEquivPlace y₁) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace y₂) 1)
      (Dw : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (_ : (Dw : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₁) 1 -
          Finsupp.single ((𝔛.Mfib Pl hPl ρ hρ).placeOfPoint Q₂) 1),
      ∃ s₀ : SchemeHomOver Λ.σA Λ.f,
        (Λ.pts (O.degPts i (Pic0.mk Dv))).1 = barPt Pl ≫ s₀.1 ∧
        Λ.ptsSp.symm (schemeHomOverComp ⟨resPt Pl, rfl⟩ s₀) = Pic0.mk Dw)

    (hdia0 : ∀ (e : (ZMod (M / p))ˣ) (P : closedPoints (𝔛.Mfib Pl hPl ρ hρ).C),
      ∃ h : (inv (𝔛.efib Pl hPl ρ hρ)).base
          ((fibreMap (overOfIso (𝔛.dia0 e) (𝔛.dia0_over e)) ((IsLocalRing.residue ↥Pl).comp ρ)).base
            ((𝔛.efib Pl hPl ρ hρ).base P.1)) ∈ closedPoints (𝔛.Mfib Pl hPl ρ hρ).C,
        (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint ⟨_, h⟩ =
          SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
            (CuspForm.gammaLift (M / p) e)) • (𝔛.Mfib Pl hPl ρ hρ).placeOfPoint P)

    (F Finv Fstar : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥Pl) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) →+
      Pic0 (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)

    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt Pl ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (Wbar : JH M H →+ JH M H)
    (wgen : SemilinearAut (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hWbar : ∀ x : JH M H, Wbar x = wgen • x)
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = wgen • 𝔛.Meta.pointEquivPlace y)

    (hUPgen : ∀ x : JH M H,
      genOpH M H S (CohCarrier.Gen.U p (Fact.out) hpM) x + Wbar x = αpull 1 (O.degPts 0 x))

    (σ : ↥O.ssFinset ≃ ↥O.ssFinset)
    (hσ : ∀ n : ↥O.ssFinset, (σ n).1.2 = n.1.1)

    (Φ : Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) ≃ Place (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)))
    (hΦ : ∀ v, Φ v = qExpFrobeniusPlaceModL (ResidueField ↥Pl) (ΓN p M H hpM) p v)
    (hFdiv : ∀ (D D' : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl))),
      (D' : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) =
        Finsupp.mapDomain Φ (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      F (Pic0.mk D) = Pic0.mk D')

    (hpull1sp : ∀ (D : Divisor.degZero (K := ResidueField ↥Pl) (F := Fbar p M H hpM (ResidueField ↥Pl)))
      (x₁ : ↥(GluingData.admissible O.ssFinset)),
      (∀ s ∈ O.ssFinset, (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) s.1 = 0 ∧
        (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) (Φ s.1) = 0) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).1 =
        (p : ℤ) • Finsupp.mapDomain Φ.symm (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.1 =
        SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥Pl) (M / p) (infSubgroup p M H hpM)
          (CuspForm.gammaLift (M / p) pb)) • (D : Divisor (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl))) →
      (x₁ : GluingData (ResidueField ↥Pl) (Fbar p M H hpM (ResidueField ↥Pl)) O.ssFinset).2.2 = 0 →
      O.ptsSp.symm (schemeHomOverComp (Λ.ptsSp (Pic0.mk D)) (degPull 1)) = GluedPic0.mk O.ssFinset x₁)

    (ε w : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v)
    (hεε : ∀ v : ℕ, (ε v).comp (ε v) = ε v)
    (hεtr : ∀ v : ℕ, (𝒢.transition v).comp (ε (v + 1)) = (ε v).comp (𝒢.transition v))
    (hεu : ∀ v : ℕ, (ε v).comp (u v) = (u v).comp (ε v))
    (hwtr : ∀ v : ℕ, (𝒢.transition v).comp (w (v + 1)) = (w v).comp (𝒢.transition v))
    (hεw : ∀ v : ℕ, (ε v).comp (w v) = w v) (hwε : ∀ v : ℕ, (w v).comp (ε v) = w v)
    (hwuε : ∀ v : ℕ, (w v).comp ((u v).comp (ε v)) = ε v)
    (huεw : ∀ v : ℕ, ((u v).comp (ε v)).comp (w v) = ε v)

    {𝒢' : PDivisibleGroup Rh p h} (Dual : 𝒢.CartierDuality 𝒢')

    (hc he : ℕ)
    (Gc : ℕ → Type) [∀ v, CommRing (Gc v)] [∀ v, HopfAlgebra (ZMod p) (Gc v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Gc v)] [∀ v, Module.Finite (ZMod p) (Gc v)]
    (Ge : ℕ → Type) [∀ v, CommRing (Ge v)] [∀ v, HopfAlgebra (ZMod p) (Ge v)]
    [∀ v, Coalgebra.IsCocomm (ZMod p) (Ge v)] [∀ v, Module.Finite (ZMod p) (Ge v)]
    (sc : ∀ v, Gc (v + 1) →ₐc[ZMod p] Gc v) (se : ∀ v, Ge (v + 1) →ₐc[ZMod p] Ge v)
    (qc : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc v) (πe : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Ge v)
    (σ : ∀ v, Ge v →ₐc[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))
    (Θ : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] Gc v ⊗[ZMod p] Ge v)
    (hsum : hc + he = h)
    (hGc : ∀ v, IsLocalRing (Gc v)) (hGe : ∀ v, IsReduced (Ge v))
    (hGe' : ∀ v, Algebra.FormallyUnramified (ZMod p) (Ge v))
    (hsc : ∀ v, Function.Surjective (sc v))
    (hrankGc : ∀ v, Module.finrank (ZMod p) (Gc v) = p ^ (v * hc))
    (hkerGc : ∀ v, RingHom.ker (sc v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Gc (v + 1)) (p ^ v))
    (hse : ∀ v, Function.Surjective (se v))
    (hrankGe : ∀ v, Module.finrank (ZMod p) (Ge v) = p ^ (v * he))
    (hkerGe : ∀ v, RingHom.ker (se v) = PDivisibleGroup.Hopf.torsionIdeal (ZMod p) (Ge (v + 1)) (p ^ v))
    (hqc : ∀ v, Function.Surjective (qc v)) (hπe : ∀ v, Function.Surjective (πe v))
    (hkerπe : ∀ v, RingHom.ker (πe v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Ge v) = nilradical (ZMod p ⊗[Rh] 𝒢.level v))
    (hπeσ : ∀ v, (πe v).comp (σ v) = BialgHom.id (ZMod p) (Ge v))
    (hkerqc : ∀ v, RingHom.ker (qc v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc v) =
      Ideal.map (σ v : Ge v →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) (Ge v))))
    (hΘ : ∀ v, Function.Bijective (Θ v))
    (hΘ' : ∀ v b, Θ v b = Algebra.TensorProduct.map (qc v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Gc v)
      (πe v : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] Ge v) (Coalgebra.comul (R := ZMod p) b))
    (hqcs : ∀ v, (qc v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (sc v).comp (qc (v + 1)))
    (hπes : ∀ v, (πe v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (se v).comp (πe (v + 1)))
    (hsσ : ∀ v, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)).comp (σ (v + 1)) = (σ v).comp (se v))
    (hΘs : ∀ v, (Θ v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) = (Bialgebra.TensorProduct.map (sc v) (se v)).comp (Θ (v + 1)))

    (VB : ∀ v, (ZMod p ⊗[Rh] 𝒢.level v) →ₐc[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))
    (hVB1 : ∀ v (b : (ZMod p ⊗[Rh] 𝒢.level v)), (VB v b) ^ p = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p b)
    (hVB2 : ∀ v (b : (ZMod p ⊗[Rh] 𝒢.level v)), VB v (b ^ p) = PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p b)
    (hVB3 : ∀ v (φ : CartierDual (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)) (b : (ZMod p ⊗[Rh] 𝒢.level v)), φ (VB v b) = (φ ^ p) b) :
    ∃ d₀ : (ZMod M)ˣ, ∀ (δ : ∀ v : ℕ, 𝒢.level v →ₐc[Rh] 𝒢.level v),
      (∀ v : ℕ, (𝒢.transition v).comp (δ (v + 1)) = (δ v).comp (𝒢.transition v)) →
      (∀ v : ℕ, Spec.map (CommRingCat.ofHom (δ v : 𝒢.level v →+* 𝒢.level v)) ≫ ι v =
        ι v ≫ (O.hecke S (CohCarrier.Gen.dia d₀)).1) →
      (∀ v : ℕ, (ε v).comp (δ v) = (δ v).comp (ε v)) →
      (∀ v : ℕ, (u v).comp (δ v) = (δ v).comp (u v)) →

      ∀ v : ℕ, (qc v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc v).comp
        (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ v))).comp
          (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) =
      (qc v : ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] Gc v).comp
        (((VB v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) :
            ZMod p ⊗[Rh] 𝒢.level v →ₐc[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) :
          ZMod p ⊗[Rh] 𝒢.level v →ₐ[ZMod p] ZMod p ⊗[Rh] 𝒢.level v) := by
  classical
  have hp : p.Prime := Fact.out

  letI algZ : Algebra (ZMod p) (ResidueField ↥Pl) := ZMod.algebra _ p
  let rκ : Rh →+* (ResidueField ↥Pl) := (IsLocalRing.residue ↥Pl).comp
    ((algebraMap Rh (AlgebraicClosure ℚ)).codRestrict Pl.toSubring hRA)
  letI algR : Algebra Rh (ResidueField ↥Pl) := rκ.toAlgebra
  have hrκ : ∀ x : Rh, algebraMap Rh (ResidueField ↥Pl) x =
      IsLocalRing.residue ↥Pl ⟨algebraMap Rh (AlgebraicClosure ℚ) x, hRA x⟩ := fun x => rfl
  have hrκ' : algebraMap Rh (ResidueField ↥Pl) = (algebraMap (ZMod p) (ResidueField ↥Pl)).comp (algebraMap Rh (ZMod p)) := by
    refine X1R.ringHom_eq_algebraMap_comp p (algebraMap Rh (ZMod p)) _ fun x hx => ?_
    rw [hrκ, IsLocalRing.residue_eq_zero_iff, ValuationSubring.valuation_lt_one_iff]
    exact (hres x).mp hx
  haveI hIST : IsScalarTower Rh (ZMod p) (ResidueField ↥Pl) := IsScalarTower.of_algebraMap_eq' hrκ'

  have hκ0 : (p : ResidueField ↥Pl) = 0 := CharP.cast_eq_zero _ p
  have hp0 : (p : Γ(RelativeGroupLaw.baseChangeScheme (resPt Pl ≫ Λ.σA) O.g, ⊤)) = 0 :=
    X1R.natCast_eq_zero_Γ_pullback O.g (resPt Pl ≫ Λ.σA) hκ0
  have hs : (Spec (CommRingCat.of (ResidueField ↥Pl))).frobenius p 1 hp (Scheme.natCast_eq_zero_ΓSpec hκ0) ≫
      (resPt Pl ≫ Λ.σA) = resPt Pl ≫ Λ.σA := by
    rw [Scheme.frobenius_Spec p 1 hp hκ0, hσA]
    simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    exact X1R.powChar_comp_ringHom_ratLocalizedAt p hκ0 ((IsLocalRing.residue ↥Pl).comp ρ)
  have hΦG := X1R.frobenius_fst_comp_eq O.g (resPt Pl ≫ Λ.σA) p hp hκ0 hs hp0

  have H1 := ModularCurve.JHNeronObjectAtP.exists_units_pullbackFst_abqFibre_comp_relFrobenius_comp_hecke_U_comp_hecke_dia_eq_comp_schemeNsmul
    p M H hpM hpM2 hHp Pl hPl hj 𝔛 Λ O hrep S ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull
    hpull hpull_mul hpullsp Wbar wgen hWbar hwgen hUPgen _ hσ Φ hΦ hFdiv hpull1sp hp0 hΦG
  obtain ⟨d₀, hK⟩ := H1
  refine ⟨d₀, fun δ' hδ'tr hδ'ι hεδ' huδ' => ?_⟩

  have hεu1 : ∀ v (y : ZMod p ⊗[Rh] 𝒢.level v),
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) y) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) y) := by
    intro v y
    have h0 : ∀ x, ε v (u v x) = u v (ε v x) := fun x => by simpa using DFunLike.congr_fun (hεu v) x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp [h0]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hεδ1 : ∀ v (y : ZMod p ⊗[Rh] 𝒢.level v),
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) y) = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) y) := by
    intro v y
    have h0 : ∀ x, ε v (δ' v x) = δ' v (ε v x) := fun x => by simpa using DFunLike.congr_fun (hεδ' v) x
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp [h0]
    | add x y hx hy => simp only [map_add, hx, hy]
  have huδ1 : ∀ v (y : ZMod p ⊗[Rh] 𝒢.level v),
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ' v))) y = (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) y) := by
    intro v y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp
    | add x y hx hy => simp only [map_add, hx, hy]

  have star : ∀ (v : ℕ) (b : ZMod p ⊗[Rh] 𝒢.level v),
      qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ' v))) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (b ^ p))) =
      qc v (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) b)) := by
    intro v

    have hsq : (Spec.map (CommRingCat.ofHom ((Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom.comp
        (Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)).toRingHom)) ≫ ι v) ≫ O.g =
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : (ResidueField ↥Pl) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)))) :
        Spec (CommRingCat.of ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))) ⟶ _) ≫ (resPt Pl ≫ Λ.σA) := by
      rw [Category.assoc, hS1 v, hσA]
      simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext x
      have e1 : (⟨algebraMap Rh (AlgebraicClosure ℚ) (ρh x), hRA _⟩ : ↥Pl) = ρ x := Subtype.ext (by
        change algebraMap Rh (AlgebraicClosure ℚ) (ρh x) = Pl.subtype (ρ x)
        rw [← RingHom.comp_apply (algebraMap Rh (AlgebraicClosure ℚ)) ρh, hS0, ← RingHom.comp_apply Pl.subtype ρ, hρ])
      have e2 : algebraMap Rh (ResidueField ↥Pl) (ρh x) = IsLocalRing.residue ↥Pl (ρ x) := by rw [hrκ, e1]
      calc _ = (Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)))
            ((Algebra.TensorProduct.includeRight : 𝒢.level v →ₐ[Rh] (ZMod p ⊗[Rh] 𝒢.level v)) (algebraMap Rh (𝒢.level v) (ρh x))) := rfl
        _ = (Algebra.TensorProduct.includeRight : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)))
            (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) (algebraMap Rh (ZMod p) (ρh x))) := by
              rw [AlgHom.commutes, IsScalarTower.algebraMap_apply Rh (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)]
        _ = algebraMap (ZMod p) (ResidueField ↥Pl) (algebraMap Rh (ZMod p) (ρh x)) ⊗ₜ[ZMod p] (1 : ZMod p ⊗[Rh] 𝒢.level v) := by
              rw [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply]
        _ = IsLocalRing.residue ↥Pl (ρ x) ⊗ₜ[ZMod p] (1 : ZMod p ⊗[Rh] 𝒢.level v) := by
              rw [← IsScalarTower.algebraMap_apply, e2]
        _ = _ := rfl

    have H3 := ModularCurve.JHNeronObjectAtP.mono_lift_and_exists_specMap_qc_comp_baseChange_comp_lift_eq_comp_pullbackFst_abqFibre_of_ordinaryIdempotent_of_bridge
      p M H hpM hpM2 hHp Pl hPl hj 𝔛 Λ O hrep Rh hRA hRloc hres 𝒢 Δ hΔ hfin ρh ι hS0 hS1 hS2 hS3 hS4 hS5 hS6 hS8 S u hu huι
      ρ hρ hσA hsp hspΛ hdia0 F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpull_mul hpullsp Wbar wgen hWbar hwgen
      hUPgen _ hσ Φ hΦ hFdiv hpull1sp ε w hεε hεtr hεu hwtr hεw hwε hwuε huεw v hrκ hsq
      (Gc v) (Ge v) (qc v) (πe v) (Θ v) (hGc v) (hGe v) (hqc v) (hπe v) (hΘ v) (hΘ' v)
    obtain ⟨hmono, ⟨pr, hpr⟩, hf₂⟩ := H3
    haveI := hmono

    have hB0 : (p : ZMod p ⊗[Rh] 𝒢.level v) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v)), ZMod.natCast_self, map_zero]
    have hA0 : (p : (ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) = 0 := by
      rw [← map_natCast (algebraMap (ZMod p) ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))), ZMod.natCast_self, map_zero]

    let FrobB : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v) :=
      { toRingHom := powCharRingHom (ZMod p ⊗[Rh] 𝒢.level v) p 1 hp hB0
        commutes' := fun r => by
          show (algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) r) ^ p ^ 1 = algebraMap (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) r
          rw [pow_one, ← map_pow, ZMod.pow_card] }
    have hFrobB : ∀ x, FrobB x = x ^ p := fun x => by
      show x ^ p ^ 1 = x ^ p
      rw [pow_one]
    let eF : ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) :=
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl)) FrobB).toRingHom
    let eU : ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) :=
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
        ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom
    let eD : ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) →+* ((ResidueField ↥Pl) ⊗[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v)) :=
      (Algebra.TensorProduct.map (AlgHom.id (ResidueField ↥Pl) (ResidueField ↥Pl))
        ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) : (ZMod p ⊗[Rh] 𝒢.level v) →ₐ[ZMod p] (ZMod p ⊗[Rh] 𝒢.level v))).toRingHom

    have hFsq := X1R.specMap_comp_lift_eq_lift_comp_relFrob O.g (resPt Pl ≫ Λ.σA) (ι v) _ _ hsq p hp hp0 hΦG hA0 eF
      (by ext x; simp [eF, hFrobB, Algebra.TensorProduct.tmul_pow]) (by ext c; simp [eF])
    have hUsq := AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
      O.g (resPt Pl ≫ Λ.σA) (ι v) (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).1 (O.hecke S (CohCarrier.Gen.U p Fact.out hpM)).2
      (u v : 𝒢.level v →+* 𝒢.level v) (huι v) _ _ hsq eU (by ext x; simp [eU]) (by ext c; simp [eU])
    have hDsq := AlgebraicGeometry.specMap_comp_pullbackLift_eq_pullbackLift_comp_pullbackMap_of_comp_eq_comp
      O.g (resPt Pl ≫ Λ.σA) (ι v) (O.hecke S (CohCarrier.Gen.dia d₀)).1 (O.hecke S (CohCarrier.Gen.dia d₀)).2
      (δ' v : 𝒢.level v →+* 𝒢.level v) (hδ'ι v) _ _ hsq eD (by ext x; simp [eD]) (by ext c; simp [eD])
    have hf₁ := X1R.paste3 hFsq hUsq hDsq
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp] at hf₁

    have h6 := AlgebraicGeometry.comp_eq_comp_of_specMap_comp_eq_comp_of_mono_of_comp_eq _ _ _ pr hpr _ _ _ _ hf₁ hf₂ hK

    intro b
    have h7 := RingHom.congr_fun h6 ((1 : ResidueField ↥Pl) ⊗ₜ[ZMod p] b)
    have h8 : qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) b)) ^ p)) =
        qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (PDivisibleGroup.Hopf.nsmulAlgHom (ZMod p) (ZMod p ⊗[Rh] 𝒢.level v) p b)) := by
      apply Algebra.TensorProduct.includeRight_injective (R := ZMod p) (A := ResidueField ↥Pl)
        (algebraMap (ZMod p) (ResidueField ↥Pl)).injective
      simp [eF, eU, eD, hFrobB, Algebra.TensorProduct.includeRight_apply] at h7 ⊢
      exact h7
    calc _ = qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (b ^ p)))) := by rw [huδ1]
      _ = qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) (b ^ p)))) := by rw [← hεδ1, ← hεu1]
      _ = qc v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)) (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (u v)) ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (δ' v)) b)) ^ p)) := by rw [map_pow, map_pow]
      _ = _ := h8
      _ = _ := by rw [PDivisibleGroup.Hopf.nsmulAlgHom_bialgHom_apply]

  have hVt : ∀ v, ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v))).comp (VB (v + 1)) = (VB v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) :=
    fun v => HopfAlgebra.comp_eq_comp_of_forall_cartierDual_apply_eq_pow_apply_zmodp p
      (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) (VB (v + 1)) (hVB3 (v + 1)) (VB v) (hVB3 v)
  have hg : ∀ v, ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v))).comp
      (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u (v + 1)).comp (δ' (v + 1))))).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε (v + 1)))) =
      (((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ' v)))).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v))).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) := by
    intro v
    have h1 : ∀ x, 𝒢.transition v (u (v + 1) x) = u v (𝒢.transition v x) := fun x => by
      simpa using DFunLike.congr_fun (hu v) x
    have h2 : ∀ x, 𝒢.transition v (δ' (v + 1) x) = δ' v (𝒢.transition v x) := fun x => by
      simpa using DFunLike.congr_fun (hδ'tr v) x
    have h3 : ∀ x, 𝒢.transition v (ε (v + 1) x) = ε v (𝒢.transition v x) := fun x => by
      simpa using DFunLike.congr_fun (hεtr v) x
    apply BialgHom.ext
    intro y
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp [h1, h2, h3]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hg' : ∀ v, ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v))).comp ((VB (v + 1)).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε (v + 1)))) =
      ((VB v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v))).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) := by
    intro v
    have h3 : ∀ x, 𝒢.transition v (ε (v + 1) x) = ε v (𝒢.transition v x) := fun x => by
      simpa using DFunLike.congr_fun (hεtr v) x
    have h4 : ∀ y, (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) (VB (v + 1) y) = VB v ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v)) y) := fun y => by
      simpa using DFunLike.congr_fun (hVt v) y
    apply BialgHom.ext
    intro y
    simp only [BialgHom.coe_comp, Function.comp_apply]
    rw [h4]
    congr 1
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul c x => simp [h3]
    | add x y hx hy => simp only [map_add, hx, hy]

  have fin := X1R.endgame p hc (fun v => ZMod p ⊗[Rh] 𝒢.level v) Gc Ge
    (fun v => (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (𝒢.transition v))) sc qc σ hGc hGe hqc hkerqc hsc hrankGc hkerGc hqcs
    (fun v => ((Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) ((u v).comp (δ' v)))).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v)))
    (fun v => (VB v).comp (Bialgebra.TensorProduct.map (BialgHom.id (ZMod p) (ZMod p)) (ε v))) hg hg'
    (fun v b => by
      simp only [BialgHom.coe_comp, Function.comp_apply]
      rw [star, map_pow, hVB2])
  intro v
  exact fin v

end S_ModularCurve_JHNeronObjectAtP_exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_units_forall_qc_comp_baseChange_U_comp_diamond_comp_eq_qc_comp_verschiebung_of_ordinaryIdempotent_of_bridge (solution)
