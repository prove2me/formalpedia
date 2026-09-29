-- Prove2me | solution 1 for ModularCurve.exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9a6d71c4-e9e2-541d-bbb9-e086d1700d17

import Mathlib
import Definitions.Def_ModularCurve_XH
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
import Theorems.Thm_ModularCurve_exists_xHDRModelAtP_atkinLehner_generic
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_exists_schemeHomOver_barPt_comp_eq_of_isProper
import Theorems.Thm_ValuationSubring_exists_ratLocalizedAt_ringHom_of_liesOverPrime
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_nonempty_ssPlacesQExp
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_XHDRModelAtP_ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA"
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod"
p2m_attr_erase "instance" "SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal'"
p2m_attr_erase "simp" "WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ"
p2m_attr_erase "simp" "ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq"
p2m_attr_erase "simp" "ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app"

set_option autoImplicit false
open scoped MatrixGroups
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra IsLocalRing AlgebraicCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP

namespace DivSpecF

open ModularCurve

theorem exists_gaussProlongation (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ)
    (A : ValuationSubring (AlgebraicClosure ℚ)) :
    ∃ R : RegularProlongation A ↥(xHFunctionFieldBar M H)
        ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H)),
      (∀ f : ↥(xHFunctionFieldBar M H),
        f ∈ R.integers ↔
          ∃ x y : LaurentSeries ↥A, coeffMap (residue ↥A) y ≠ 0 ∧
            (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x) ∧
      (∀ (y : LaurentSeries ↥A) (hy : coeffMap A.subtype y ∈ xHFunctionFieldBar M H),
        ∃ hint : (⟨coeffMap A.subtype y, hy⟩ : ↥(xHFunctionFieldBar M H)) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) :
              LaurentSeries (ResidueField ↥A)) = coeffMap (residue ↥A) y) ∧
      (∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ R.integers) (x y : LaurentSeries ↥A),
        coeffMap (residue ↥A) y ≠ 0 →
        (f : LaurentSeries (AlgebraicClosure ℚ)) * coeffMap A.subtype y = coeffMap A.subtype x →
        ((R.residue ⟨f, hf⟩ : ↥(qExpFunctionFieldC (ResidueField ↥A) (CohCarrier.GammaH M H))) :
            LaurentSeries (ResidueField ↥A)) * coeffMap (residue ↥A) y = coeffMap (residue ↥A) x) := by
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H
  obtain ⟨R, h1, h2, h3⟩ :=
    exists_regularProlongation_laurentBaseChange_qExpFunctionFieldC_residue_mul_eq
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  exact ⟨R, h1, h2, h3⟩

theorem mapDomain_apply_eq_sum_ite {α β : Type*} [DecidableEq β] (r : α → β) (D : α →₀ ℤ) (Q : β) :
    Finsupp.mapDomain r D Q = ∑ v ∈ D.support, if r v = Q then D v else 0 := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply, Finsupp.single_apply]

end DivSpecF

open DivSpecF in
set_option maxHeartbeats 3200000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (IsLocalRing.ResidueField ↥A) p] [IsAlgClosed (IsLocalRing.ResidueField ↥A)] :
    ∃ (R : AlgebraicCurve.RegularProlongation A ↥(ModularCurve.xHFunctionFieldBar M H) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H)))
      (r : AlgebraicCurve.Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) →
        AlgebraicCurve.Place (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)))),
      (∀ (y : LaurentSeries ↥A) (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H),
        ∃ hint : (⟨ModularCurve.coeffMap A.subtype y, hy⟩ : ↥(ModularCurve.xHFunctionFieldBar M H)) ∈ R.integers,
          ((R.residue ⟨_, hint⟩ : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
            ModularCurve.coeffMap (IsLocalRing.residue ↥A) y) ∧
      (∀ f : R.integers, R.residue f ≠ 0 →
        ∀ g : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
          (g : LaurentSeries (IsLocalRing.ResidueField ↥A)) =
            ((R.residue f : ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH M H))) : LaurentSeries (IsLocalRing.ResidueField ↥A)) →
          ∀ D : AlgebraicCurve.Divisor (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
            (∀ P, D P = P.ord (f : ↥(ModularCurve.xHFunctionFieldBar M H))) →
            ∃ E : AlgebraicCurve.Divisor (IsLocalRing.ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField ↥A) (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))),
              (∀ Q, E Q ≠ 0 → Q ∈ ModularCurve.ssPlacesQExp (IsLocalRing.ResidueField ↥A)
                (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) ∧
              ∀ Q, Finsupp.mapDomain r D Q + E Q = Q.ord g) := by
  classical

  obtain ⟨R, hRi, hRii, hRiii⟩ := DivSpecF.exists_gaussProlongation M H A

  have hj : ModularCurve.jqModC ℚ ∈ ModularCurve.qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)) :=
    ModularCurve.intFormRatiosC_subset ℚ ⊤ (ModularCurve.jqModC_mem_intFormRatiosC ℚ ⊤)
  obtain ⟨𝔛, θ, -, -⟩ := ModularCurve.exists_xHDRModelAtP_atkinLehner_generic p M H hpM hpM2 hHp hj
  obtain ⟨ρ, hρ⟩ := ValuationSubring.exists_ratLocalizedAt_ringHom_of_liesOverPrime p A hA
  haveI := 𝔛.isProper
  haveI := 𝔛.efib_iso A hA ρ hρ
  haveI := 𝔛.comp_isClosedImmersion A hA ρ hρ 0

  haveI : NeZero (M / p) := ⟨fun h0 => by
    have hp : 0 < p := (Fact.out : p.Prime).pos
    have := Nat.div_mul_cancel hpM
    rw [h0, zero_mul] at this
    exact (NeZero.ne M) this.symm⟩
  have hpN : ¬ p ∣ M / p := by
    rintro ⟨c, hc⟩
    apply hpM2
    refine ⟨c, ?_⟩
    rw [pow_two, mul_assoc, ← hc, Nat.mul_div_cancel' hpM]
  obtain ⟨v₀, hv₀⟩ := ModularCurve.nonempty_ssPlacesQExp (M / p) (ΓN p M H hpM)
    (ModularCurve.Gamma1_le_GammaH _ _) (CohCarrier.GammaH_le_Gamma0 _) p hpN (ResidueField ↥A)

  have hsec : ∀ v : Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      ∃ uu : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj),
        barPt A ≫ uu.1 = (𝔛.Meta.pointEquivPlace.symm v).1 ≫ 𝔛.eeta ≫ pullback.fst _ _ := by
    intro v
    have hx : ((𝔛.Meta.pointEquivPlace.symm v).1 ≫ 𝔛.eeta ≫ pullback.fst _ _) ≫ toBase p (ΓM M H) hj =
        genPt p := by
      simp only [Category.assoc]
      rw [pullback.condition, ← Category.assoc 𝔛.eeta, 𝔛.heeta, ← Category.assoc,
        (𝔛.Meta.pointEquivPlace.symm v).2, Category.id_comp]
    exact ModularCurve.JZeroNeronObjectAtP.exists_schemeHomOver_barPt_comp_eq_of_isProper p A ρ hρ
      (toBase p (ΓM M H) hj) ⟨_, hx⟩
  choose u hu using hsec

  have hcond : ∀ v : Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H),
      (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ (u v).1) ≫ toBase p (ΓM M H) hj =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρ)) := by
    intro v
    rw [Category.assoc, (u v).2, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  let uκ : Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) →
      (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((residue ↥A).comp ρ)) :=
    fun v => pullback.lift _ _ (hcond v)
  have huκ₁ : ∀ v, uκ v ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ (u v).1 :=
    fun v => pullback.lift_fst _ _ _
  have huκ₂ : ∀ v, uκ v ≫ pullback.snd _ _ = 𝟙 _ := fun v => pullback.lift_snd _ _ _

  set Mf := 𝔛.Mfib A hA ρ hρ with hMf
  have hc0inj : Function.Injective (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base :=
    (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).isClosedEmbedding.injective
  let good : Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) → Prop := fun v =>
    ∃ P : closedPoints Mf.C, (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base P.1 =
        (uκ v).base (closedPoint (ResidueField ↥A)) ∧
      Mf.placeOfPoint P ∉ ModularCurve.ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p
  let r : Place (AlgebraicClosure ℚ) ↥(ModularCurve.xHFunctionFieldBar M H) →
      Place (ResidueField ↥A) ↥(ModularCurve.qExpFunctionFieldC (ResidueField ↥A)
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))) :=
    fun v => if h : good v then Mf.placeOfPoint h.choose else v₀
  refine ⟨R, r, hRii, ?_⟩

  intro f hfres g hg D hD
  obtain ⟨x, y, hybar, hfxy⟩ := (hRi f.1).mp f.2
  have hres := hRiii f.1 f.2 x y hybar hfxy
  have hg0' : (g : LaurentSeries (ResidueField ↥A)) ≠ 0 := by
    rw [hg]
    exact fun h => hfres (by exact_mod_cast h)
  have hg0 : g ≠ 0 := fun h => hg0' (by rw [h]; rfl)
  have hg' : (g : LaurentSeries (ResidueField ↥A)) * ModularCurve.coeffMap (residue ↥A) y =
      ModularCurve.coeffMap (residue ↥A) x := by
    rw [hg]; exact hres
  have hxbar : ModularCurve.coeffMap (residue ↥A) x ≠ 0 := by
    rw [← hg']; exact mul_ne_zero hg0' hybar
  haveI := (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
    p M H hpM hpM2 (ResidueField ↥A)).1
  obtain ⟨Dg, hDg, -⟩ := HasPrincipalDivisors.exists_divisor
    (K := ResidueField ↥A) (F := ModularCurve.JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) g hg0
  refine ⟨Dg - Finsupp.mapDomain r D, ?_, fun Q => by rw [Finsupp.sub_apply, hDg Q]; ring⟩
  intro Q hQ
  by_contra hQss
  apply hQ
  rw [Finsupp.sub_apply, sub_eq_zero, hDg Q]

  obtain ⟨Pbar, hPbar⟩ := Mf.placeOfPoint_bijective.2 Q
  have hPss : Mf.placeOfPoint Pbar ∉ ModularCurve.ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p := by
    rw [hPbar]; exact hQss
  have hX := ModularCurve.XHDRModelAtP.ord_placeOfPoint_eq_sum_ite_of_not_mem_ssPlacesQExp_of_mul_coeffMap_eq_coeffMap
    p M hpM hpM2 H hHp A hA hj 𝔛 ρ hρ f.1 x y hxbar hybar hfxy g hg'
    (ι := ↥D.support)
    (fun j => 𝔛.Meta.pointEquivPlace.symm j.1) (fun j => u j.1) (fun j => hu j.1)
    (fun j => uκ j.1) (fun j => huκ₁ j.1) (fun j => huκ₂ j.1) (fun j => D j.1) ?hdiv Pbar hPss
  case hdiv =>
    intro v
    simp only [Equiv.apply_symm_apply, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.single_apply]
    rw [← hD v]
    rw [Finset.sum_coe_sort D.support (fun j => if j = v then D j else 0)]
    rw [Finset.sum_ite_eq' D.support v]
    split_ifs with hv
    · rfl
    · exact (Finsupp.notMem_support_iff.mp hv)
  rw [hPbar] at hX
  rw [hX, DivSpecF.mapDomain_apply_eq_sum_ite, ← Finset.sum_coe_sort D.support]
  refine Finset.sum_congr rfl fun v _ => ?_

  have key : r v.1 = Q ↔ (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Pbar.1 =
      (uκ v.1).base (closedPoint (ResidueField ↥A)) := by
    constructor
    · intro hrv
      by_cases hgood : good v.1
      · have hr : r v.1 = Mf.placeOfPoint hgood.choose := dif_pos hgood
        have hPe : hgood.choose = Pbar :=
          Mf.placeOfPoint_bijective.1 (by rw [← hr, hrv, hPbar])
        rw [← hPe]; exact hgood.choose_spec.1
      · have hr : r v.1 = v₀ := dif_neg hgood
        exact (hQss (by rw [← hrv, hr]; exact hv₀)).elim
    · intro hc
      have hgood : good v.1 := ⟨Pbar, hc, hPss⟩
      have hr : r v.1 = Mf.placeOfPoint hgood.choose := dif_pos hgood
      have hPe : hgood.choose = Pbar :=
        Subtype.ext (hc0inj (hgood.choose_spec.1.trans hc.symm))
      rw [hr, hPe, hPbar]
  by_cases hc : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ 0).base Pbar.1 = (uκ v.1).base (closedPoint (ResidueField ↥A))
  · rw [if_pos hc, if_pos (key.mpr hc)]
  · rw [if_neg hc, if_neg (fun h => hc (key.mp h))]

end S_ModularCurve_exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd
end P2MW
export P2MW.S_ModularCurve_exists_regularProlongation_placeMap_xHFunctionFieldBar_of_dvd_of_not_sq_dvd (solution)
