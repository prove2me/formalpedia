-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d41d1349-4451-52a4-bd89-82cf6861618c

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf"
p2m_attr_erase "instance" "PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom ModularCurve.TwoChart.isOpenImmersion_fInf ModularCurve.TwoChart.isOpenImmersion_ιFin ModularCurve.TwoChart.isOpenImmersion_ιInf"
p2m_attr_erase "instance" "ModularCurve.TwoChart.isOpenImmersion_fFin ValuationSubring.instIsAlgClosedResidueField"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆"
p2m_attr_erase "simp" "ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP"
p2m_attr_erase "simp" "ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero"
p2m_attr_erase "simp" "TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply"
p2m_attr_erase "simp" "TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk ModularCurve.TwoChart.coe_jChartFin ModularCurve.TwoChart.ιFin_modelTo ModularCurve.TwoChart.ιInf_modelTo ModularCurve.TwoChart.ιInf_modelTo_assoc ModularCurve.TwoChart.coe_jInvChartInf ModularCurve.TwoChart.ιFin_modelTo_assoc ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 12800000

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve~PlaceSpecialization ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP"

open scoped MatrixGroups

namespace ClearSol

section PosNeg
variable {α : Type*}

noncomputable def pPart (E : α →₀ ℤ) : α →₀ ℤ := Finsupp.mapRange (fun n : ℤ => ((n.toNat : ℕ) : ℤ)) (by simp) E

noncomputable def nPart (E : α →₀ ℤ) : α →₀ ℤ := Finsupp.mapRange (fun n : ℤ => (((-n).toNat : ℕ) : ℤ)) (by simp) E

@[scoped simp] theorem pPart_apply (E : α →₀ ℤ) (a : α) : pPart E a = ((E a).toNat : ℤ) := Finsupp.mapRange_apply ..
@[scoped simp] theorem nPart_apply (E : α →₀ ℤ) (a : α) : nPart E a = ((-E a).toNat : ℤ) := Finsupp.mapRange_apply ..

theorem pPart_nonneg (E : α →₀ ℤ) (a : α) : 0 ≤ pPart E a := by simp
theorem nPart_nonneg (E : α →₀ ℤ) (a : α) : 0 ≤ nPart E a := by simp

theorem pPart_sub_nPart (E : α →₀ ℤ) (a : α) : pPart E a - nPart E a = E a := by simp

theorem support_pPart (E : α →₀ ℤ) : (pPart E).support ⊆ E.support := Finsupp.support_mapRange
theorem support_nPart (E : α →₀ ℤ) : (nPart E).support ⊆ E.support := Finsupp.support_mapRange

theorem pPart_ne_zero (E : α →₀ ℤ) {a : α} (h : pPart E a ≠ 0) : E a ≠ 0 := by
  intro h0; apply h; simp [h0]
theorem nPart_ne_zero (E : α →₀ ℤ) {a : α} (h : nPart E a ≠ 0) : E a ≠ 0 := by
  intro h0; apply h; simp [h0]

theorem prod_zpow_eq_pPart_div_nPart {L : Type*} [Field L] (E : α →₀ ℤ) (x : α → L)
    (hx : ∀ a ∈ E.support, x a ≠ 0) :
    (E.prod fun a n => x a ^ n) = (pPart E).prod (fun a n => x a ^ n) / (nPart E).prod (fun a n => x a ^ n) := by
  rw [Finsupp.prod_of_support_subset (pPart E) (support_pPart E) _ (fun a _ => zpow_zero _),
    Finsupp.prod_of_support_subset (nPart E) (support_nPart E) _ (fun a _ => zpow_zero _),
    ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun a ha => ?_
  rw [← zpow_sub₀ (hx a ha), pPart_sub_nPart]

theorem prod_zpow_eq_prod_sigma {M : Type*} [CommGroupWithZero M] (E : α →₀ ℤ) (hE : ∀ a, 0 ≤ E a) (x : α → M) :
    (E.prod fun a n => x a ^ n) = ∏ q ∈ E.support.sigma (fun a => Finset.range (E a).toNat), x q.1 := by
  rw [Finset.prod_sigma]
  refine Finset.prod_congr rfl fun a _ => ?_
  show x a ^ (E a) = ∏ s ∈ Finset.range (E a).toNat, x a
  rw [Finset.prod_const, Finset.card_range, ← zpow_natCast, Int.toNat_of_nonneg (hE a)]

end PosNeg

section ModRed
variable {Γ : Type*} [LinearOrderedCommGroupWithZero Γ]

theorem exists_pow_lt_prod_le_pow {ι : Type*} (v : Γ) (hv0 : v ≠ 0) (hv1 : v < 1) (s : Finset ι) (x : ι → Γ)
    (hx : ∀ i ∈ s, v < x i ∧ x i ≤ 1) :
    ∃ k : ℕ, v ^ (k + 1) < ∏ i ∈ s, x i ∧ ∏ i ∈ s, x i ≤ v ^ k := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simpa using hv1, by simp⟩
  | insert a s ha ih =>
    obtain ⟨k, hk1, hk2⟩ := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    obtain ⟨ha1, ha2⟩ := hx a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    have hxa0 : 0 < x a := lt_of_le_of_lt zero_le' ha1
    have hv0' : 0 < v := zero_lt_iff.mpr hv0
    by_cases hcase : v ^ (k + 1) < x a * ∏ i ∈ s, x i
    · refine ⟨k, hcase, ?_⟩
      calc x a * ∏ i ∈ s, x i ≤ 1 * v ^ k := mul_le_mul' ha2 hk2
        _ = v ^ k := one_mul _
    · push Not at hcase
      refine ⟨k + 1, ?_, hcase⟩
      calc v ^ (k + 1 + 1) = v * v ^ (k + 1) := by rw [pow_succ']
        _ < x a * v ^ (k + 1) := mul_lt_mul_of_pos_right ha1 (pow_pos hv0' _)
        _ < x a * ∏ i ∈ s, x i := mul_lt_mul_of_pos_left hk1 hxa0

end ModRed

section Val
variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem isUnit_of_valuation_eq_one {x : L} (hx : A.valuation x = 1) : ∃ h : x ∈ A, IsUnit (⟨x, h⟩ : A) := by
  have hxA : x ∈ A := (A.valuation_le_one_iff x).mp hx.le
  exact ⟨hxA, (A.valuation_eq_one_iff ⟨x, hxA⟩).mpr hx⟩

theorem valuation_coe_unit {u : A} (hu : IsUnit u) : A.valuation (u : L) = 1 := (A.valuation_eq_one_iff u).mp hu

theorem coe_units_inv (S : ValuationSubring L) (u : (↥S)ˣ) : (((u⁻¹ : (↥S)ˣ) : ↥S) : L) = ((u : ↥S) : L)⁻¹ := by
  have h1 : ((u : ↥S) : L) * (((u⁻¹ : (↥S)ˣ) : ↥S) : L) = 1 := by
    rw [← MulMemClass.coe_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, OneMemClass.coe_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem exists_inv_of_isUnit {u : A} (hu : IsUnit u) : ∃ w : A, IsUnit w ∧ (w : L) = (u : L)⁻¹ := by
  obtain ⟨uu, huu⟩ := hu
  refine ⟨((uu⁻¹ : (↥A)ˣ) : A), Units.isUnit _, ?_⟩
  rw [coe_units_inv, huu]

end Val

section Ann
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]

theorem valuation_evalAt_param (An : Annulus A F) {P : Place L F} (hP : P ∈ An.dom) :
    A.valuation (An.modulus : L) < A.valuation (P.evalAt An.param) ∧ A.valuation (P.evalAt An.param) < 1 ∧
      P.evalAt An.param ≠ 0 := by
  obtain ⟨-, -, ⟨hzA, hzm⟩, hz0, m, hm, hπ⟩ := An.mem_dom P hP
  have hvz : A.valuation (P.evalAt An.param) < 1 := (A.valuation_lt_one_iff ⟨_, hzA⟩).mp hzm
  have hvm : A.valuation (m : L) < 1 := (A.valuation_lt_one_iff m).mp hm
  refine ⟨?_, hvz, hz0⟩
  rw [hπ, map_mul]
  have hvz0 : 0 < A.valuation (P.evalAt An.param) := zero_lt_iff.mpr ((map_ne_zero _).mpr hz0)
  calc A.valuation (P.evalAt An.param) * A.valuation (m : L) < A.valuation (P.evalAt An.param) * 1 :=
        mul_lt_mul_of_pos_left hvm hvz0
    _ = _ := mul_one _

end Ann

section Gauss
variable {L : Type*} [Field L] {A : ValuationSubring L} {F : Type*} [Field F] [Algebra L F]
  {Fbar : Type*} [Field Fbar] [Algebra (ResidueField A) Fbar]

theorem gu_ne_zero (R : RegularProlongation A F Fbar) {x : F} (hx : ∃ h : x ∈ R.integers, R.residue ⟨x, h⟩ ≠ 0) :
    x ≠ 0 := by
  obtain ⟨h, hres⟩ := hx
  rintro rfl
  apply hres
  have : (⟨(0 : F), h⟩ : R.integers) = 0 := rfl
  rw [this, map_zero]

theorem gu_congr (R : RegularProlongation A F Fbar) {x y : F} (hxy : x = y)
    (hx : ∃ h : x ∈ R.integers, R.residue ⟨x, h⟩ ≠ 0) : ∃ h : y ∈ R.integers, R.residue ⟨y, h⟩ ≠ 0 := by
  subst hxy; exact hx

theorem gu_mul (R : RegularProlongation A F Fbar) {x y : F} (hx : ∃ h : x ∈ R.integers, R.residue ⟨x, h⟩ ≠ 0)
    (hy : ∃ h : y ∈ R.integers, R.residue ⟨y, h⟩ ≠ 0) : ∃ h : x * y ∈ R.integers, R.residue ⟨x * y, h⟩ ≠ 0 := by
  obtain ⟨hx, hxr⟩ := hx
  obtain ⟨hy, hyr⟩ := hy
  refine ⟨mul_mem hx hy, ?_⟩
  have : (⟨x * y, mul_mem hx hy⟩ : R.integers) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
  rw [this, map_mul]
  exact mul_ne_zero hxr hyr

theorem gu_inv (R : RegularProlongation A F Fbar) {x : F} (hx : ∃ h : x ∈ R.integers, R.residue ⟨x, h⟩ ≠ 0) :
    ∃ h : x⁻¹ ∈ R.integers, R.residue ⟨x⁻¹, h⟩ ≠ 0 := by
  obtain ⟨hf, h⟩ := hx
  obtain ⟨u, hu⟩ := R.isUnit_of_residue_ne_zero h
  have hcoe : ((u : R.integers) : F) = x := by rw [hu]
  have hinv : (((u⁻¹ : (↥R.integers)ˣ) : R.integers) : F) = x⁻¹ := by rw [coe_units_inv, hcoe]
  have hmem : x⁻¹ ∈ R.integers := hinv ▸ SetLike.coe_mem _
  refine ⟨hmem, ?_⟩
  have hx : (⟨x⁻¹, hmem⟩ : R.integers) = ((u⁻¹ : (↥R.integers)ˣ) : R.integers) := Subtype.ext hinv.symm
  rw [hx]
  exact R.residue_ne_zero_of_isUnit (Units.isUnit _)

end Gauss

end ClearSol
p2m_reactivate "P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen.ClearSol"

open ClearSol

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
          y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
          𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ) (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ)

    (hcompat : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        (𝔛.Mfib A hA ρ hρ).placeOfPoint P0 =
          if i = 0 then Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y)
          else Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y))
    (hcompat' : ∀ (i : Fin 2)
        (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
        (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase p (ΓM M H) hj))
        (_ : barPt A ≫ u.1 = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _)
        (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (Γ := ΓM M H) (hj := hj) ((IsLocalRing.residue ↥A).comp ρ))
        (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1)
        (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
        (P0 : closedPoints (𝔛.Mfib A hA ρ hρ).C)
        (_ : (𝔛.efib A hA ρ hρ ≫ 𝔛.comp A hA ρ hρ i).base P0.1 = uκ.base (IsLocalRing.closedPoint (ResidueField ↥A))),
        if i = 0 then
          Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (𝔛.Meta.pointEquivPlace y) =
            δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))
        else
          Psp.reduceFst α hα (𝔛.Meta.pointEquivPlace y) =
            qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p ((𝔛.Mfib A hA ρ hρ).placeOfPoint P0))

    (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hRL : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hNV : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)

    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (s : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) ×
      Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) (hs : s ∈ SS)
    (es : ℕ) (hes : 0 < es) (An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H))
    (hdom : ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W))
    (hmodulus : ∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ es * u)
    (hinert : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
      (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param)
    (hz₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers)
    (hz₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0)
    (hatt₂ : ∃ h₂ : An.param ∈ Rpd.R₂.integers, s.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))
    (hatt₁ : ∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
      s.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
      ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
        (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
          ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
            (-(s.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A))

    (E : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ) (hE : ∀ V, E V ≠ 0 → V ∈ An.dom)
    (d : ℤ) (u : ↥A) (hu : IsUnit u)
    (hbal : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d
      = E.prod (fun V m => (-(V.evalAt An.param)) ^ m)) :
    ∃ f : ↥(xHFunctionFieldBar M H), f ≠ 0 ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        (∃ t ∈ SS, Psp.reduceFst α hα V = t.1) → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → V.ord f = E V) ∧
      (∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        V.ord f ≠ 0 → ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V → ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V → ∃ t ∈ SS, Psp.reduceFst α hα V = t.1) ∧
      (∃ c : AlgebraicClosure ℚ,
        (∃ h₁ : c • f ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨c • f, h₁⟩ ≠ 0) ∧
        (∃ h₂ : c • f ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨c • f, h₂⟩ ≠ 0)) := by
  classical

  have hprime : p.Prime := Fact.out
  have hp0 : ((p : ℕ) : AlgebraicClosure ℚ) ≠ 0 := by exact_mod_cast hprime.ne_zero
  obtain ⟨uπ, huπ, hmod⟩ := id hmodulus
  have hπ0 : ((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    rw [hmod]
    push_cast
    refine mul_ne_zero (pow_ne_zero _ ?_) ?_
    · exact_mod_cast hp0
    · intro h0
      apply huπ.ne_zero
      exact_mod_cast h0
  have hvπ0 : A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) ≠ 0 := (map_ne_zero _).mpr hπ0
  have hvπ0' : 0 < A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) := zero_lt_iff.mpr hvπ0
  have hvπ1 : A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) < 1 := (A.valuation_lt_one_iff _).mp An.modulus_mem

  have hwin : ∀ V ∈ An.dom, A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation (V.evalAt An.param) ∧
      A.valuation (V.evalAt An.param) < 1 ∧ V.evalAt An.param ≠ 0 := fun V hV => valuation_evalAt_param An hV

  have hEp_dom : ∀ V, pPart E V ≠ 0 → V ∈ An.dom := fun V h => hE V (pPart_ne_zero E h)
  have hEn_dom : ∀ V, nPart E V ≠ 0 → V ∈ An.dom := fun V h => hE V (nPart_ne_zero E h)
  have hbase0 : ∀ V ∈ E.support, -(V.evalAt An.param) ≠ 0 := fun V hV =>
    neg_ne_zero.mpr (hwin V (hE V (Finsupp.mem_support_iff.mp hV))).2.2
  have hsplit := prod_zpow_eq_pPart_div_nPart E (fun V => -(V.evalAt An.param)) hbase0

  obtain ⟨Pp, hPp⟩ : ∃ Pp : AlgebraicClosure ℚ, Pp = (pPart E).prod (fun V n => (-(V.evalAt An.param)) ^ n) := ⟨_, rfl⟩
  obtain ⟨Pn, hPn⟩ : ∃ Pn : AlgebraicClosure ℚ, Pn = (nPart E).prod (fun V n => (-(V.evalAt An.param)) ^ n) := ⟨_, rfl⟩
  have hPn0 : Pn ≠ 0 := by
    rw [hPn]
    exact Finset.prod_ne_zero_iff.mpr fun V hV => zpow_ne_zero _ (hbase0 V (support_nPart E hV))
  have hPp0 : Pp ≠ 0 := by
    rw [hPp]
    exact Finset.prod_ne_zero_iff.mpr fun V hV => zpow_ne_zero _ (hbase0 V (support_pPart E hV))

  have hu0 : ((u : ↥A) : AlgebraicClosure ℚ) ≠ 0 := by
    intro h0
    apply hu.ne_zero
    exact_mod_cast h0
  have hU0 : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d ≠ 0 :=
    mul_ne_zero hu0 (zpow_ne_zero _ hπ0)
  have hPn_eq : Pn = Pp * (((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d)⁻¹ := by
    have h1 : ((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d = Pp / Pn := by
      rw [hbal, hsplit, hPp, hPn]
    rw [eq_div_iff hPn0] at h1

    rw [← h1, mul_comm _ Pn, mul_assoc, mul_inv_cancel₀ hU0, mul_one]

  have hfac : ∀ q ∈ (pPart E).support.sigma (fun V => Finset.range (pPart E V).toNat),
      A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation (-(q.1.evalAt An.param)) ∧
        A.valuation (-(q.1.evalAt An.param)) ≤ 1 := by
    intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨h1, h2, -⟩ := hwin q.1 (hEp_dom q.1 (Finsupp.mem_support_iff.mp hq.1))
    rw [Valuation.map_neg]
    exact ⟨h1, h2.le⟩
  obtain ⟨k, hk1, hk2⟩ := exists_pow_lt_prod_le_pow _ hvπ0 hvπ1
    ((pPart E).support.sigma (fun V => Finset.range (pPart E V).toNat))
    (fun q : (Σ _ : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), ℕ) => A.valuation (-(q.1.evalAt An.param))) hfac
  have hvPp : A.valuation Pp = ∏ q ∈ (pPart E).support.sigma (fun V => Finset.range (pPart E V).toNat),
      A.valuation (-(q.1.evalAt An.param)) := by
    rw [hPp, prod_zpow_eq_prod_sigma (pPart E) (pPart_nonneg E), map_prod]
  rw [← hvPp] at hk1 hk2
  have hvPp0 : 0 < A.valuation Pp := zero_lt_iff.mpr ((map_ne_zero _).mpr hPp0)

  obtain ⟨ui, hui, hui_coe⟩ := exists_inv_of_isUnit hu
  have hpad : ∃ (Epad : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ) (dp dn : ℤ) (up un : ↥A),
      (∀ V, Epad V ≠ 0 → V ∈ An.dom) ∧ (∀ V, 0 ≤ Epad V) ∧ IsUnit up ∧ IsUnit un ∧
      ((up : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ dp
        = (pPart E + Epad).prod (fun V n => (-(V.evalAt An.param)) ^ n) ∧
      ((un : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ dn
        = (nPart E + Epad).prod (fun V n => (-(V.evalAt An.param)) ^ n) := by
    by_cases heq : A.valuation Pp = A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k
    ·
      have hunit : A.valuation (Pp * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv₀, map_pow, heq, mul_inv_cancel₀ (pow_ne_zero _ hvπ0)]
      obtain ⟨hupA, hup⟩ := isUnit_of_valuation_eq_one hunit
      refine ⟨0, (k : ℤ), (k : ℤ) - d, ⟨_, hupA⟩, ⟨_, hupA⟩ * ui, ?_, ?_, hup, hup.mul hui, ?_, ?_⟩
      · intro V hV; exact absurd (Finsupp.zero_apply (a := V)) hV
      · intro V; simp
      · rw [add_zero, ← hPp, zpow_natCast]
        show Pp * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹ * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k = Pp
        rw [mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hπ0), mul_one]
      · rw [add_zero, ← hPn, hPn_eq, MulMemClass.coe_mul, hui_coe]
        show Pp * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹ * ((u : ↥A) : AlgebraicClosure ℚ)⁻¹ *
            ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ ((k : ℤ) - d) =
          Pp * (((u : ↥A) : AlgebraicClosure ℚ) * ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d)⁻¹
        rw [zpow_sub₀ hπ0, zpow_natCast, mul_inv]
        field_simp
    ·
      have hlt : A.valuation Pp < A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k := lt_of_le_of_ne hk2 heq
      set c : AlgebraicClosure ℚ := ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ (k + 1) * Pp⁻¹ with hc_def
      set r : AlgebraicClosure ℚ := Pp * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹ with hr_def
      have hvc : A.valuation c = A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ (k + 1) * (A.valuation Pp)⁻¹ := by
        rw [hc_def, map_mul, map_pow, map_inv₀]
      have hvr : A.valuation r = A.valuation Pp * (A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ k)⁻¹ := by
        rw [hr_def, map_mul, map_inv₀, map_pow]
      have hvc1 : A.valuation c < 1 := by
        rw [hvc, mul_inv_lt_iff₀ hvPp0, one_mul]
        exact hk1
      have hvcπ : A.valuation ((An.modulus : ↥A) : AlgebraicClosure ℚ) < A.valuation c := by
        rw [hvc, lt_mul_inv_iff₀ hvPp0, pow_succ']
        exact mul_lt_mul_of_pos_left hlt hvπ0'
      have hvr1 : A.valuation r < 1 := by
        rw [hvr, mul_inv_lt_iff₀ (pow_pos hvπ0' _), one_mul]
        exact hlt
      have hc0 : c ≠ 0 := by rw [hc_def]; exact mul_ne_zero (pow_ne_zero _ hπ0) (inv_ne_zero hPp0)
      have hcA : c ∈ A := (A.valuation_le_one_iff c).mp hvc1.le
      have hcm : (⟨c, hcA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨c, hcA⟩).mpr hvc1
      have hrA : r ∈ A := (A.valuation_le_one_iff r).mp hvr1.le
      have hrm : (⟨r, hrA⟩ : ↥A) ∈ maximalIdeal ↥A := (A.valuation_lt_one_iff ⟨r, hrA⟩).mpr hvr1
      have hcr : ((An.modulus : ↥A) : AlgebraicClosure ℚ) = c * r := by
        rw [hc_def, hr_def]
        field_simp
        ring
      have hcPp : Pp * c = ((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ (k + 1) := by
        rw [hc_def]; field_simp
      obtain ⟨W, ⟨hWdom, hWz⟩, -⟩ := An.existsUnique_evalAt_eq ⟨c, hcA⟩ hcm hc0 ⟨⟨r, hrA⟩, hrm, hcr⟩
      have hWz' : W.evalAt An.param = c := hWz

      have hmul : ∀ (G : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) →₀ ℤ), (∀ V, G V ≠ 0 → V ∈ An.dom) →
          (G + Finsupp.single W 1).prod (fun V n => (-(V.evalAt An.param)) ^ n)
            = G.prod (fun V n => (-(V.evalAt An.param)) ^ n) * (-c) := by
        intro G hG
        rw [Finsupp.prod_add_index, Finsupp.prod_single_index (zpow_zero _), zpow_one, hWz']
        · intro V _; exact zpow_zero _
        · intro V hV b₁ b₂
          have hVdom : V ∈ An.dom := by
            rcases Finset.mem_union.mp hV with h | h
            · exact hG V (Finsupp.mem_support_iff.mp h)
            · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at h
              split_ifs at h with hWV
              · exact hWV ▸ hWdom
              · exact absurd rfl h
          exact zpow_add₀ (neg_ne_zero.mpr (hwin V hVdom).2.2) b₁ b₂
      refine ⟨Finsupp.single W 1, ((k + 1 : ℕ) : ℤ), ((k + 1 : ℕ) : ℤ) - d, -1, -ui, ?_, ?_, isUnit_one.neg, hui.neg, ?_, ?_⟩
      · intro V hV
        rw [Finsupp.single_apply] at hV
        split_ifs at hV with hWV
        · exact hWV ▸ hWdom
        · exact absurd rfl hV
      · intro V
        rw [Finsupp.single_apply]
        split_ifs <;> norm_num
      · rw [hmul _ hEp_dom, ← hPp, zpow_natCast, mul_neg, hcPp]
        push_cast
        ring
      · rw [hmul _ hEn_dom, ← hPn, hPn_eq, zpow_sub₀ hπ0, zpow_natCast, mul_neg, mul_inv,
          show Pp * ((((u : ↥A) : AlgebraicClosure ℚ))⁻¹ * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d)⁻¹) * c =
            (Pp * c) * ((((u : ↥A) : AlgebraicClosure ℚ))⁻¹ * (((An.modulus : ↥A) : AlgebraicClosure ℚ) ^ d)⁻¹) by ring,
          hcPp]
        push_cast
        rw [hui_coe]
        field_simp
  obtain ⟨Epad, dp, dn, up, un, hpad_dom, hpad0, hup, hun, hbalp, hbaln⟩ := hpad

  have hEpP_dom : ∀ V, (pPart E + Epad) V ≠ 0 → V ∈ An.dom := by
    intro V hV
    rw [Finsupp.add_apply] at hV
    by_cases h1 : pPart E V = 0
    · rw [h1, zero_add] at hV; exact hpad_dom V hV
    · exact hEp_dom V h1
  have hEnP_dom : ∀ V, (nPart E + Epad) V ≠ 0 → V ∈ An.dom := by
    intro V hV
    rw [Finsupp.add_apply] at hV
    by_cases h1 : nPart E V = 0
    · rw [h1, zero_add] at hV; exact hpad_dom V hV
    · exact hEn_dom V h1
  have hEpP0 : ∀ V, 0 ≤ (pPart E + Epad) V := fun V => by
    rw [Finsupp.add_apply]; exact add_nonneg (pPart_nonneg E V) (hpad0 V)
  have hEnP0 : ∀ V, 0 ≤ (nPart E + Epad) V := fun V => by
    rw [Finsupp.add_apply]; exact add_nonneg (nPart_nonneg E V) (hpad0 V)

  obtain ⟨gp, ⟨hgp₁, hgpr₁, -⟩, ⟨hgp₂, hgpr₂, -⟩, hchip_p, hseam_p⟩ :=
    ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
      hO hRL hNV hθgal hβ_coe s hs es hes An hdom hmodulus hinert hz₁ hz₂ hatt₂ hatt₁
      (pPart E + Epad) hEpP_dom hEpP0 dp up hup hbalp
  obtain ⟨gn, ⟨hgn₁, hgnr₁, -⟩, ⟨hgn₂, hgnr₂, -⟩, hchip_n, hseam_n⟩ :=
    ModularCurve.XHDRModelAtP.exists_ord_residue_eq_and_ord_eq_of_nonneg_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
      p M H hpM hpM2 hHp hj 𝔛 A hA ρ hρ pb hpb δ hδ SS hSS θ α hα hβ Psp Rpd hwgen hα_coe hTD hmodel hcompat hcompat'
      hO hRL hNV hθgal hβ_coe s hs es hes An hdom hmodulus hinert hz₁ hz₂ hatt₂ hatt₁
      (nPart E + Epad) hEnP_dom hEnP0 dn un hun hbaln
  have hgp0 : gp ≠ 0 := gu_ne_zero Rpd.R₁ ⟨hgp₁, hgpr₁⟩
  have hgn0 : gn ≠ 0 := gu_ne_zero Rpd.R₁ ⟨hgn₁, hgnr₁⟩

  have hord : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), V.ord (gp * gn⁻¹) = V.ord gp - V.ord gn := by
    intro V
    rw [V.ord_mul hgp0 (inv_ne_zero hgn0), V.ord_inv]
    ring
  refine ⟨gp * gn⁻¹, mul_ne_zero hgp0 (inv_ne_zero hgn0), ?_, ?_, 1, ?_, ?_⟩
  ·
    intro V hVt hV1 hV2
    rw [hord V, hchip_p V hVt hV1 hV2, hchip_n V hVt hV1 hV2, Finsupp.add_apply, Finsupp.add_apply,
      ← pPart_sub_nPart E V]
    ring
  ·
    intro V hV hV1 hV2
    rw [hord V] at hV
    by_cases hp' : V.ord gp = 0
    · rw [hp', zero_sub, neg_ne_zero] at hV
      exact hseam_n V hV hV1 hV2
    · exact hseam_p V hp' hV1 hV2
  ·
    exact gu_congr Rpd.R₁ (one_smul _ _).symm (gu_mul Rpd.R₁ ⟨hgp₁, hgpr₁⟩ (gu_inv Rpd.R₁ ⟨hgn₁, hgnr₁⟩))
  ·
    exact gu_congr Rpd.R₂ (one_smul _ _).symm (gu_mul Rpd.R₂ ⟨hgp₂, hgpr₂⟩ (gu_inv Rpd.R₂ ⟨hgn₂, hgnr₂⟩))

end S_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_ord_eq_and_smul_mem_integers_of_isUnit_mul_modulus_zpow_eq_prod_neg_evalAt_zpow_of_annulus_offDiag_of_wgen (solution)
