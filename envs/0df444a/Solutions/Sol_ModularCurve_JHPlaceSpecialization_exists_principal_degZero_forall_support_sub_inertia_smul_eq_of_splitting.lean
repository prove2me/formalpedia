-- Prove2me | solution 1 for ModularCurve.JHPlaceSpecialization.exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/39027c23-8593-5b3e-8bf6-1040cf2c52b9

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_AlgebraicCurve_SemistableCharts
import Definitions.Def_ModularCurve_JHNodeDepth
import Definitions.Def_ModularCurve_JHNodeDepthInf
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn
import Theorems.Thm_ModularCurve_place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_isCurveOver_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_exists_weilCanonical_riemannRoch
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar
import Theorems.Thm_ModularCurve_qExpFrobeniusPlaceModL_bijective
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_ProlongationDatum_IsModel_exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit
import Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHPlaceSpecialization_exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.XHDRModelAtP.Mfib_chart_nonempty ModularCurve.XHDRModelAtP.Meta_chart_nonempty ModularCurve.XHDRModelAtP.smoothLocus_relDim ModularCurve.XHDRModelAtP.efib_iso ModularCurve.XHDRLevel.fact_jAt_ne_zero ModularCurve.XHDRModelAtP.eeta_iso ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing"
p2m_attr_erase "instance" "TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid"
p2m_attr_erase "instance" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback SheafOfModules.isIso_ihomModelToIhom"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.baseAut_x1ArithFrobC_apply ModularCurve.coe_qExpCoeffRingAut_apply ModularCurve.qExpCoeffSemilinearAutHom_apply ModularCurve.baseAut_x1x0ArithFrobC_apply ModularCurve.baseAut_qExpArithFrobC_apply ModularCurve.baseAut_qExpCoeffSemilinearAut ModularCurve.toRingAut_qExpCoeffSemilinearAut compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.XHDRModelAtP.mk.sizeOf_spec ModularCurve.XHDRLevel.coe_jAt ModularCurve.XHDRModelAtP.πw_val ModularCurve.XHDRModelAtP.mk.injEq ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.LevelN.coe_jGen HahnSeries.ramScale_apply ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun"
p2m_attr_erase "simp" "ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂"
p2m_attr_erase "simp" "TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma ModularForm.coe_atkinLehnerLin_apply CuspForm.coe_atkinLehnerLin_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.coe_jqNGen ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaOneBarOf ModularCurve.coe_heckeAlphaOneBar AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk"

set_option autoImplicit false

p2m_open "AlgebraicCurve~genus IsLocalRing ModularCurve ModularCurve.JHNeronObjectAtP"
open scoped MatrixGroups

open Classical in

/-!                                                                                                                            -/

noncomputable section

set_option linter.unusedSectionVars false

namespace SndFix

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] [NeZero (M / p)]

set_option quotPrecheck false
local notation "κ" => ResidueField ↥A
local notation "FM" => ↥(xHFunctionFieldBar M H)
local notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))
local notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)
local notation "Gal" => arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H)

theorem not_isStrictFst_of_isStrictSnd (Psp : JHPlaceSpecialization p M H hpM A)
    (α β : FMp →ₐ[AlgebraicClosure ℚ] FM) (hα : α.IsIntegral) (hβ : β.IsIntegral) (δ : Place κ Fb → Place κ Fb)
    {W : Place (AlgebraicClosure ℚ) FM} (h2 : Psp.IsStrictSnd α β hα hβ δ W) : ¬ Psp.IsStrictFst α β hα hβ δ W := by
  intro h1
  apply h1.2
  show qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p
      (δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W))) = Psp.reduceFst α hα W
  have e1 : δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα W)) = Psp.reduceSnd β hβ δ W := h1.1
  have e2 : Psp.reduceFst α hα W = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd β hβ δ W) := h2.1
  rw [e1, ← e2]

def IFixed (A : ValuationSubring (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) FM) : Prop :=
  ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • V = V

def orbit (A : ValuationSubring (AlgebraicClosure ℚ)) (V : Place (AlgebraicClosure ℚ) FM) : Set (Place (AlgebraicClosure ℚ) FM) :=
  {V' | ∃ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • V = V'}

theorem self_mem_orbit (V : Place (AlgebraicClosure ℚ) FM) : V ∈ orbit (M := M) (H := H) A V := ⟨1, one_mem _, by rw [map_one, one_smul]⟩

theorem orbit_subset_support {E : Divisor (AlgebraicClosure ℚ) FM} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • E = E)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : V ∈ E.support) : orbit (M := M) (H := H) A V ⊆ ↑E.support := by
  rintro V' ⟨σ, hσ, rfl⟩
  rw [Finset.mem_coe, Finsupp.mem_support_iff, ← hst σ hσ, SemilinearAut.divisor_smul_apply, inv_smul_smul]
  exact Finsupp.mem_support_iff.mp hV

theorem orbit_finite {E : Divisor (AlgebraicClosure ℚ) FM} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • E = E)
    {V : Place (AlgebraicClosure ℚ) FM} (hV : V ∈ E.support) : (orbit (M := M) (H := H) A V).Finite :=
  (E.support.finite_toSet).subset (orbit_subset_support hst hV)

theorem apply_eq_of_mem_orbit {E : Divisor (AlgebraicClosure ℚ) FM} (hst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • E = E)
    {V V' : Place (AlgebraicClosure ℚ) FM} (hV' : V' ∈ orbit (M := M) (H := H) A V) : E V' = E V := by
  obtain ⟨σ, hσ, rfl⟩ := hV'
  conv_lhs => rw [← hst σ hσ]
  exact SemilinearAut.divisor_smul_apply_smul _ _ _

theorem not_fixed_of_mem_orbit {V V' : Place (AlgebraicClosure ℚ) FM} (hV : ¬ IFixed (M := M) (H := H) A V)
    (hV' : V' ∈ orbit (M := M) (H := H) A V) : ¬ IFixed (M := M) (H := H) A V' := by
  obtain ⟨τ, hτ, rfl⟩ := hV'
  intro hfix
  apply hV
  intro σ hσ
  have h := hfix (τ * σ * τ⁻¹) (mul_mem (mul_mem hτ hσ) (inv_mem hτ))
  rw [map_mul, map_mul, map_inv, mul_smul, mul_smul, inv_smul_smul] at h
  exact smul_left_cancel _ h

theorem exists_eq_of_sum_single_apply_ne_zero {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) FM) (V : Place (AlgebraicClosure ℚ) FM)
    (hV : (∑ i, Finsupp.single (Q i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) V ≠ 0) : ∃ i, Q i = V := by
  classical
  rw [Finsupp.finsetSum_apply] at hV
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hV
  rw [Finsupp.single_apply] at hi
  split_ifs at hi with h
  · exact ⟨i, h⟩
  · exact absurd rfl hi

theorem sum_single_apply_nonneg {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) FM) (V : Place (AlgebraicClosure ℚ) FM) :
    (0 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) V := by
  classical
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i' _ => by rw [Finsupp.single_apply]; split_ifs <;> norm_num

theorem one_le_sum_single_apply_self {d : ℕ} (Q : Fin d → Place (AlgebraicClosure ℚ) FM) (i : Fin d) :
    (1 : ℤ) ≤ (∑ i', Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) (Q i) := by
  classical
  rw [Finsupp.finsetSum_apply]
  have h : ∀ i' ∈ (Finset.univ : Finset (Fin d)), (0 : ℤ) ≤ (Finsupp.single (Q i') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) (Q i) := by
    intro i' _; rw [Finsupp.single_apply]; split_ifs <;> norm_num
  refine le_trans ?_ (Finset.single_le_sum h (Finset.mem_univ i))
  rw [Finsupp.single_eq_same]

theorem degFM (V : Place (AlgebraicClosure ℚ) FM) : V.deg = 1 := ModularCurve.place_deg_eq_one_laurentBaseChange_qExpFunctionFieldC
    (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) (ModularCurve.translation_mem_GammaH M H) (xHFunctionField M H) rfl V

theorem degree_finset_sum_single (O : Finset (Place (AlgebraicClosure ℚ) FM)) :
    Divisor.degree (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) = O.card := by
  rw [map_sum]
  simp only [Divisor.degree_single, degFM, Nat.cast_one, mul_one, Finset.sum_const, nsmul_eq_mul]

theorem smul_sum_single_of_orbit {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (V : Place (AlgebraicClosure ℚ) FM) (O : Finset (Place (AlgebraicClosure ℚ) FM))
    (hO : ∀ V', V' ∈ O ↔ ∃ τ ∈ A.inertiaSubgroupIn ℚ, Gal τ • V = V') :
    Gal σ • (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) = ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) := by
  classical
  rw [Finset.smul_sum]
  simp only [SemilinearAut.smul_single]
  refine Finset.sum_nbij (fun V' => Gal σ • V') (fun V' hV' => ?_) (fun a _ b _ h => smul_left_cancel _ h)
    (fun V' hV' => ?_) (fun _ _ => rfl)
  · rw [hO] at hV' ⊢
    obtain ⟨τ, hτ, rfl⟩ := hV'
    exact ⟨σ * τ, mul_mem hσ hτ, by rw [map_mul, mul_smul]⟩
  · rw [Finset.mem_coe, hO] at hV'
    obtain ⟨τ, hτ, rfl⟩ := hV'
    refine ⟨(Gal σ)⁻¹ • (Gal τ • V), ?_, ?_⟩
    · rw [Finset.mem_coe, hO]
      exact ⟨σ⁻¹ * τ, mul_mem (inv_mem hσ) hτ, by rw [map_mul, map_inv, mul_smul]⟩
    · dsimp only
      rw [smul_inv_smul]

open Classical in

theorem exists_fixing_corrector (Good : Place (AlgebraicClosure ℚ) FM → Prop)
    (horbit : ∀ V : Place (AlgebraicClosure ℚ) FM, Good V → ∀ O : Finset (Place (AlgebraicClosure ℚ) FM),
      (∀ V', V' ∈ O ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • V = V') →
      ∃ D : Divisor (AlgebraicClosure ℚ) FM,
        (∀ V' ∈ D.support, IFixed (M := M) (H := H) A V' ∧ Good V') ∧
        ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) - D) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := FM) ∧
        ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) FM) - D) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM)) :
    ∀ (n : ℕ) (E : Divisor (AlgebraicClosure ℚ) FM),
      (E.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V)).card ≤ n →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • E = E) →
      (∀ V ∈ E.support, Good V) →
      ∃ C : Divisor (AlgebraicClosure ℚ) FM,
        C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := FM) ∧ C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := FM) ∧
        ∀ V ∈ (E - C).support, IFixed (M := M) (H := H) A V ∧ Good V := by
  classical
  intro n
  induction n with
  | zero =>
    intro E hcard _ hgood
    refine ⟨0, zero_mem _, zero_mem _, fun V hV => ?_⟩
    rw [sub_zero] at hV
    refine ⟨?_, hgood V hV⟩
    by_contra hnf
    have : V ∈ E.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V) := Finset.mem_filter.mpr ⟨hV, hnf⟩
    rw [Nat.le_zero, Finset.card_eq_zero] at hcard
    rw [hcard] at this
    exact absurd this (Finset.notMem_empty V)
  | succ n ih =>
    intro E hcard hst hgood
    by_cases hex : ∃ V ∈ E.support, ¬ IFixed (M := M) (H := H) A V
    swap
    · push_neg at hex
      exact ⟨0, zero_mem _, zero_mem _, fun V hV => by rw [sub_zero] at hV; exact ⟨hex V hV, hgood V hV⟩⟩
    obtain ⟨V, hVE, hVnf⟩ := hex
    have hfin := orbit_finite hst hVE
    have hOmem : ∀ V', V' ∈ hfin.toFinset ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • V = V' := fun V' => by
      rw [Set.Finite.mem_toFinset]; rfl
    obtain ⟨D, hDfg, hprin, hdeg⟩ := horbit V (hgood V hVE) hfin.toFinset hOmem
    obtain ⟨Orb, hOrb⟩ : ∃ Orb : Divisor (AlgebraicClosure ℚ) FM, Orb = ∑ V' ∈ hfin.toFinset, Finsupp.single V' (1 : ℤ) := ⟨_, rfl⟩
    rw [← hOrb] at hprin hdeg
    have hOrb_apply : ∀ V', Orb V' = if V' ∈ orbit (M := M) (H := H) A V then 1 else 0 := by
      intro V'
      rw [hOrb, Finsupp.finsetSum_apply]
      simp only [Finsupp.single_apply]
      rw [Finset.sum_ite_eq' hfin.toFinset V' (fun _ => (1 : ℤ))]
      simp only [Set.Finite.mem_toFinset]
    have hDst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • D = D := by
      intro σ hσ
      rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hDfg V' hV').1 σ hσ), Finsupp.mapDomain_id]
    obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Divisor (AlgebraicClosure ℚ) FM, E₁ = E - E V • (Orb - D) := ⟨_, rfl⟩
    have hst₁ : ∀ σ ∈ A.inertiaSubgroupIn ℚ, Gal σ • E₁ = E₁ := by
      intro σ hσ
      rw [hE₁, smul_sub, smul_comm, smul_sub, hst σ hσ, hOrb, smul_sum_single_of_orbit hσ V _ hOmem, hDst σ hσ]
    have hsub : E₁.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V) ⊆ (E.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V)).erase V := by
      intro V' hV'
      obtain ⟨hV'E₁, hV'nf⟩ := Finset.mem_filter.mp hV'
      have hDV' : D V' = 0 := by
        by_contra h
        exact hV'nf ((hDfg V' (Finsupp.mem_support_iff.mpr h)).1)
      rw [Finsupp.mem_support_iff, hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, hDV', sub_zero,
        hOrb_apply, smul_eq_mul] at hV'E₁
      by_cases hVo : V' ∈ orbit (M := M) (H := H) A V
      · exfalso; apply hV'E₁
        rw [if_pos hVo, mul_one, apply_eq_of_mem_orbit hst hVo, sub_self]
      · rw [if_neg hVo, mul_zero, sub_zero] at hV'E₁
        refine Finset.mem_erase.mpr ⟨fun h => hVo ?_, Finset.mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hV'E₁, hV'nf⟩⟩
        rw [h]; exact self_mem_orbit V
    have hcard₁ : (E₁.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V)).card ≤ n := by
      have h1 := Finset.card_le_card hsub
      have hVmem : V ∈ E.support.filter (fun V => ¬ IFixed (M := M) (H := H) A V) := Finset.mem_filter.mpr ⟨hVE, hVnf⟩
      have h2 := Finset.card_erase_of_mem hVmem
      omega
    have hgood₁ : ∀ V' ∈ E₁.support, Good V' := by
      intro V' hV'
      by_cases h1 : V' ∈ E.support
      · exact hgood V' h1
      · by_cases h2 : V' ∈ D.support
        · exact (hDfg V' h2).2
        · exfalso
          apply Finsupp.mem_support_iff.mp hV'
          have hEV' : E V' = 0 := Finsupp.notMem_support_iff.mp h1
          have hVo : V' ∉ orbit (M := M) (H := H) A V := fun h => h1 (orbit_subset_support hst hVE h)
          rw [hE₁, Finsupp.sub_apply, Finsupp.smul_apply, Finsupp.sub_apply, Finsupp.notMem_support_iff.mp h2, hEV',
            hOrb_apply, if_neg hVo]
          simp
    obtain ⟨C', hC'p, hC'd, hC'fg⟩ := ih E₁ hcard₁ hst₁ hgood₁
    refine ⟨E V • (Orb - D) + C', add_mem (zsmul_mem hprin _) hC'p, add_mem (zsmul_mem hdeg _) hC'd, fun V' hV' => ?_⟩
    apply hC'fg V'
    rwa [hE₁, sub_sub]

theorem isCurveOver_Fb : IsCurveOver κ Fb :=
  ModularCurve.isCurveOver_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM)
    (ModularCurve.translation_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))

theorem essFiniteType_Fb : Algebra.EssFiniteType κ Fb := by
  obtain ⟨x, -, htr, hfd⟩ := ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed (ResidueField ↥A)
    (JHNeronObjectAtP.ΓN p M H hpM) (ModularCurve.translation_mem_GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))
  exact AlgebraicCurve.essFiniteType_of_transcendental_of_finiteDimensional htr hfd

theorem exists_rr_Fb (hpM2 : ¬ p ^ 2 ∣ M) :
    ∃ Kc : Divisor κ Fb, ∀ D : Divisor κ Fb, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - (genusFF κ Fb : ℤ) := by
  haveI := isCurveOver_Fb (p := p) (M := M) (H := H) (hpM := hpM) (A := A)
  haveI := essFiniteType_Fb (p := p) (M := M) (H := H) (hpM := hpM) (A := A)
  exact AlgebraicCurve.exists_weilCanonical_riemannRoch κ Fb
    (ModularCurve.JHNeronObjectAtP.hasPrincipalDivisors_and_constantsAreBase_and_surjective_residueField_fbar p M H hpM hpM2 κ).2.1

open Classical in

theorem card_image_fst_eq (SS : Finset (Place κ Fb × Place κ Fb))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :
    (SS.image Prod.fst).card = Nat.card ↥(ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) := by
  classical
  have hinj : Set.InjOn Prod.fst (SS : Set (Place κ Fb × Place κ Fb)) := by
    intro s hs t ht h
    have hs' := (ModularCurve.mem_ssNodePairsQExp_iff s).mp ((hSS s).mp hs)
    have ht' := (ModularCurve.mem_ssNodePairsQExp_iff t).mp ((hSS t).mp ht)
    have h2 : s.2 = t.2 := (ModularCurve.qExpFrobeniusPlaceModL_bijective (ResidueField ↥A) p (JHNeronObjectAtP.ΓN p M H hpM)).1
      (hs'.2.symm.trans (h.trans ht'.2))
    exact Prod.ext h h2
  rw [Finset.card_image_of_injOn hinj]
  have hset : (SS : Set (Place κ Fb × Place κ Fb)) = ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p := by
    ext s; rw [Finset.mem_coe]; exact hSS s
  rw [← hset, Nat.card_coe_set_eq, Set.ncard_coe_finset]

end SndFix

set_option maxHeartbeats 6400000 in
open SndFix in
open Classical in

theorem SndFix.forall_smul_eq_of_sub_mem_principal
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]

    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)

    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)

    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (hmodel : Rpd.IsModel α β hα hβ δ) (hO : Rpd.OrderLawFixed α β hα hβ δ)
    (hRL : Rpd.RegularityLaw α β hα hβ δ SS) (hNV : Rpd.NodeValueLaw α β hα hβ δ SS)

    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hβ_coe : ∀ u, ((β u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) = arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβθ : β = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α β hα hβ δ Q → Psp.IsStrictFst α β hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α β hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α β hα hβ δ Q → Psp.IsStrictSnd α β hα hβ δ Q' →
      Psp.reduceSnd β hβ δ Q' = Psp.reduceSnd β hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd β hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α β hα hβ δ W → Psp.reduceSnd β hβ δ W = Psp.reduceSnd β hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd β hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α β hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (Psp.sndDiv α β hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd β hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd β hβ δ C) =
            (Psp.reduceSnd β hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd β hβ δ C = w))
    {d₁ d₂ : ℕ} (Q₁' : Fin d₁ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (Q₂' : Fin d₂ → Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hQ₁' : ∀ i, Psp.IsStrictFst α β hα hβ δ (Q₁' i)) (hQ₂' : ∀ j, Psp.IsStrictSnd α β hα hβ δ (Q₂' j))
    (hinj₁' : Function.Injective fun i => Psp.reduceFst α hα (Q₁' i))
    (hinj₂' : Function.Injective fun j => Psp.reduceSnd β hβ δ (Q₂' j))
    {T₁ T₂ : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))}
    (hT₁' : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁' i) = v) (hT₂' : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd β hβ δ (Q₂' j) = v)
    (hT₁W : Disjoint T₁ (SS.image Prod.fst))
    (hT₁aff : ∀ v ∈ T₁, JHPlaceSpecialization.IsAffinePlace p M H hpM A v) (hT₂aff : ∀ v ∈ T₂, JHPlaceSpecialization.IsAffinePlace p M H hpM A v)
    (hgp₁ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₁ → 0 ≤ v.ord h) → (∀ v ∈ T₁, -1 ≤ v.ord h) → (∀ w ∈ (SS.image Prod.fst), w.HasValue h 0) → h = 0)
    (hgp₂ : ∀ h : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), v ∉ T₂ → 0 ≤ v.ord h) → (∀ v ∈ T₂, -1 ≤ v.ord h) → ∃ c : (ResidueField ↥A), h = algebraMap (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) c)
    (Qs : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hQs : Psp.IsStrictFst α β hα hβ δ Qs) (hQs'' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁' i))
    {σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ} (hσ : σ ∈ A.inertiaSubgroupIn ℚ)
    (hcls : ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) -
        (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) ∈
          Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) :
    (∀ i, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i = Q₁' i) ∧ (∀ j, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j = Q₂' j) := by

  have hred : ∀ V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.reduceFst α hα ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = Psp.reduceFst α hα V ∧
      Psp.reduceSnd β hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V) = Psp.reduceSnd β hβ δ V := fun V =>
    ModularCurve.JHPlaceSpecialization.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn p M H hpM A θ α β hα hβ δ Psp
      hα_coe hθgal hβθ σ hσ V
  have hQ₁'' : ∀ i, Psp.IsStrictFst α β hα hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) := fun i => by
    have h := hQ₁' i
    unfold JHPlaceSpecialization.IsStrictFst at h ⊢
    rw [(hred _).1, (hred _).2]; exact h
  have hQ₂'' : ∀ j, Psp.IsStrictSnd α β hα hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) := fun j => by
    have h := hQ₂' j
    unfold JHPlaceSpecialization.IsStrictSnd at h ⊢
    rw [(hred _).1, (hred _).2]; exact h
  have hred₁'' : ∀ i, Psp.reduceFst α hα ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) = Psp.reduceFst α hα (Q₁' i) := fun i => (hred _).1
  have hred₂'' : ∀ j, Psp.reduceSnd β hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) = Psp.reduceSnd β hβ δ (Q₂' j) := fun j => (hred _).2

  obtain ⟨f, hf0, hdivf⟩ := hcls
  have hsE1 : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) =
      ∑ i, Finsupp.single ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) (1 : ℤ) := by
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]; simp only [SemilinearAut.smul_single]
  have h1κ : ((1 : ℕ) : ResidueField ↥A) ≠ 0 := by rw [Nat.cast_one]; exact one_ne_zero

  have hE := ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.sum_single_add_sum_single_eq_of_ord_eq_nsmul_sub_of_gammaLift_of_discLaw_of_unit_of_cusp
    p M H hpM hpM2 hHp A hA θ α β hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hRL hNV hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Q₁' Q₂' hQ₁' hQ₂' hinj₁' hinj₂'
    (fun i => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) (fun j => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) hQ₁'' hQ₂'' hred₁'' hred₂''
    hT₁' hT₂' hT₁W hT₁aff hT₂aff hgp₁ hgp₂ Qs hQs hQs'' 1 h1κ f hf0
    (fun V => by rw [Nat.cast_one, one_mul, ← hdivf V, hsE1])

  constructor
  · intro i
    have hle := one_le_sum_single_apply_self (M := M) (H := H) (fun i => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) i
    have hmem : ((∑ i', Finsupp.single (Q₁' i') (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
        ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) ≠ 0 := by
      rw [← hE]
      intro h0
      rw [Finsupp.add_apply] at h0
      have h2 := sum_single_apply_nonneg (M := M) (H := H) (fun j => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i)
      omega
    rw [Finsupp.add_apply] at hmem
    by_cases hB : (∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) = 0
    · rw [hB, add_zero] at hmem
      obtain ⟨i', hi'⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₁' _ hmem
      have : i' = i := hinj₁' (by show Psp.reduceFst α hα (Q₁' i') = Psp.reduceFst α hα (Q₁' i); rw [hi', hred₁'' i])
      rw [← hi', this]
    · obtain ⟨j, hj⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₂' _ hB
      have h1 : Psp.IsStrictFst α β hα hβ δ (Q₂' j) := by rw [hj]; exact hQ₁'' i
      exact absurd h1 (not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ (hQ₂' j))
  · intro j
    have hle := one_le_sum_single_apply_self (M := M) (H := H) (fun j => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) j
    have hmem : ((∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j', Finsupp.single (Q₂' j') (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)))
        ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) ≠ 0 := by
      rw [← hE]
      intro h0
      rw [Finsupp.add_apply] at h0
      have h2 := sum_single_apply_nonneg (M := M) (H := H) (fun i => (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j)
      omega
    rw [Finsupp.add_apply] at hmem
    by_cases hB : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j) = 0
    · rw [hB, zero_add] at hmem
      obtain ⟨j', hj'⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₂' _ hmem
      have : j' = j := hinj₂' (by show Psp.reduceSnd β hβ δ (Q₂' j') = Psp.reduceSnd β hβ δ (Q₂' j); rw [hj', hred₂'' j])
      rw [← hj', this]
    · obtain ⟨i, hi⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₁' _ hB
      have h2 : Psp.IsStrictSnd α β hα hβ δ (Q₁' i) := by rw [hi]; exact hQ₂'' j
      exact absurd (hQ₁' i) (not_isStrictFst_of_isStrictSnd Psp α β hα hβ δ h2)

namespace SndFix

set_option maxHeartbeats 6400000 in
open SndFix in
open Classical in

theorem exists_fixed_good_rep_of_orbit_main
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))
    (hsplit : ∀ (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X) →
      (∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) →
      ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
        (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
        (∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
          GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) ∧
        ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) (hV : (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (O : Finset (Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) (hOrb : ∀ V', V' ∈ O ↔ ∃ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V') :
    ∃ D : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      (∀ V' ∈ D.support, SndFix.IFixed (M := M) (H := H) A V' ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V' ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V' ∨ ∃ s ∈ SS, Psp.reduceFst α hα V' = s.1)) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) ∧
      ((∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
  have hβθ : (θ.toAlgHom.comp α) = (θ : ↥(xHFunctionFieldBar M H) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H)).comp α := rfl

  have hred : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      Psp.reduceFst α hα ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W) = Psp.reduceFst α hα W ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W :=
    fun σ hσ W => ModularCurve.JHPlaceSpecialization.reduceFst_smul_eq_and_reduceSnd_smul_eq_of_mem_inertiaSubgroupIn p M H hpM A θ α (θ.toAlgHom.comp α) hα hβ δ Psp
      hα_coe hθgal hβθ σ hσ W
  have hgood_smul : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W ∨ ∃ s ∈ SS, Psp.reduceFst α hα W = s.1) → (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W) ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W) ∨ ∃ s ∈ SS, Psp.reduceFst α hα ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • W) = s.1) := by
    intro σ hσ W hW
    rcases hW with h | h | ⟨s, hs, hsW⟩
    · left; unfold JHPlaceSpecialization.IsStrictFst at h ⊢; rw [(hred σ hσ W).1, (hred σ hσ W).2]; exact h
    · right; left; unfold JHPlaceSpecialization.IsStrictSnd at h ⊢; rw [(hred σ hσ W).1, (hred σ hσ W).2]; exact h
    · right; right; exact ⟨s, hs, by rw [(hred σ hσ W).1, hsW]⟩

  obtain ⟨Kc, hRR⟩ := SndFix.exists_rr_Fb (p := p) (M := M) (H := H) (hpM := hpM) (A := A) hpM2

  have hGP := ModularCurve.JHPlaceSpecialization.exists_isStrictFst_isStrictSnd_generalPosition_disjoint_forall_inertia_smul_eq_of_gammaLift_of_unit
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit ∅ Kc (genusFF (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))) hRR
  obtain ⟨d₁, d₂, Q₁, Q₂, T₁, T₂, Qs, hd₁, hd₂, hQ₁, hQ₂, hinj₁, hinj₂, hT₁, hT₂, hT₁W, -, -, hT₁aff, hT₂aff, hgp₁, hgp₂, hQs, hQs', hI₁, hI₂⟩ := hGP

  have hcard := SndFix.card_image_fst_eq (p := p) (M := M) (H := H) (hpM := hpM) (A := A) SS hSS
  have hgen : genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) + 1 = 2 * genusFF (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) +
      Nat.card ↥(ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p) :=
    ModularCurve.genusFF_xHFunctionFieldBar_add_one_eq_two_mul_genusFF_add_natCard_ssNodePairsQExp p M H hpM hpM2 hHp (ResidueField ↥A)
  have hdeg : d₁ + d₂ = genusFF (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) := by omega

  have hFam := ModularCurve.JHPlaceSpecialization.exists_families_isStrictFst_isStrictSnd_notMem_forall_inertia_smul_eq_of_gammaLift_ed2
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit ∅ 1 0
  obtain ⟨Qb, -, hQb, -, -, -, -, -, hQbfix, -⟩ := hFam

  obtain ⟨Osum, hOsum⟩ : ∃ Osum : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Osum = ∑ V' ∈ O, Finsupp.single V' (1 : ℤ) := ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), X = Osum - (O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) := ⟨_, rfl⟩
  have hXdeg : X ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    rw [Divisor.mem_degZero, hX, map_sub, map_zsmul, hOsum, degree_finset_sum_single, Divisor.degree_single, degFM]
    simp
  have hXst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • X = X := by
    intro σ hσ
    rw [hX, smul_sub, hOsum, smul_sum_single_of_orbit hσ V O hOrb, smul_comm, SemilinearAut.smul_single, hQbfix 0 σ hσ]
  have hXgood : ∀ V' ∈ X.support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V' ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V' ∨ ∃ s ∈ SS, Psp.reduceFst α hα V' = s.1) := by
    intro V' hV'
    rw [Finsupp.mem_support_iff, hX, Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul] at hV'
    by_cases h1 : Osum V' = 0
    · rw [h1, zero_sub, neg_ne_zero, mul_ne_zero_iff, Finsupp.single_apply_ne_zero] at hV'
      rw [hV'.2.1]
      exact Or.inl (hQb 0)
    · rw [hOsum, Finsupp.finsetSum_apply] at h1
      obtain ⟨V'', hV''O, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h1
      rw [Finsupp.single_apply_ne_zero] at hne
      rw [hne.1]
      obtain ⟨τ, hτ, rfl⟩ := (hOrb V'').mp hV''O
      exact hgood_smul τ hτ V hV

  let Xz : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))) := ⟨X, hXdeg⟩
  have hXz : (Xz : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X := rfl
  clear_value Xz
  have hS := hsplit Xz (by rw [hXz]; exact hXst) (by rw [hXz]; exact hXgood)
  obtain ⟨D₁, D₂, hD₁, hD₂good, hglue, hprin⟩ := hS
  obtain ⟨hadm, hmk⟩ := hglue
  rw [hXz] at hprin

  have hC := ModularCurve.JHPlaceSpecialization.ProlongationDatum.IsModel.exists_isStrictFst_isStrictSnd_reduceFst_eq_reduceSnd_eq_pic0Mk_eq_of_isGoodDiv_of_gammaLift_of_unit_of_cusp
    p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Q₁ Q₂ hQ₁ hQ₂ hinj₁ hinj₂ hT₁ hT₂ hT₁W hT₁aff hT₂aff hgp₁ hgp₂ hdeg D₂ hD₂good hadm hmk
  obtain ⟨Q₁', Q₂', hQ₁', hQ₂', hred₁, hred₂, hdeg0, hx'⟩ := hC

  have hD₁st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = D₁ := by
    intro σ hσ
    rw [SemilinearAut.divisor_smul_def, Finsupp.mapDomain_congr (g := id) (fun V' hV' => (hD₁ V' hV').1 σ hσ), Finsupp.mapDomain_id]
  have hD₂cls : ∀ σ ∈ A.inertiaSubgroupIn ℚ,
      ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    intro σ hσ
    have hCσ := SemilinearAut.smul_mem_principal (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) hprin
    have : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₂ = -(((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X - D₁ - D₂)) - (X - D₁ - D₂)) := by
      rw [smul_sub, smul_sub, hXst σ hσ, hD₁st σ hσ]; abel
    rw [this]
    exact neg_mem (sub_mem hCσ hprin)

  obtain ⟨E0, hE0⟩ : ∃ E0 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), E0 = (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂ j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := ⟨_, rfl⟩
  obtain ⟨E1, hE1⟩ : ∃ E1 : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), E1 = (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) + ∑ j, Finsupp.single (Q₂' j) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) := ⟨_, rfl⟩
  have hE0st : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • E0 = E0 := by
    intro σ hσ
    rw [hE0, smul_add, Finset.smul_sum, Finset.smul_sum]
    simp only [SemilinearAut.smul_single, hI₁ _ σ hσ, hI₂ _ σ hσ]

  have h1 : ((E1 - E0) - (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    have hq := (QuotientAddGroup.eq (s := (Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H))).addSubgroupOf _)).mp hx'.symm
    rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_add, AddSubgroup.coe_neg] at hq
    have hc : ((⟨_, hdeg0⟩ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = E1 - E0 := by rw [hE1, hE0]
    rw [hc, neg_add_eq_sub] at hq
    exact hq

  have hcls : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • E1 - E1) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by
    intro σ hσ
    have hσ1 := SemilinearAut.smul_mem_principal (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) h1
    have : (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • E1 - E1 = ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • ((E1 - E0) - D₂) - ((E1 - E0) - D₂)) + ((arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₂) := by
      rw [smul_sub, smul_sub, hE0st σ hσ]; abel
    rw [this]
    exact add_mem (sub_mem hσ1 h1) (hD₂cls σ hσ)

  have hinj₁' : Function.Injective fun i => Psp.reduceFst α hα (Q₁' i) := by
    intro i j h; apply hinj₁; show Psp.reduceFst α hα (Q₁ i) = Psp.reduceFst α hα (Q₁ j); rw [← hred₁ i, ← hred₁ j]; exact h
  have hinj₂' : Function.Injective fun j => Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂' j) := by
    intro i j h; apply hinj₂; show Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ i) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂ j); rw [← hred₂ i, ← hred₂ j]; exact h
  have hT₁' : ∀ v, v ∈ T₁ ↔ ∃ i, Psp.reduceFst α hα (Q₁' i) = v := fun v => by
    rw [hT₁]; simp only [hred₁]
  have hT₂' : ∀ v, v ∈ T₂ ↔ ∃ j, Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ (Q₂' j) = v := fun v => by
    rw [hT₂]; simp only [hred₂]
  have hQs'' : ∀ i, Psp.reduceFst α hα Qs ≠ Psp.reduceFst α hα (Q₁' i) := fun i => by rw [hred₁]; exact hQs' i

  have hfixE' : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (∀ i, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₁' i = Q₁' i) ∧ (∀ j, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • Q₂' j = Q₂' j) := by
    intro σ hσ
    have hc := hcls σ hσ
    rw [hE1] at hc
    exact SndFix.forall_smul_eq_of_sub_mem_principal p M H hpM hpM2 hHp A hA θ α (θ.toAlgHom.comp α) hα hβ pb hpb δ hδ SS hSS Psp Rpd hTD hmodel hO hreg hnv hα_coe hβ_coe hθgal hβθ hLFst hLSnd hUnit hcusp Q₁' Q₂' hQ₁' hQ₂' hinj₁' hinj₂' hT₁' hT₂' hT₁W hT₁aff hT₂aff hgp₁ hgp₂
      Qs hQs hQs'' hσ hc

  refine ⟨(O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + (E1 - E0), ?_, ?_, ?_⟩
  · intro V' hV'
    have hcases : (Finsupp.single (Qb 0) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V' ≠ 0 ∨ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V' ≠ 0 ∨ E1 V' ≠ 0 ∨ E0 V' ≠ 0 := by
      by_contra h
      push_neg at h
      obtain ⟨a1, a2, a3, a4⟩ := h
      apply Finsupp.mem_support_iff.mp hV'
      rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.smul_apply, a1, a2, a3, a4]; simp
    rcases hcases with h | h | h | h
    · rw [Finsupp.single_apply_ne_zero] at h
      rw [h.1]
      exact ⟨hQbfix 0, Or.inl (hQb 0)⟩
    · exact hD₁ V' (Finsupp.mem_support_iff.mpr h)
    · rw [hE1, Finsupp.add_apply] at h
      by_cases h1' : (∑ i, Finsupp.single (Q₁' i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V' = 0
      · rw [h1', zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₂' V' h
        exact ⟨fun σ hσ => (hfixE' σ hσ).2 j, Or.inr (Or.inl (hQ₂' j))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₁' V' h1'
        exact ⟨fun σ hσ => (hfixE' σ hσ).1 i, Or.inl (hQ₁' i)⟩
    · rw [hE0, Finsupp.add_apply] at h
      by_cases h1' : (∑ i, Finsupp.single (Q₁ i) (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) V' = 0
      · rw [h1', zero_add] at h
        obtain ⟨j, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₂ V' h
        exact ⟨hI₂ j, Or.inr (Or.inl (hQ₂ j))⟩
      · obtain ⟨i, rfl⟩ := exists_eq_of_sum_single_apply_ne_zero (M := M) (H := H) Q₁ V' h1'
        exact ⟨hI₁ i, Or.inl (hQ₁ i)⟩
  ·
    have : (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) -
        ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + (E1 - E0)) = (X - D₁ - D₂) - ((E1 - E0) - D₂) := by
      rw [hX, hOsum]; abel
    rw [this]
    exact sub_mem hprin h1
  · have : (∑ V' ∈ O, Finsupp.single V' (1 : ℤ) : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) -
        ((O.card : ℤ) • Finsupp.single (Qb 0) (1 : ℤ) + (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) + (E1 - E0)) = X - D₁ - (E1 - E0) := by
      rw [hX, hOsum]; abel
    rw [this]
    have hE10 : (E1 - E0) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) := by rw [hE1, hE0]; exact hdeg0
    exact sub_mem (sub_mem hXdeg D₁.2) hE10

end SndFix

open Classical in
theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : (θ.toAlgHom.comp α).IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ v, δ v = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM) (CuspForm.gammaLift (M / p) pb)) • v)
    (SS : Finset (Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A) (Rpd : JHPlaceSpecialization.ProlongationDatum Psp θ)

    (hFix : ∀ y ∈ ssPlacesQExp (ResidueField ↥A) (ΓN p M H hpM) p,
      JHPlaceSpecialization.Fixed p M H hpM A δ y ∧
        JHPlaceSpecialization.Fixed p M H hpM A δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (ΓN p M H hpM) p y))
    (hTD : Psp.TypeDichotomy α (θ.toAlgHom.comp α) hα hβ δ)
    (hmodel : Rpd.IsModel α (θ.toAlgHom.comp α) hα hβ δ) (hO : Rpd.OrderLawFixed α (θ.toAlgHom.comp α) hα hβ δ)
    (hreg : Rpd.RegularityLaw α (θ.toAlgHom.comp α) hα hβ δ SS) (hnv : Rpd.NodeValueLaw α (θ.toAlgHom.comp α) hα hβ δ SS)

    (hθgal : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (f : ↥(xHFunctionFieldBar M H)),
      θ (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • f) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ • θ f)
    (hβ_coe : ∀ u, (((θ.toAlgHom.comp α) u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))

    (hFixFin : {v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) | JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v}.Finite)

    (hLFst : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceFst α hα Q' = Psp.reduceFst α hα Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceFst α hα Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₁ : g ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨g, hg₁⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceFst α hα W = Psp.reduceFst α hα Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₁ : ε ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨ε, hε₁⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceFst α hα Q).ord (Rpd.R₁.residue ⟨ε, hε₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hLSnd : ∀ (Q Q' : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q → Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ Q' →
      Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q' = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → Q' ≠ Q → JHPlaceSpecialization.IsAffinePlace p M H hpM A (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q) →
      ∀ (n : ℕ), (n : (ResidueField ↥A)) ≠ 0 → ∀ (g : ↥(xHFunctionFieldBar M H)) (hg₂ : g ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨g, hg₂⟩ ≠ 0 →
      Q.ord g = -(n : ℤ) → Q'.ord g = n →
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W → Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ W = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q → W ≠ Q → W ≠ Q' → W.ord g = 0) →
      ∀ (e : ↥A) (ε : ↥(xHFunctionFieldBar M H)) (hε₂ : ε ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨ε, hε₂⟩ ≠ 0 →
      g = 1 + algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) (e : AlgebraicClosure ℚ) * ε →
      -1 ≤ (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ Q).ord (Rpd.R₂.residue ⟨ε, hε₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))

    (hUnit : ∃ (u₁ u₂ : ↥(xHFunctionFieldBar M H)) (D₁ D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)),
      (∀ W, D₁ W = W.ord u₁) ∧ (∀ W, D₂ W = W.ord u₂) ∧

      (∃ h₁ : u₁ ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨u₁, h₁⟩ ≠ 0 ∧ u₁⁻¹ ∈ Rpd.R₁.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceFst α hα) (Psp.fstDiv α (θ.toAlgHom.comp α) hα hβ δ D₁) v = v.ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceFst α hα) (D₁.filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceFst α hα C) =
            (Psp.reduceFst α hα C).ord (Rpd.R₁.residue ⟨u₁, h₁⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₂ : f ^ m * u₁ ^ j ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨f ^ m * u₁ ^ j, h₂⟩ ≠ 0) ∧

      (∃ h₂ : u₂ ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨u₂, h₂⟩ ≠ 0 ∧ u₂⁻¹ ∈ Rpd.R₂.integers ∧
        (∀ v : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)), ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ v →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (Psp.sndDiv α (θ.toAlgHom.comp α) hα hβ δ D₂) v = v.ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))) ∧
        (∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
          Finsupp.mapDomain (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ) (D₂.filter (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A))) (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C) =
            (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C).ord (Rpd.R₂.residue ⟨u₂, h₂⟩ : (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))) ∧
      (∀ f : ↥(xHFunctionFieldBar M H), f ≠ 0 → ∃ (m : ℕ) (j : ℤ), m ≠ 0 ∧
        ∃ h₁ : f ^ m * u₂ ^ j ∈ Rpd.R₁.integers, Rpd.R₁.residue ⟨f ^ m * u₂ ^ j, h₁⟩ ≠ 0))
    (hcusp : ∀ w : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ¬ (JHPlaceSpecialization.IsAffinePlace (p := p) (M := M) (H := H) (hpM := hpM) (A := A)) w →
        (∃ C, (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceFst α hα C = w) ∧
        (∃ C, (JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A)) C ∧ Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C = w))

    (horientInf : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) C →
      δ (qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceFst α hα C)) = Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C)
    (horient0 : ∀ C : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H), JHPlaceSpecialization.IsZeroSide (p := p) (M := M) (H := H) (A := A) C →
      Psp.reduceFst α hα C = qExpFrobeniusPlaceModL (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p (Psp.reduceSnd (θ.toAlgHom.comp α) hβ δ C))

    (e : ↥SS → ℕ) (he : ∀ s, 0 < e s)
    (hAnn : ∀ s : ↥SS, ∃ An : AlgebraicCurve.Annulus A ↥(xHFunctionFieldBar M H),
      (∀ W : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
        W ∈ An.dom ↔ (Psp.reduceFst α hα W = s.1.1 ∧ ¬ Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ W ∧ ¬ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ W)) ∧
      (∃ u : ↥A, IsUnit u ∧ An.modulus = ((p : ℕ) : ↥A) ^ (e s) * u) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ ∈ A.inertiaSubgroupIn ℚ →
        (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • An.param = An.param) ∧
      algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : AlgebraicClosure ℚ))⁻¹ * An.param ∈ Rpd.R₁.integers ∧
      (∃ h₂ : An.param ∈ Rpd.R₂.integers, Rpd.R₂.residue ⟨An.param, h₂⟩ ≠ 0) ∧

      (∃ h₂ : An.param ∈ Rpd.R₂.integers, s.1.2.ord (Rpd.R₂.residue ⟨An.param, h₂⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₂.integers), Rpd.R₂.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt An.param) ^ (-(s.1.2.ord (Rpd.R₂.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)) ∧
      (∃ h₁ : algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹ ∈ Rpd.R₁.integers,
        s.1.1.ord (Rpd.R₁.residue ⟨_, h₁⟩) = 1 ∧
        ∀ (f : ↥(xHFunctionFieldBar M H)) (hf : f ∈ Rpd.R₁.integers), Rpd.R₁.residue ⟨f, hf⟩ ≠ 0 →
          (∀ P ∈ An.dom, P.ord f = 0) → ∀ P ∈ An.dom,
            ∃ h : P.evalAt f * (P.evalAt (algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H) ((An.modulus : ↥A) : AlgebraicClosure ℚ) * An.param⁻¹)) ^
              (-(s.1.1.ord (Rpd.R₁.residue ⟨f, hf⟩))) ∈ A, IsUnit (⟨_, h⟩ : ↥A)))

    (hsplit : ∀ (X : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) = X) →
      (∀ V ∈ (X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) →
      ∃ (D₁ D₂ : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))),
        (∀ V ∈ (D₁ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)).support,
          (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) ∧
        Psp.IsGoodDiv α (θ.toAlgHom.comp α) hα hβ δ (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∧
        (∃ hadm : Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) ∈ GluingData.admissible SS,
          GluedPic0.mk SS ⟨Psp.glueData α (θ.toAlgHom.comp α) hα hβ δ SS (D₂ : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)), hadm⟩ = 0) ∧
        ((X : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) - D₁ - D₂) ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)))
    (E : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (hEst : ∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • E = E)
    (hEgood : ∀ V ∈ E.support, (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1)) :
    ∃ C : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H),
      C ∈ Divisor.principal (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) ∧
      C ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)) ∧
      ∀ V ∈ (E - C).support,
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, (arithmeticGalois (L := AlgebraicClosure ℚ) (xHFunctionField M H) σ) • V = V) ∧ (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1) := by
  obtain ⟨C, hCp, hCd, hCfg⟩ := SndFix.exists_fixing_corrector (M := M) (H := H) (A := A)
    (fun V => (Psp.IsStrictFst α (θ.toAlgHom.comp α) hα hβ δ V ∨ Psp.IsStrictSnd α (θ.toAlgHom.comp α) hα hβ δ V ∨ ∃ s ∈ SS, Psp.reduceFst α hα V = s.1))
    (fun V hV Oo hOo => SndFix.exists_fixed_good_rep_of_orbit_main p M H hpM hpM2 hHp A hA θ α hα hβ hα_coe pb hpb δ hδ SS hSS Psp Rpd hFix hTD hmodel hO hreg hnv hθgal hβ_coe hFixFin hLFst hLSnd hUnit hcusp horientInf horient0 e he hAnn hsplit V hV Oo hOo)
    _ E le_rfl hEst hEgood
  exact ⟨C, hCp, hCd, fun V hV => hCfg V hV⟩

end
end S_ModularCurve_JHPlaceSpecialization_exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting
end P2MW
export P2MW.S_ModularCurve_JHPlaceSpecialization_exists_principal_degZero_forall_support_sub_inertia_smul_eq_of_splitting (solution)
