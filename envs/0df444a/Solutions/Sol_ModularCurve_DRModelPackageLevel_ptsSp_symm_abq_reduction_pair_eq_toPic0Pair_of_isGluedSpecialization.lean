-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/29a8ca01-3288-5c13-ba87-5eb89e7bee7e

import Mathlib
import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Theorems.Thm_ModularCurve_reductionInputsModL_of_not_dvd
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_ModularCurve_NodeDescentTower
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
import Theorems.Thm_ModularCurve_JZeroNeronObjectAtP_LevelModel_ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
import Theorems.Thm_ModularCurve_IgusaScheme_isProper_and_smooth_and_geometricallyIntegral
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"
p2m_attr_erase "simp" "ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU"
p2m_attr_erase "simp" "ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.DRLevel"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

theorem M3Sol.isCurveOver_bar (M : ℕ) [NeZero M] :
    AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M) := by
  let x : ↥(ModularCurve.modularFunctionFieldBar M) :=
    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jq_mem_full M)⟩
  have hx : Transcendental (AlgebraicClosure ℚ) x := by
    intro halg
    apply ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)
    have h := halg.algHom (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M)
      (LaurentSeries (AlgebraicClosure ℚ)))
    have hval : (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M)
        (LaurentSeries (AlgebraicClosure ℚ))) x = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
      show (x : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)
      exact ModularCurve.NodeLocalized.coeffEmb_jq_eq
    rwa [hval] at h
  haveI hfin := ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero M
  haveI : Algebra.IsSeparable (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.modularFunctionFieldBar M)))
      ↥(ModularCurve.modularFunctionFieldBar M) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (AlgebraicClosure ℚ) _ x hx hfin inferInstance

section PTEXT
open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.stalkMap_congr_point_assoc stalkClosedPointIso Scheme.Hom.stalkMap_congr_hom Spec Scheme.Hom.stalkMap_comp Spec.map Scheme Scheme.stalkClosedPointTo pointEquivClosedPoint IsSeparated Scheme.Modules.pullbackCongr Scheme.Modules.pullbackId Scheme.Modules SpecToEquivOfLocalRing_eq_iff pointEquivClosedPoint_apply_coe Scheme.Hom.stalkMap_id SpecToEquivOfLocalRing Scheme.IdealSheafData Scheme.Modules.pullbackComp Scheme.Modules.IsInvertible Scheme.Modules.pullbackUnitIso Scheme.Modules.isInvertible_unit RelPicard.postComp Scheme.Modules.pullbackTensorObjIso Scheme.Modules.pullbackTensorUnitObjIso Scheme.Modules.rigidify RelEffCartierDiv Scheme.IdealSheafData.IsInvertible Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso RelEffCartierDiv.isInvertible_I RelEffCartierDiv.ofPoint RelEffCartierDiv.ofPoint_I"
p2m_open "AlgebraicGeometry"

theorem RingHom.eq_of_isLocalRing_of_comp_eq_id
    {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    (φ ψ : A →+* K) (ι : K →+* A)
    (hφ : φ.comp ι = RingHom.id K) (hψ : ψ.comp ι = RingHom.id K) : φ = ψ := by
  have hφs : Function.Surjective φ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hφ k⟩
  have hψs : Function.Surjective ψ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hψ k⟩
  have hker : RingHom.ker φ = RingHom.ker ψ := by
    rw [IsLocalRing.ker_eq_maximalIdeal φ hφs, IsLocalRing.ker_eq_maximalIdeal ψ hψs]
  ext a
  have h1 : a - ι (φ a) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa using (RingHom.congr_fun hφ (φ a)).symm
  rw [hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]
  simpa using (RingHom.congr_fun hψ (φ a)).symm

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom mk Hom.stalkMap_congr_point_assoc empty Hom.stalkMap_congr_hom topIso Hom.stalkMap_comp stalkClosedPointTo Modules.pullbackCongr Modules.pullbackId Modules residue Hom.stalkMap_id IdealSheafData Modules.pullbackComp Modules.IsInvertible Modules.pullbackUnitIso Modules.isInvertible_unit Modules.pullbackTensorObjIso Modules.pullbackTensorUnitObjIso Modules.rigidify IdealSheafData.IsInvertible IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.ext_of_section_base_eq {κ : Type u} [Field κ] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of κ)) (p q : Spec (.of κ) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (h : p (closedPoint κ) = q (closedPoint κ)) : p = q := by

  have hpt : ∀ y : Spec (.of κ), y = closedPoint κ := fun y => Subsingleton.elim _ _

  have key : ∀ (r : Spec (.of κ) ⟶ X) (_ : r ≫ f = 𝟙 _),
      f.stalkMap (r (closedPoint κ)) ≫ r.stalkMap (closedPoint κ) =
        ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (r (closedPoint κ)))))).hom := by
    intro r hr
    have := Scheme.Hom.stalkMap_congr_hom _ _ hr (closedPoint κ)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id] at this

    erw [Category.comp_id] at this
    exact this

  let ι : CommRingCat.of κ ⟶ X.presheaf.stalk (p (closedPoint κ)) :=
    (stalkClosedPointIso (.of κ)).inv ≫
      ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (p (closedPoint κ)))).symm)).hom ≫
        f.stalkMap (p (closedPoint κ))
  have h1 : ι ≫ Scheme.stalkClosedPointTo p = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [reassoc_of% (key p hp)]
    simp
  have h2 : ι ≫ ((X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q) = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [Scheme.Hom.stalkMap_congr_point_assoc f _ _ h, reassoc_of% (key q hq)]
    simp

  apply (SpecToEquivOfLocalRing X (.of κ)).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨h, ?_⟩
  change Scheme.stalkClosedPointTo p =
    (X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q
  refine CommRingCat.hom_ext ?_
  refine RingHom.eq_of_isLocalRing_of_comp_eq_id (K := κ) _ _ ι.hom ?_ ?_
  · rw [← CommRingCat.hom_comp, h1, CommRingCat.hom_id]
  · rw [← CommRingCat.hom_comp, h2, CommRingCat.hom_id]

end AlgebraicGeometry

end PTEXT

theorem M3Sol.ext_of_section_of_apply_eq {X : Scheme.{0}} {K : Type} [Field K] (q : X ⟶ Spec (CommRingCat.of K))
    (f g : Spec (CommRingCat.of K) ⟶ X) (hf : f ≫ q = 𝟙 _) (hg : g ≫ q = 𝟙 _)
    (h : f.base (IsLocalRing.closedPoint K) = g.base (IsLocalRing.closedPoint K)) : f = g :=
  AlgebraicGeometry.Scheme.ext_of_section_base_eq q f g hf hg h

theorem M3Sol.schemeHomOverComp_eq_postComp {R : Type} [CommRing R] {X X' T : Scheme.{0}}
    {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)} {t : T ⟶ Spec (CommRingCat.of R)}
    (a : SchemeHomOver t x) (φ : SchemeHomOver x x') :
    NeronModelInfra.schemeHomOverComp a φ = AlgebraicGeometry.RelPicard.postComp φ a :=
  Subtype.ext rfl

noncomputable section

universe u v

theorem M3Sol.pic0congr_symm_mk {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F ≃+* F') (he : ∀ a : K, e (algebraMap K F a) = algebraMap K F' a)
    (D : ↥(Divisor.degZero (K := K) (F := F'))) :
    (Pic0.congr e he).symm (Pic0.mk D) = Pic0.mk ((Pic0.degZeroCongr e he).symm D) := rfl

namespace PrincTriv

def ClsMon (X : Scheme.{u}) : Type (u + 1) := Quotient (isIsomorphicSetoid X.Modules)

variable {X Y : Scheme.{u}}

def cls (A : X.Modules) : ClsMon X := Quotient.mk _ A

theorem cls_eq_iff {A B : X.Modules} : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

scoped instance : CommMonoid (ClsMon X) where
  mul := Quotient.map₂ (fun A B => A ⊗ B) (fun _ _ hA _ _ hB => ⟨hA.some ⊗ᵢ hB.some⟩)
  one := cls (𝟙_ X.Modules)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Quotient.sound ⟨α_ _ _ _⟩
  one_mul a := Quotient.inductionOn a fun _ => Quotient.sound ⟨λ_ _⟩
  mul_one a := Quotient.inductionOn a fun _ => Quotient.sound ⟨ρ_ _⟩
  mul_comm a b := Quotient.inductionOn₂ a b fun _ _ => Quotient.sound ⟨β_ _ _⟩

theorem cls_tensor (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B := rfl

theorem cls_unit : cls (𝟙_ X.Modules) = 1 := rfl

def unitOf (A B : X.Modules) (h : Nonempty (A ⊗ B ≅ 𝟙_ X.Modules)) : (ClsMon X)ˣ where
  val := cls A
  inv := cls B
  val_inv := by rw [← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h
  inv_val := by rw [mul_comm, ← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h

@[scoped simp] theorem val_unitOf (A B : X.Modules) (h) : (unitOf A B h : ClsMon X) = cls A := rfl
@[scoped simp] theorem inv_unitOf (A B : X.Modules) (h) : ((unitOf A B h)⁻¹ : (ClsMon X)ˣ) = (cls B : ClsMon X) := rfl

def pullbackCls (f : X ⟶ Y) : ClsMon Y →* ClsMon X where
  toFun := Quotient.map (fun A => (Scheme.Modules.pullback f).obj A) (fun _ _ h => ⟨(Scheme.Modules.pullback f).mapIso h.some⟩)
  map_one' := Quotient.sound ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  map_mul' a b := Quotient.inductionOn₂ a b fun A B => Quotient.sound ⟨Scheme.Modules.pullbackTensorObjIso f A B⟩

theorem pullbackCls_cls (f : X ⟶ Y) (A : Y.Modules) :
    pullbackCls f (cls A) = cls ((Scheme.Modules.pullback f).obj A) := rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.PrincTriv"

namespace PrincTriv

variable {X Y : Scheme.{u}}

def idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) : (ClsMon X)ˣ :=
  unitOf I.module I.invModule hI.nonempty_module_tensor_invModule_iso.1

@[scoped simp] theorem val_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (idealUnit I hI : ClsMon X) = cls I.module := rfl

@[scoped simp] theorem val_inv_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ((idealUnit I hI)⁻¹ : (ClsMon X)ˣ) = (cls I.invModule : ClsMon X) := rfl

theorem idealUnit_congr {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    idealUnit I hI = idealUnit J hJ := by subst h; rfl

theorem idealUnit_mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIJ : (I * J).IsInvertible) : idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  ext
  show cls (I * J).module = cls I.module * cls J.module
  rw [← cls_tensor]
  obtain ⟨μ, -⟩ := hI.exists_tensor_iso_mul_module hJ
  exact (cls_eq_iff.mpr ⟨μ⟩).symm

theorem idealUnit_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (k : ℕ) :
    idealUnit (I ^ k) (hI.pow k) = idealUnit I hI ^ k := by
  induction k with
  | zero =>
    have h00 : (I ^ 0 * I ^ 0).IsInvertible := by rw [← pow_add]; exact hI.pow 0
    have h2 : idealUnit (I ^ 0) (hI.pow 0) * idealUnit (I ^ 0) (hI.pow 0) = idealUnit (I ^ 0) (hI.pow 0) := by
      rw [← idealUnit_mul (hI.pow 0) (hI.pow 0) h00]
      exact idealUnit_congr _ _ (by rw [← pow_add])
    rw [show idealUnit I hI ^ 0 = 1 from pow_zero _]
    exact mul_left_cancel (h2.trans (mul_one _).symm)
  | succ k ih =>
    have h' : (I ^ k * I).IsInvertible := (pow_succ I k) ▸ hI.pow (k + 1)
    calc idealUnit (I ^ (k + 1)) (hI.pow (k + 1)) = idealUnit (I ^ k * I) h' := idealUnit_congr _ _ (pow_succ I k)
      _ = idealUnit (I ^ k) (hI.pow k) * idealUnit I hI := idealUnit_mul _ _ _
      _ = idealUnit I hI ^ (k + 1) := by rw [ih, pow_succ]

theorem cls_foldr {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (A B : Fin n → X.Modules) (l : List (Fin n)) :
    cls (l.foldr (fun i M => if c i = j then A i ⊗ B i ⊗ M else M) (𝟙_ X.Modules)) =
      (l.map fun i => if c i = j then cls (A i) * cls (B i) else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    split_ifs with h
    · rw [cls_tensor, cls_tensor, ih, mul_assoc]
    · rw [ih, one_mul]

theorem cls_twist {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (I : Fin n → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) :
    cls ((List.finRange n).foldr
        (fun i M => if c i = j then ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M else M)
        (𝟙_ X.Modules)) =
      ↑((∏ i ∈ Finset.univ.filter (fun i => c i = j), idealUnit (I i) (hI i) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
  rw [cls_foldr c j (fun i => ((I i) ^ (pos i)).invModule) (fun i => ((I i) ^ (neg i)).module),
    ← Fin.prod_univ_def, ← Finset.prod_filter, ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show cls (((I i) ^ (pos i)).invModule) = ↑((idealUnit _ ((hI i).pow (pos i)))⁻¹) from rfl,
    show cls (((I i) ^ (neg i)).module) = ↑(idealUnit _ ((hI i).pow (neg i))) from rfl,
    idealUnit_pow, idealUnit_pow, ← Units.val_mul, ← zpow_neg, neg_sub, zpow_sub, zpow_natCast, zpow_natCast,
    mul_comm]

theorem prod_inv_mul_zpow {ι G : Type*} [CommGroup G] [DecidableEq ι] (s : Finset ι) (a : ι → G) (b : G) (m : ι → ℤ) :
    ∏ i ∈ s, ((a i)⁻¹ * b) ^ (m i) = (∏ i ∈ s, (a i) ^ (m i))⁻¹ * b ^ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih, mul_zpow, inv_zpow, zpow_add, mul_inv]
    ac_rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.PrincTriv"

namespace PrincTriv
variable {X : Scheme.{u}}

theorem cls_foldr' {n : ℕ} (A B : Fin n → X.Modules) (l : List (Fin n)) :
    cls (l.foldr (fun i M => A i ⊗ B i ⊗ M) (𝟙_ X.Modules)) = (l.map fun i => cls (A i) * cls (B i)).prod := by
  induction l with
  | nil => rfl
  | cons i l ih => simp only [List.foldr_cons, List.map_cons, List.prod_cons]; rw [cls_tensor, cls_tensor, ih, mul_assoc]

theorem cls_twist' {n : ℕ} (I : Fin n → X.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) :
    cls ((List.finRange n).foldr
        (fun i M => ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M) (𝟙_ X.Modules)) =
      ↑((∏ i, idealUnit (I i) (hI i) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
  rw [cls_foldr' (fun i => ((I i) ^ (pos i)).invModule) (fun i => ((I i) ^ (neg i)).module), ← Fin.prod_univ_def,
    ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show cls (((I i) ^ (pos i)).invModule) = ↑((idealUnit _ ((hI i).pow (pos i)))⁻¹) from rfl,
    show cls (((I i) ^ (neg i)).module) = ↑(idealUnit _ ((hI i).pow (neg i))) from rfl,
    idealUnit_pow, idealUnit_pow, ← Units.val_mul, ← zpow_neg, neg_sub, zpow_sub, zpow_natCast, zpow_natCast,
    mul_comm]

theorem idealUnit_congr' {I J : X.IdealSheafData} (hI : I.IsInvertible) (h : I = J) :
    idealUnit I hI = idealUnit J (h ▸ hI) := by subst h; rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.PrincTriv"

namespace PrincTriv
variable {X : Scheme.{u}}

theorem isInvertible_twist {n : ℕ} (I : Fin n → X.IdealSheafData) (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ)
    (l : List (Fin n)) :
    Scheme.Modules.IsInvertible (l.foldr
      (fun i M => ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M) (𝟙_ X.Modules)) := by
  induction l with
  | nil => exact Scheme.Modules.isInvertible_unit X
  | cons i l ih =>
    rw [List.foldr_cons]
    exact ((hI i).pow (pos i)).isInvertible_invModule.tensor (((hI i).pow (neg i)).isInvertible_module.tensor ih)

theorem nonempty_iso_unit_of_field {K : Type u} [Field K] (M : (Spec (CommRingCat.of K)).Modules)
    (hM : Scheme.Modules.IsInvertible M) : Nonempty (M ≅ 𝟙_ (Spec (CommRingCat.of K)).Modules) := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := hM.exists_trivialization (IsLocalRing.closedPoint K)
  haveI : Subsingleton ↥(Spec (CommRingCat.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hU : U = ⊤ := eq_top_iff.mpr fun x _ => by rw [Subsingleton.elim x (IsLocalRing.closedPoint K)]; exact hxU
  subst hU
  exact ⟨((Scheme.Modules.pullbackId _).app M).symm ≪≫
    (Scheme.Modules.pullbackCongr (Spec (CommRingCat.of K)).topIso.inv_hom_id.symm).app M ≪≫
    ((Scheme.Modules.pullbackComp _ _).app M).symm ≪≫
    (Scheme.Modules.pullback _).mapIso e ≪≫ Scheme.Modules.pullbackUnitIso _⟩

theorem map_pullbackCls_idealUnit_of_comap {Y : Scheme.{u}} (g : Y ⟶ X) {I : X.IdealSheafData} {J : Y.IdealSheafData}
    (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I.comap g = J) :
    Units.map (pullbackCls g : ClsMon X →* ClsMon Y) (idealUnit I hI) = idealUnit J hJ := by
  subst h
  rw [← inv_inj, ← map_inv]
  ext
  show pullbackCls g (cls I.invModule) = cls (I.comap g).invModule
  rw [pullbackCls_cls]
  exact cls_eq_iff.mpr (Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso g hI hJ)

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.PrincTriv"

namespace PrincTriv
variable {X : Scheme.{u}}
theorem isInvertible_twist_if {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (I : Fin n → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) (l : List (Fin n)) :
    Scheme.Modules.IsInvertible (l.foldr
      (fun i M => if c i = j then ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M else M) (𝟙_ X.Modules)) := by
  induction l with
  | nil => exact Scheme.Modules.isInvertible_unit X
  | cons i l ih =>
    rw [List.foldr_cons]
    by_cases h : c i = j
    · rw [if_pos h]; exact ((hI i).pow (pos i)).isInvertible_invModule.tensor (((hI i).pow (neg i)).isInvertible_module.tensor ih)
    · rw [if_neg h]; exact ih
end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization.PrincTriv"

set_option maxHeartbeats 51200000 in

theorem M3Sol.coord_copy
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (hJ : M.toLevelData.IsJacobian) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hFE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀)

      (I : Fin 2) (πI : SchemeHomOver (toBase N₀ p) (toBase0 N₀ p))
      (_ : 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) I ≫ fibreMap0 πI (algebraMap (R p) (ResidueField ↥A)) = 𝟙 _)
      (spfun : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀) → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀))
      (_ : ∀ h : ReductionInputsModL A N₀, placeReductionModL h = fun W =>
          AlgebraicCurve.Place.congrRingEquiv (e := (IntermediateField.equivOfEq hFE).toRingEquiv)
            (he := fun a => (IntermediateField.equivOfEq hFE).commutes a) (spfun W))
      (redI : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀))
      (_ : ∀ (yq : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (xq : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _}),
          xq.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = yq.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πI.1 →
          spfun (M.Meta₀.pointEquivPlace xq) = redI (𝔓.Meta.pointEquivPlace yq))

      {n : ℕ} (qq : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (ss : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
      (_ : ∀ i, (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = barPt A ≫ (ss i).1)
      (c : Fin n → Fin 2)
      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A))))
      (_ : ∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1)
      (_ : ∀ i, y i ≫ pullback.snd _ _ = 𝟙 _)
      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (_ : ∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i)
      (pos neg : Fin n → ℕ)
      (_ : (∑ i ∈ Finset.univ.filter (fun i => c i = I), ((pos i : ℤ) - (neg i : ℤ))) = 0)
      (hDz : (∑ i ∈ Finset.univ.filter (fun i => c i = I), Finsupp.single (redI (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ))) ∈
        Divisor.degZero (K := ResidueField ↥A) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀)))

      (aκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (M.D₀.baseChange (ResidueField ↥A)).toBase)
      (_ : Nonempty ((hD₀κ.poincare.pullbackAlong aκ).L ≅
        ((List.finRange n).foldr
          (fun i N => if c i = I then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ N
            else N)
          (𝟙_ _))))
      (rI : SchemeHomOver (JZeroNeronObjectAtP.resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
      (_ : rI.1 = aκ.1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A))),
      (Pic0.congr (IntermediateField.equivOfEq hFE).toRingEquiv (fun a => (IntermediateField.equivOfEq hFE).commutes a)).symm
          (M.toLevelData.ptsSp.symm rI) = Pic0.mk ⟨_, hDz⟩ := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
  intro _i2 _i3 hD₀κ hP₀κ hFE I πI hcompI spfun hred redI hplace n qq ss hqs c y hy₁ hy₂ z hz hzy pos neg hdegI hDz aκ eA rI hrI
  obtain ⟨eAI⟩ := eA

  have hbase : 𝟙 (Spec (CommRingCat.of (ResidueField ↥A))) ≫ specMap (R p) (ResidueField ↥A) =
      JZeroNeronObjectAtP.resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ) := by
    rw [Category.id_comp]
    show Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp M.ρ)) = _
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨hprop0, hsm0, hgi0⟩ := ModularCurve.IgusaScheme.isProper_and_smooth_and_geometricallyIntegral N₀ p hpN₀
  haveI := hprop0
  haveI := hsm0
  haveI := hgi0

  let σσ : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase0 N₀ p) :=
    fun j => NeronModelInfra.schemeHomOverComp (ss j) πI
  let pp : Fin n → ℕ := fun j => if c j = I then pos j else 0
  let nn : Fin n → ℕ := fun j => if c j = I then neg j else 0
  have hmm : ∀ j, ((pp j : ℤ) - (nn j : ℤ)) = if c j = I then ((pos j : ℤ) - (neg j : ℤ)) else 0 := fun j => by
    by_cases h : c j = I <;> simp [pp, nn, h]
  have hdeg' : (∑ j, ((pp j : ℤ) - (nn j : ℤ))) = 0 := by
    simp_rw [hmm]; rw [← Finset.sum_filter]; exact hdegI

  obtain ⟨b, hb⟩ := ModularCurve.JZeroNeronObjectAtP.LevelModel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
    N₀ p A M σσ pp nn hdeg'

  have hσκ : ∀ j, (JZeroNeronObjectAtP.resPt A ≫ (σσ j).1) ≫ toBase0 N₀ p =
      𝟙 _ ≫ specMap (R p) (ResidueField ↥A) := fun j => by rw [Category.assoc, (σσ j).2, ← hbase]
  let zz : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) :=
    fun j => pullback.lift (JZeroNeronObjectAtP.resPt A ≫ (σσ j).1) (𝟙 _) (hσκ j)
  have hzz : ∀ j, zz j ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ := fun j => pullback.lift_snd _ _ _
  have hzzσ : ∀ j, zz j ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)) = JZeroNeronObjectAtP.resPt A ≫ (σσ j).1 :=
    fun j => pullback.lift_fst _ _ _
  have hzz_eq : ∀ j, c j = I → zz j = z j := fun j hj => by
    have hzyI : z j ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) I = y j := hj ▸ hzy j
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
      symm
      calc z j ≫ pullback.fst (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))
          = (z j ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) I ≫
              fibreMap0 πI (algebraMap (R p) (ResidueField ↥A))) ≫ pullback.fst _ _ := by rw [hcompI, Category.comp_id]
        _ = y j ≫ pullback.fst _ _ ≫ πI.1 := by rw [← Category.assoc (z j), hzyI, Category.assoc, DRLevel.fibreMap0_fst]
        _ = JZeroNeronObjectAtP.resPt A ≫ (ss j).1 ≫ πI.1 := by rw [← Category.assoc, hy₁ j, Category.assoc]
    · rw [pullback.lift_snd, hz j]

  let bκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (M.D₀.baseChange (ResidueField ↥A)).toBase :=
    ⟨pullback.lift (JZeroNeronObjectAtP.resPt A ≫ b.1) (𝟙 _) (by rw [Category.assoc, b.2, ← hbase]), pullback.lift_snd _ _ _⟩

  obtain ⟨eN3⟩ := ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_baseChange_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
    N₀ p A M hA hD₀κ hP₀κ σσ pp nn b hb zz hzz hzzσ bκ (pullback.lift_fst _ _ _)

  have hIz : ∀ (u : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)))
      (hu : u ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _),
      (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) u hu).I.IsInvertible := fun u hu =>
    RelEffCartierDiv.isInvertible_I _

  have ecls : PrincTriv.cls ((List.finRange n).foldr
        (fun j N => if c j = I then
          ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z j) (hz j)).I ^ (pos j)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z j) (hz j)).I ^ (neg j)).module ⊗ N
          else N)
        (𝟙_ _)) =
      PrincTriv.cls ((List.finRange n).foldr
        (fun j N => ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (zz j) (hzz j)).I ^ (pp j)).invModule ⊗
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (zz j) (hzz j)).I ^ (nn j)).module ⊗ N)
        (𝟙_ _)) := by
    rw [PrincTriv.cls_twist c I _ (fun j => hIz (z j) (hz j)) pos neg, PrincTriv.cls_twist' _ (fun j => hIz (zz j) (hzz j)) pp nn,
      ← Finset.prod_filter_mul_prod_filter_not Finset.univ (fun j => c j = I)]
    congr 2
    rw [Finset.prod_eq_one (s := Finset.univ.filter fun j => ¬ c j = I) (fun j hj => by
        rw [hmm, if_neg (Finset.mem_filter.mp hj).2, zpow_zero]), mul_one]
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' : c j = I := (Finset.mem_filter.mp hj).2
    rw [hmm, if_pos hj']
    congr 1
    have := hzz_eq j hj'

    have hI : (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z j) (hz j)).I =
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (zz j) (hzz j)).I := by
      simp only [RelEffCartierDiv.ofPoint_I, this]
    exact PrincTriv.idealUnit_congr _ _ hI

  have hab : aκ = bκ :=
    hD₀κ.ext_of_iso (𝟙 _) _ _ ⟨eAI ≪≫ (PrincTriv.cls_eq_iff.mp ecls).some ≪≫ eN3.symm⟩
  have hrb : rI = GoodReductionJacobian.schemeHomOverComp (JZeroNeronObjectAtP.resPt A) rfl b :=
    Subtype.ext (by rw [hrI, hab]; exact pullback.lift_fst _ _ _)

  have hσσ : ∀ j, (barPt A ≫ (σσ j).1) ≫ toBase0 N₀ p = genPt p := fun j => by rw [Category.assoc, (σσ j).2, M.barPt_σA]
  let xx : Fin n → SchemeHomOver (genPt p) (toBase0 N₀ p) := fun j => ⟨barPt A ≫ (σσ j).1, hσσ j⟩
  let bη : SchemeHomOver (genPt p) M.D₀.toBase := ⟨barPt A ≫ b.1, by rw [Category.assoc, b.2, M.barPt_σA]⟩
  obtain ⟨eN2P⟩ := ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_iso_pointTwist_of_iso_rigidify_sectionTwist
    N₀ p A M σσ pp nn b hb xx (fun _ => rfl) bη rfl

  haveI := M.eeta₀_iso
  have hlift : ∀ j, ((qq j).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πI.1) ≫ toBase0 N₀ p = genPt p := fun j => by
    rw [Category.assoc, Category.assoc, Category.assoc, πI.2, pullback.condition, ← Category.assoc 𝔓.eeta, 𝔓.heeta,
      ← Category.assoc, (qq j).2, Category.id_comp]
  let q' : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _} := fun j =>
    ⟨pullback.lift ((qq j).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πI.1) (𝟙 _) ((hlift j).trans (Category.id_comp _).symm) ≫
        inv M.eeta₀, by rw [Category.assoc, ← M.heeta₀, IsIso.inv_hom_id_assoc, pullback.lift_snd]⟩
  have hq'x : ∀ j, (q' j).1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      (qq j).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ πI.1 := fun j => by
    simp only [q', Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst]
  have hxq : ∀ j, (xx j).1 = (q' j).1 ≫ M.eeta₀ ≫ pullback.fst (toBase0 N₀ p) (genPt p) := fun j => by
    rw [hq'x]
    show barPt A ≫ (ss j).1 ≫ πI.1 = _
    rw [← Category.assoc, ← hqs j, Category.assoc, Category.assoc]

  haveI := M3Sol.isCurveOver_bar N₀
  have hdz : (∑ j, Finsupp.single (M.Meta₀.pointEquivPlace (q' j)) ((pp j : ℤ) - (nn j : ℤ))) ∈
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N₀)) := by
    rw [Divisor.mem_degZero, map_sum]
    simp_rw [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one]
    exact hdeg'
  obtain ⟨eN2⟩ := ModularCurve.JZeroNeronObjectAtP.LevelModel.nonempty_poincare_pullbackAlong_pts_pic0Mk_iso_pointTwist
    N₀ p A M hJ q' xx hxq pp nn hdeg' ⟨_, hdz⟩ rfl
  have hgen : M.pts (Pic0.mk ⟨_, hdz⟩) = bη := M.rep.ext_of_iso (genPt p) _ _ ⟨eN2 ≪≫ eN2P.symm⟩

  have hN4 := ModularCurve.JZeroNeronObjectAtP.LevelModel.ptsSp_symm_schemeHomOverComp_resPt_eq_reductionModL
    N₀ p hpN₀ A hA M hJ (Pic0.mk ⟨_, hdz⟩) b (by rw [hgen])
  rw [hrb]
  refine (congrArg _ hN4).trans ?_
  rw [reductionModL_mk (reductionInputsModL_of_not_dvd N₀ hpN₀ A hA)]
  refine (M3Sol.pic0congr_symm_mk _ _ _).trans ?_
  congr 1
  apply Subtype.ext
  rw [Pic0.coe_degZeroCongr_symm, coe_reductionDegZeroAlong, AddEquiv.symm_apply_eq]
  show Finsupp.mapDomain (placeReductionModL (reductionInputsModL_of_not_dvd N₀ hpN₀ A hA))
      (∑ j, Finsupp.single (M.Meta₀.pointEquivPlace (q' j)) ((pp j : ℤ) - (nn j : ℤ))) =
    Divisor.congr _ _ (∑ i ∈ Finset.univ.filter (fun i => c i = I), Finsupp.single (redI (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ)))
  rw [hred (reductionInputsModL_of_not_dvd N₀ hpN₀ A hA), Finsupp.mapDomain_finsetSum, map_sum]
  simp only [Finsupp.mapDomain_single, Divisor.congr_single]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => c j = I),
    Finset.sum_eq_zero (s := Finset.univ.filter fun j => ¬ c j = I) (fun j hj => by
      rw [hmm, if_neg (Finset.mem_filter.mp hj).2, Finsupp.single_zero]), add_zero]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : c j = I := (Finset.mem_filter.mp hj).2
  rw [hmm, if_pos hj', hplace (qq j) (q' j) (hq'x j)]

set_option maxHeartbeats 51200000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

    (M : JZeroNeronObjectAtP.LevelModel N₀ p A) (_ : M.toLevelData.IsJacobian) :

    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    ∀
      (D : RelativePic0Designation (R p) (toBase N₀ p))
      (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

      (_ : IsSeparated D.toBase)

      (_ : ∀ (y : ↥(fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))),
          ¬ (y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base ∧
              y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base) →
            (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base y ∈
              (𝔓.smoothLocus : Set (X N₀ p)))
      [IsProper (baseChange (R p) (toBase N₀ p) (ResidueField ↥A))]
      [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)) (D.baseChange (ResidueField ↥A)))

      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀)) (M.D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) M.ε₀ (ResidueField ↥A)
        (M.rep.poincare.pullbackAlong ⟨pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange (ResidueField ↥A) M.ε₀).1 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0 = (sectionBaseChange (ResidueField ↥A) 𝔓.εinf).1)
      (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (M.D₀.baseChange (ResidueField ↥A)).toBase)

      (_ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        hε₁' hDκ hD₀κ)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) M.ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
            ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
              (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

      (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
      (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
          (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

      (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

      (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
      (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
      (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
          (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
        Nonempty ((hDQ.poincare.pullbackAlong
            ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
                (Category.comp_id t)))).idealModule))

      (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
      (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
      (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

      (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
      (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
      (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)
      (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
      (_ : ∀ x y : JZero (N₀ * p),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
      (_ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
        (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
      (_ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
            Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

      (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) (_ : ∀ w, w ∈ W ↔ w ∈ ssPlaces p N₀ (ResidueField ↥A))

      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) (ResidueField ↥A)) ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))
      (hE : modularFunctionFieldC (ResidueField ↥A) N₀ = modularFunctionFieldFullC (ResidueField ↥A) N₀)

      (_ : ∀ h : ReductionInputsModL A N₀,
        placeReductionModL h = fun W =>
          AlgebraicCurve.Place.congrRingEquiv
            (e := (IntermediateField.equivOfEq hE).toRingEquiv)
            (he := fun a => (IntermediateField.equivOfEq hE).commutes a) (P.sp W))

      (t : ℕ) (τ : SchemeHomOver (torusStr (ResidueField ↥A) t) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : ∀ {T : Scheme.{0}} (t' : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t' (D.baseChange (ResidueField ↥A)).toBase),
        (∀ i, NeronModelInfra.schemeHomOverComp a (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) M.rep).baseChange (specMap (R p) (ResidueField ↥A))).one t') ↔
          ∃ y : SchemeHomOver t' (torusStr (ResidueField ↥A) t),
            NeronModelInfra.schemeHomOverComp y τ = a)

      (sp : ↥(inertiaInvariants A (N₀ * p)) →+
        GluedPic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))
      (_ : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) sp)

      (x : ↥(inertiaInvariants A (N₀ * p))) (_ : P.IsGoodClass (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (x : JZero (N₀ * p)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) D.toBase)
      (_ : (pts (x : JZero (N₀ * p))).1 = barPt A ≫ s.1)
      (sκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : sκ.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)

      (r : Fin 2 → SchemeHomOver (JZeroNeronObjectAtP.resPt A ≫ Spec.map (CommRingCat.ofHom M.ρ)) M.D₀.toBase)
      (_ : ∀ i, (r i).1 = (NeronModelInfra.schemeHomOverComp sκ (abq i)).1 ≫ pullback.fst M.D₀.toBase (specMap (R p) (ResidueField ↥A))),

      ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
          (M.toLevelData.ptsSp.symm (r 0)),
        (Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm
          (M.toLevelData.ptsSp.symm (r 1))) =
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) (sp x) := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp M.ρ).toAlgebra
  letI := heckeModuleBar (N₀ * p)
  letI := heckeModuleBar N₀
  intro D hD hsepD hsm _i1 _i2 _i3 _i4 hDκ hPκ hD₀κ hP₀κ hε₁' abq habq0 habq1 hDQ hPQ hsepQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂
    ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hgal hpts_aj data hKr hα hβ P W hW hGC1 hGC2 hFE hred
    tt τ hexact sp hsp x hgood s hs sκ hsκ r hrr
  classical
  have hJ : M.toLevelData.IsJacobian := ‹_›
  obtain ⟨E, hEgood, hadmE, hEx⟩ := hgood
  let g : ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)) := ⟨_, hadmE⟩
  have hg : (g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)) =
      P.glueData (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) E := rfl
  have hspx : sp x = GluedPic0.mk _ g := by
    have hx' : x = ⟨Pic0.mk E, hEx ▸ x.2⟩ := Subtype.ext hEx.symm
    rw [hx']
    exact hsp E _ g hEgood rfl
  have hsE : (pts (Pic0.mk E)).1 = barPt A ≫ s.1 := by rw [hEx]; exact hs
  haveI : IsProper (toBase N₀ p) := 𝔓.isProper

  have ENUM : ∃ (n : ℕ) (qq : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (pos neg : Fin n → ℕ),
      (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 ∧
      ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
        ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (qq i)) ((pos i : ℤ) - (neg i : ℤ))) ∧
      (∀ i, P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i)) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i))) := by
    haveI := M3Sol.isCurveOver_bar (N₀ * p)
    set Ed : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) := (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) with hEd
    let supp := Ed.support
    let e : Fin supp.card ≃ ↥supp := supp.equivFin.symm
    have h1 : ∀ w, (((Ed w).toNat : ℕ) : ℤ) - (((-(Ed w)).toNat : ℕ) : ℤ) = Ed w := fun w => Int.toNat_sub_toNat_neg _
    refine ⟨supp.card, fun i => (𝔓.Meta.pointEquivPlace).symm (e i).1, fun i => (Ed (e i).1).toNat,
      fun i => (-(Ed (e i).1)).toNat, ?_, ?_, ?_⟩
    · simp_rw [h1]
      rw [Equiv.sum_comp e (fun w : ↥supp => Ed w.1), Finset.sum_coe_sort supp (fun w => Ed w)]
      have hE0 : Divisor.degree Ed = 0 := E.2
      rw [← hE0, Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [AddMonoidHom.mulRight_apply, IsCurveOver.deg_eq_one_of_isAlgClosed w, Nat.cast_one, mul_one]
    · simp_rw [Equiv.apply_symm_apply, h1]
      rw [Equiv.sum_comp e (fun w : ↥supp => Finsupp.single w.1 (Ed w.1)),
        Finset.sum_coe_sort supp (fun w => Finsupp.single w (Ed w))]
      exact (Finsupp.sum_single Ed).symm
    · intro i
      rw [Equiv.apply_symm_apply]
      exact hEgood (e i).1 (e i).2
  obtain ⟨n, qq, pos, neg, hn, hDx, hstrict⟩ := ENUM

  have SEC := fun i => ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm N₀ p hpN₀ 𝔓 A M.ρ M.hρ
    (𝔓.Meta.pointEquivPlace (qq i))
  let ss : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom M.ρ)) (toBase N₀ p) := fun i => (SEC i).exists.choose
  have hqs : ∀ i, (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ (ss i).1 := by
    intro i
    have h := (SEC i).exists.choose_spec
    have e : ((𝔓.Meta.pointEquivPlace).symm (𝔓.Meta.pointEquivPlace (qq i))).1 ≫ 𝔓.eeta ≫
        pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
        (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) := by
      rw [Equiv.symm_apply_apply]
    exact (h.trans e).symm

  have LAB : ∃ (c : Fin n → Fin 2)
      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp M.ρ)))
      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)))),
      (∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1) ∧
      (∀ i, y i ≫ pullback.snd _ _ = 𝟙 _) ∧
      (∀ i, Set.range (y i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ) (c i)).base) ∧
      (∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _) ∧
      (∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i) ∧
      (∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉
        Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base) ∧
      (∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((z i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ =
          if c i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ∧
      (∀ i, (c i = 0 ↔ P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i))) ∧ (c i = 1 ↔ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i)))) := by

    have hexcl : ∀ W, P.IsStrictFst W → P.IsStrictSnd W → False := fun W hF hS => hF.2 (by rw [hF.1, ← hS.1])

    let yy : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp M.ρ)) :=
      fun i => DRLevel.sectionFibreOver M.ρ (ss i)
    have hyy₁ : ∀ i, yy i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1 :=
      fun i => pullback.lift_fst _ _ _
    have hyy₂ : ∀ i, yy i ≫ pullback.snd _ _ = 𝟙 _ := fun i => pullback.lift_snd _ _ _

    have key : ∀ i, ∃ (ci : Fin 2) (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
        (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ≫
            𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ci).base P0.1 =
          (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 =
          (if ci = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ∧
        (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉
          Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - ci)).base ∧
        ((ci = 0 ↔ P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i))) ∧ (ci = 1 ↔ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i)))) := by
      intro i
      rcases hstrict i with hF | hS
      · obtain ⟨⟨P0, hP0, hpl⟩, hn⟩ := ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceFst_of_isStrictFst
          N₀ p hpN₀ 𝔓 A hA M.ρ M.hρ (ResidueField ↥A) (IsLocalRing.residue ↥A) data hKr hα hβ P hGC1 hGC2
          (qq i) hF (ss i) (hqs i).symm (yy i) (hyy₁ i) (hyy₂ i)
        refine ⟨0, P0, hP0, by rw [if_pos rfl]; exact hpl, by rw [sub_zero]; exact hn,
          ⟨fun _ => hF, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun hS' => (hexcl _ hF hS').elim⟩⟩
      · obtain ⟨⟨P1, hP1, hpl⟩, hn⟩ := ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
          N₀ p hpN₀ 𝔓 A hA M.ρ M.hρ (ResidueField ↥A) (IsLocalRing.residue ↥A) data hKr hα hβ P hGC1 hGC2
          (qq i) hS (ss i) (hqs i).symm (yy i) (hyy₁ i) (hyy₂ i)
        refine ⟨1, P1, hP1, by rw [if_neg (by decide)]; exact hpl, by rw [sub_self]; exact hn,
          ⟨fun h => absurd h (by decide), fun hF' => (hexcl _ hF' hS).elim⟩, ⟨fun _ => hS, fun _ => rfl⟩⟩
    choose cc PP hPP hpl hnn hciff using key

    let q0 : Fin n → {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C //
        q ≫ (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase = 𝟙 _} :=
      fun i => (pointEquivClosedPoint (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase).symm (PP i)
    have hq0 : ∀ i, (q0 i).1.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (PP i).1 := fun i => by
      have e := pointEquivClosedPoint_apply_coe (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase (q0 i)
      rw [Equiv.apply_symm_apply] at e
      exact e.symm
    let zz : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) :=
      fun i => (q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))
    have hzz : ∀ i, zz i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ := fun i => by
      show ((q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))) ≫ pullback.snd _ _ = 𝟙 _
      rw [Category.assoc, 𝔓.hefib, (q0 i).2]
    have hzzpt : ∀ i, (zz i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (cc i)).base
        (IsLocalRing.closedPoint (ResidueField ↥A)) = (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) := fun i => by
      rw [← hPP i, ← hq0 i]
      rfl

    have hlab : ∀ i, zz i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (cc i) = yy i := fun i => by
      refine M3Sol.ext_of_section_of_apply_eq (pullback.snd _ _) _ _ ?_ (hyy₂ i) (hzzpt i)
      rw [Category.assoc, 𝔓.comp_over]
      exact hzz i
    have hcr : ∀ i, Set.range (yy i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp M.ρ) (cc i)).base := fun i => by
      rintro _ ⟨pt, rfl⟩
      obtain rfl : pt = IsLocalRing.closedPoint (ResidueField ↥A) := Subsingleton.elim _ _
      exact ⟨(zz i).base (IsLocalRing.closedPoint (ResidueField ↥A)), hzzpt i⟩

    have hww : ∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((zz i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ =
          if cc i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i)) := fun i => by
      have e : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((zz i).base (IsLocalRing.closedPoint (ResidueField ↥A))) = (PP i).1 := by
        show ((q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ≫
          inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base _ = _
        rw [IsIso.hom_inv_id, Category.comp_id]
        exact hq0 i
      refine ⟨e ▸ (PP i).2, ?_⟩
      have hs : (⟨_, e ▸ (PP i).2⟩ : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C) = PP i :=
        Subtype.ext e
      rw [hs]
      exact hpl i
    exact ⟨cc, yy, zz, hyy₁, hyy₂, hcr, hzz, hlab, hnn, hww, hciff⟩
  obtain ⟨c, y, z, hy₁, hy₂, hc, hz, hzy, hnot, hw, hciff⟩ := LAB
  let w : Fin n → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀) := fun i =>
    if c i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))

  have hG0 : ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 0), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) := by
    rw [show ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1 =
        Finsupp.mapDomain P.reduceFst (P.fstDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))) from
      congrArg Prod.fst hg, PlaceSpecialization.fstDiv, hDx, Finsupp.filter_sum, Finsupp.mapDomain_finsetSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hci : c i = 0
    · rw [Finsupp.filter_single_of_pos _ ((hciff i).1.mp hci), Finsupp.mapDomain_single, if_pos hci]
      simp only [w, if_pos hci]
    · rw [Finsupp.filter_single_of_neg _ (fun h => hci ((hciff i).1.mpr h)), Finsupp.mapDomain_zero, if_neg hci]
  have hG1 : ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) := by
    rw [show ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1 =
        Finsupp.mapDomain P.reduceSnd (P.sndDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))) from
      congrArg (fun t => t.2.1) hg, PlaceSpecialization.sndDiv, hDx, Finsupp.filter_sum, Finsupp.mapDomain_finsetSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hci : c i = 1
    · have hci0 : ¬ c i = 0 := by rw [hci]; decide
      rw [Finsupp.filter_single_of_pos _ ((hciff i).2.mp hci), Finsupp.mapDomain_single, if_pos hci]
      simp only [w, if_neg hci0]
    · rw [Finsupp.filter_single_of_neg _ (fun h => hci ((hciff i).2.mpr h)), Finsupp.mapDomain_zero, if_neg hci]
  have hadm := (GluingData.mem_admissible (S := nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)).1 g.2

  have hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
    haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N₀
    have hd1 : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀), v.deg = 1 :=
      fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
    have key : ∀ (j : Fin 2) (Dv : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)),
        Dv ∈ Divisor.degZero (K := ResidueField ↥A) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) →
        Dv = ∑ i ∈ Finset.univ.filter (fun i => c i = j), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) →
        (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
      intro j Dv hDv hsum
      rw [Divisor.mem_degZero, hsum, map_sum] at hDv
      simp_rw [Divisor.degree_single, hd1, Nat.cast_one, mul_one] at hDv
      exact hDv
    intro j
    have hj : j = 0 ∨ j = 1 := by rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;> simp [h]
    rcases hj with rfl | rfl
    · exact key 0 _ hadm.1 hG0
    · exact key 1 _ hadm.2.1 hG1

  obtain ⟨eA0, ⟨eA1⟩⟩ := ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_abq_reduction_iso_pointTwist
    N₀ p hpN₀ 𝔓 A hA M.ρ M.hρ D hD hsepD hsm M.ε₀ M.D₀ M.rep hDκ hPκ hD₀κ hP₀κ hε₁' abq habq0 habq1 hDQ hPQ hsepQ ajQ hajQε hajQ
    kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hgal hpts_aj qq ss hqs pos neg hn E hDx s hsE sκ hsκ
    c y hy₁ hy₂ hc z hz hzy hnot hdeg

  have hIz : ∀ (u : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)))
      (hu : u ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _),
      (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) u hu).I.IsInvertible := fun u hu =>
    RelEffCartierDiv.isInvertible_I _
  have hLB := PrincTriv.isInvertible_twist_if c 1 _ (fun j => hIz (z j) (hz j)) pos neg (List.finRange n)
  obtain ⟨erig⟩ := PrincTriv.nonempty_iso_unit_of_field _
    (hLB.pullback (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) M.ε₀)))
  obtain ⟨eun⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified
    (⟨_, hLB, ⟨erig⟩⟩ : RigidifiedLineBundle (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) M.ε₀) (𝟙 _))
  have eA1' := (⟨eA1 ≪≫ eun⟩ : Nonempty _)

  have core0 := M3Sol.coord_copy N₀ p hpN₀ 𝔓 A hA M hJ hD₀κ hP₀κ hFE 0 𝔓.π (𝔓.comp_pi _ _) P.sp hred P.reduceFst
    (fun yq xq hyx => congrArg P.sp (ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeAlphaBar_of_comp_pi
      N₀ p hpN₀ 𝔓 A M hα yq xq hyx))
    qq ss hqs c y hy₁ hy₂ z hz hzy pos neg (hdeg 0) ?hDz0 (NeronModelInfra.schemeHomOverComp sκ (abq 0)) eA0 (r 0) (hrr 0)
  have core1 := M3Sol.coord_copy N₀ p hpN₀ 𝔓 A hA M hJ hD₀κ hP₀κ hFE 1 𝔓.πw (𝔓.comp1_πw _) P.sp hred P.reduceSnd
    (fun yq xq hyx => congrArg P.sp (ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
      N₀ p hpN₀ 𝔓 A M hβ yq xq hyx))
    qq ss hqs c y hy₁ hy₂ z hz hzy pos neg (hdeg 1) ?hDz1 (NeronModelInfra.schemeHomOverComp sκ (abq 1)) eA1' (r 1) (hrr 1)
  rw [hspx, GluedPic0.toPic0Pair_mk, core0, core1]
  refine Prod.ext ?_ ?_
  · show Pic0.mk _ = Pic0.mk _
    congr 1
    apply Subtype.ext
    show (∑ i ∈ Finset.univ.filter (fun i => c i = 0), Finsupp.single (P.reduceFst (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ))) =
      ((g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1
    rw [hG0]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [w, if_pos (Finset.mem_filter.mp hj).2]
  · show Pic0.mk _ = Pic0.mk _
    congr 1
    apply Subtype.ext
    show (∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ))) =
      ((g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1
    rw [hG1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : c j = 1 := (Finset.mem_filter.mp hj).2
    simp only [w, if_neg (fun h : c j = 0 => by rw [hj'] at h; exact absurd h (by decide))]
  case hDz0 =>
    rw [show (∑ i ∈ Finset.univ.filter (fun i => c i = 0), Finsupp.single (P.reduceFst (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ))) =
        ((g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1 from ?_]
    · exact hadm.1
    rw [hG0]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [w, if_pos (Finset.mem_filter.mp hj).2]
  case hDz1 =>
    rw [show (∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ((pos i : ℤ) - (neg i : ℤ))) =
        ((g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1 from ?_]
    · exact hadm.2.1
    rw [hG1]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : c j = 1 := (Finset.mem_filter.mp hj).2
    simp only [w, if_neg (fun h : c j = 0 => by rw [hj'] at h; exact absurd h (by decide))]

#print axioms solution

end
end S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_ptsSp_symm_abq_reduction_pair_eq_toPic0Pair_of_isGluedSpecialization (solution)
