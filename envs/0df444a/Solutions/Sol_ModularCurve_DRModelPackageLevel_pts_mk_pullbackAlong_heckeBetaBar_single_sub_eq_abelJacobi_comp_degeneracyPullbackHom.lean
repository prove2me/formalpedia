-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/92ffa68e-2d15-513b-9802-4af804d7d952

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP_LevelModel
import Definitions.Def_ModularCurve_ToricDescentData
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_ModularCurve_DegeneracyVp
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Definitions.Def_ModularCurve_GeometricBaseChange

import Definitions.Def_AlgebraicGeometry_RigidifiedLineBundleOfInvertible
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModuleMaps
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow
import Theorems.Thm_AlgebraicCurve_CurveModel_ker_comap_eq_prod_ker_pow_ramificationIndex
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_essFiniteType_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_DRModelPackageLevel_isFinite_flat_finrank_pi
import Theorems.Thm_ModularCurve_degeneracyPullbackInputs_of_prime
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_comap_mul
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_dual
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_pullback_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isIso_pullbackModuleComparison
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.TwoTermComplex.mk.injEq WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero"
p2m_attr_erase "simp" "WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"
p2m_attr_erase "simp" "FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply"
p2m_attr_erase "simp" "TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf"
set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicCurve"

noncomputable section

namespace PullOfPointAssembly

theorem comap_eq_map_inv {X Y : Scheme.{0}} (f : Y ⟶ X) [IsIso f] (J : X.IdealSheafData) :
    J.comap f = J.map (inv f) := by
  apply le_antisymm
  · have h : ((J.map (inv f)).map f).comap f ≤ J.map (inv f) :=
      Scheme.IdealSheafData.comap_map_le (J.map (inv f)) f
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.inv_hom_id, Scheme.IdealSheafData.map_id] at h
  · have h : J.map (inv f) ≤ ((J.comap f).map f).map (inv f) :=
      Scheme.IdealSheafData.map_mono (inv f) (Scheme.IdealSheafData.le_map_comap J f)
    rwa [← Scheme.IdealSheafData.map_comp, IsIso.hom_inv_id, Scheme.IdealSheafData.map_id] at h

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem ker_comap_eq_ker {X Y T : Scheme.{0}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) (p' : T ⟶ Y)
    (hp : p' ≫ f = p) : p.ker.comap f = p'.ker := by
  rw [comap_eq_map_inv, Scheme.IdealSheafData.map_ker, ← hp, Category.assoc, IsIso.hom_inv_id,
    Category.comp_id]

theorem comap_pow {X Y : Scheme.{0}} (f : Y ⟶ X) (I : X.IdealSheafData) (n : ℕ) :
    (I ^ n).comap f = (I.comap f) ^ n := by
  induction n with
  | zero =>
      rw [pow_zero, pow_zero, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.one_eq_top,
        Scheme.IdealSheafData.comap_top]
  | succ n ih =>
      rw [pow_succ, pow_succ, Scheme.IdealSheafData.comap_mul, ih]

theorem comap_prod {X Y : Scheme.{0}} (f : Y ⟶ X) {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData) :
    (∏ i ∈ s, I i).comap f = ∏ i ∈ s, (I i).comap f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top, Scheme.IdealSheafData.comap_top]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.prod_insert ha, Scheme.IdealSheafData.comap_mul, ih]

theorem isInvertible_prod {X : Scheme.{0}} {ι : Type*} (s : Finset ι) (I : ι → X.IdealSheafData)
    (h : ∀ i ∈ s, (I i).IsInvertible) : (∏ i ∈ s, I i).IsInvertible := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem poincare_mul {R : Type} [CommRing R] {C : Scheme.{0}} {c : C ⟶ Spec (CommRingCat.of R)}
    {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c}
    {P : SubPicGroupCondition c ε} {D : RelativePic0Designation R c}
    (h : RepresentsRelSubPic c ε P.toSubPicCondition D)
    {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t D.toBase) :
    Nonempty ((h.poincare.pullbackAlong (h.relativeGroupLaw.mul t x y)).L ≅
      (h.poincare.pullbackAlong x).L ⊗ (h.poincare.pullbackAlong y).L) :=
  h.nonempty_poincare_pullbackAlong_mul_iso (T := Over.mk t)
    (schemeHomOverToOverHom x) (schemeHomOverToOverHom y)

theorem isInvertible_I_ofPoint_field {R : Type} [CommRing R] {K : Type} [Field K] {C : Scheme.{0}}
    (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R))
    [SmoothOfRelativeDimension 1 (pullback.snd c t)] (x : Spec (CommRingCat.of K) ⟶ C) (hx : x ≫ c = t) :
    (RelEffCartierDiv.ofPoint c x hx).I.IsInvertible := by
  haveI : IsSeparated (pullback.snd c t) := MorphismProperty.pullback_snd (P := @IsSeparated) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) := by
    have : SmoothOfRelativeDimension (0 + 1) ((⊤ : (pullback c t).Opens).ι ≫ pullback.snd c t) := inferInstance
    simpa using this
  exact Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens (pullback.snd c t) ⊤ (graphOver c x hx)
    (graphOver_snd c x hx) trivial

end PullOfPointAssembly

end

open PullOfPointAssembly

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

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
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (M : LevelModel N₀ p A) (hM : M.toLevelData.IsJacobian)

    (βstar : SchemeHomOver M.D₀.toBase D.toBase)
    (hβ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (b : SchemeHomOver t M.D₀.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp b βstar)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase N₀ p) t 𝔓.εinf) (pullback.snd (toBase N₀ p) t)
          ((Scheme.Modules.pullback (curveChange 𝔓.πw.1 𝔓.πw.2 t)).obj (M.rep.poincare.pullbackAlong b).L)))
    (hβhom : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (R p))) (x y : SchemeHomOver t M.D₀.toBase),
      NeronModelInfra.schemeHomOverComp (M.law.mul t x y) βstar =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul t
          (NeronModelInfra.schemeHomOverComp x βstar) (NeronModelInfra.schemeHomOverComp y βstar))

    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))]
    (hint : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)

    (x s₀ : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
    (hs₀ : s₀.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) = genPt p ≫ M.ε₀.1)
    (E' : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)))
    (hE' : (E' : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint
          (Finsupp.single (M.Meta₀.pointEquivPlace x) 1) -
        Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint
          (Finsupp.single (M.Meta₀.pointEquivPlace s₀) 1)) :
    (pts (Pic0.mk E')).1 =
      (x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) ≫ βstar.1 := by
  classical
  haveI : IsProper (IgusaScheme.igusaTo N₀ p) := M.proper₀

  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar (N₀ * p)
  haveI := ModularCurve.isCurveOver_modularFunctionFieldBar N₀
  haveI := ModularCurve.essFiniteType_modularFunctionFieldBar (N₀ * p)
  haveI := ModularCurve.essFiniteType_modularFunctionFieldBar N₀
  letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p)
  haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) N₀ p)
  haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint

  obtain ⟨hfin, hlfp, hfl, hrk⟩ := ModularCurve.DRModelPackageLevel.isFinite_flat_finrank_pi N₀ p hpN₀ 𝔓
  haveI := hfin; haveI := hlfp; haveI := hfl
  haveI : IsFinite 𝔓.πw.1 := (inferInstance : IsFinite (𝔓.w.hom ≫ 𝔓.π.1))
  haveI : Flat 𝔓.πw.1 := (inferInstance : Flat (𝔓.w.hom ≫ 𝔓.π.1))
  haveI : LocallyOfFinitePresentation 𝔓.πw.1 := (inferInstance : LocallyOfFinitePresentation (𝔓.w.hom ≫ 𝔓.π.1))

  haveI : SmoothOfRelativeDimension 1 (pullback.snd (toBase N₀ p) (genPt p)) := by
    have e : pullback.snd (toBase N₀ p) (genPt p) = inv 𝔓.eeta ≫ 𝔓.Meta.toBase := by
      rw [← 𝔓.heeta, IsIso.inv_hom_id_assoc]
    rw [e]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance
  haveI : SmoothOfRelativeDimension 1 (pullback.snd (IgusaScheme.igusaTo N₀ p) (genPt p)) := by
    have e : pullback.snd (IgusaScheme.igusaTo N₀ p) (genPt p) = inv M.eeta₀ ≫ M.Meta₀.toBase := by
      rw [← M.heeta₀, IsIso.inv_hom_id_assoc]
    rw [e]; exact MorphismProperty.RespectsIso.precomp (P := @SmoothOfRelativeDimension 1) _ _ inferInstance

  set cc := curveChange 𝔓.πw.1 𝔓.πw.2 (genPt p) with hcc
  let πM : 𝔓.Meta.C ⟶ M.Meta₀.C := 𝔓.eeta ≫ cc ≫ inv M.eeta₀
  have hinv₀ : inv M.eeta₀ ≫ M.Meta₀.toBase = pullback.snd (IgusaScheme.igusaTo N₀ p) (genPt p) := by
    rw [IsIso.inv_comp_eq, M.heeta₀]
  have hπM : πM ≫ M.Meta₀.toBase = 𝔓.Meta.toBase := by
    simp only [πM, Category.assoc, hinv₀, hcc, curveChange_snd, 𝔓.heeta]
  have hπM₁ : πM ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
      𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1 := by
    simp only [πM, Category.assoc, IsIso.inv_hom_id_assoc, hcc, curveChange, pullback.lift_fst]
  have hccπ : cc = inv 𝔓.eeta ≫ πM ≫ M.eeta₀ := by
    simp only [πM, Category.assoc, IsIso.inv_hom_id, Category.comp_id, IsIso.inv_hom_id_assoc]
  haveI : IsFinite cc := by
    rw [hcc]; exact MorphismProperty.pullbackMap (P := @IsFinite) ‹IsFinite 𝔓.πw.1› (inferInstance : IsFinite (𝟙 _))
      (𝔓.πw.2).symm (Category.id_comp _).symm
  haveI : Flat cc := by
    rw [hcc]; exact MorphismProperty.pullbackMap (P := @Flat) ‹Flat 𝔓.πw.1› (inferInstance : Flat (𝟙 _))
      (𝔓.πw.2).symm (Category.id_comp _).symm
  haveI : LocallyOfFinitePresentation cc := by
    rw [hcc]; exact MorphismProperty.pullbackMap (P := @LocallyOfFinitePresentation) ‹LocallyOfFinitePresentation 𝔓.πw.1›
      (inferInstance : LocallyOfFinitePresentation (𝟙 _)) (𝔓.πw.2).symm (Category.id_comp _).symm
  haveI : IsFinite πM := inferInstance
  haveI : Flat πM := inferInstance
  haveI : LocallyOfFinitePresentation πM := inferInstance

  have hplace : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}) (z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _}),
      y.1 ≫ πM = z.1 → (𝔓.Meta.pointEquivPlace y).restrict ↥(modularFunctionFieldBar N₀) = M.Meta₀.pointEquivPlace z := by
    intro y z hyz
    have hzx : z.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) =
        y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) ≫ 𝔓.πw.1 := by
      rw [← hyz, Category.assoc, hπM₁]
    exact (ModularCurve.DRModelPackageLevel.pointEquivPlace_eq_restrictAlong_heckeBetaBar_of_comp_piw
      N₀ p hpN₀ 𝔓 A M hint y z hzx).symm

  let ybar : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) → SchemeHomOver (genPt p) (toBase N₀ p) := fun w =>
    ⟨(𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% 𝔓.heeta, reassoc_of% (𝔓.Meta.pointEquivPlace.symm w).2]⟩
  have hybar : ∀ w, (ybar w).1 = (𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) := fun w => rfl
  let zbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _} →
      SchemeHomOver (genPt p) (IgusaScheme.igusaTo N₀ p) := fun z =>
    ⟨z.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p), by
      simp only [Category.assoc, pullback.condition]; rw [reassoc_of% M.heeta₀, reassoc_of% z.2]⟩
  have key : ∀ z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _},
      (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (zbar z).1 (zbar z).2).I.comap cc =
        ∏ w ∈ (M.Meta₀.pointEquivPlace z).fiber ↥(modularFunctionFieldBar (N₀ * p)),
          (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀)) := by
    intro z

    have hg₀ : graphOver (IgusaScheme.igusaTo N₀ p) (zbar z).1 (zbar z).2 = z.1 ≫ M.eeta₀ := by
      apply pullback.hom_ext
      · rw [graphOver_fst]; rfl
      · rw [graphOver_snd, Category.assoc, M.heeta₀, z.2]
    have hg : ∀ w, graphOver (toBase N₀ p) (ybar w).1 (ybar w).2 = (𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta := by
      intro w
      apply pullback.hom_ext
      · rw [graphOver_fst]; rfl
      · rw [graphOver_snd, Category.assoc, 𝔓.heeta, (𝔓.Meta.pointEquivPlace.symm w).2]
    change (graphOver (IgusaScheme.igusaTo N₀ p) (zbar z).1 (zbar z).2).ker.comap cc =
      ∏ w ∈ (M.Meta₀.pointEquivPlace z).fiber ↥(modularFunctionFieldBar (N₀ * p)),
        (graphOver (toBase N₀ p) (ybar w).1 (ybar w).2).ker ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀))
    rw [hg₀, hccπ, Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.comap_comp,
      ker_comap_eq_ker M.eeta₀ (z.1 ≫ M.eeta₀) z.1 rfl,
      AlgebraicCurve.CurveModel.ker_comap_eq_prod_ker_pow_ramificationIndex M.Meta₀ 𝔓.Meta πM hπM hplace z,
      comap_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [comap_pow, hg w, ker_comap_eq_ker (inv 𝔓.eeta) (𝔓.Meta.pointEquivPlace.symm w).1
      ((𝔓.Meta.pointEquivPlace.symm w).1 ≫ 𝔓.eeta) (by simp)]

  have key2 : ∀ (z : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ M.Meta₀.C // q ≫ M.Meta₀.toBase = 𝟙 _})
      (q : SchemeHomOver (genPt p) (IgusaScheme.igusaTo N₀ p)),
      q.1 = z.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) →
      (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) q.1 q.2).I.comap cc =
        ∏ w ∈ (M.Meta₀.pointEquivPlace z).fiber ↥(modularFunctionFieldBar (N₀ * p)),
          (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀)) := by
    intro z q hq
    have hqq : q = zbar z := Subtype.ext hq
    subst hqq
    exact key z

  have hIy : ∀ w, (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I.IsInvertible := fun w =>
    isInvertible_I_ofPoint_field (toBase N₀ p) (genPt p) (ybar w).1 (ybar w).2
  have hPI : ∀ (S : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))),
      (∏ w ∈ S, (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀))).IsInvertible :=
    fun S => isInvertible_prod S _ fun w _ => (hIy w).pow _
  have pε : (genPt p ≫ 𝔓.εinf.1) ≫ toBase N₀ p = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) 𝔓.εinf.2).trans (Category.comp_id _))
  have hIε : (RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) pε).I.IsInvertible :=
    isInvertible_I_ofPoint_field (toBase N₀ p) (genPt p) _ pε
  have pε₀ : (genPt p ≫ M.ε₀.1) ≫ IgusaScheme.igusaTo N₀ p = genPt p :=
    (Category.assoc _ _ _).trans ((congrArg (genPt p ≫ ·) M.ε₀.2).trans (Category.comp_id _))

  set v := M.Meta₀.pointEquivPlace x with hv
  set v₀ := M.Meta₀.pointEquivPlace s₀ with hv₀
  have hpull : DegeneracyPullbackInputs N₀ p := ModularCurve.degeneracyPullbackInputs_of_prime N₀ p Fact.out
  haveI hFI : FundamentalIdentity (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀) ↥(modularFunctionFieldBar (N₀ * p)) := hpull.snd.snd.snd.2
  have hsum : ∀ u : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀),
      ((∑ w ∈ u.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀) : ℕ) : ℤ) = (Module.finrank ↥(modularFunctionFieldBar N₀) ↥(modularFunctionFieldBar (N₀ * p)) : ℤ) := by
    intro u
    have h := FundamentalIdentity.sum_ramificationIndex_mul_deg (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N₀)) (F' := ↥(modularFunctionFieldBar (N₀ * p))) u
    simp only [ModularCurve.deg_eq_one_modularFunctionFieldBar, Nat.cast_one, mul_one] at h
    rw [Nat.cast_sum]; exact h
  have hnn : (∑ w ∈ v₀.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀)) = ∑ w ∈ v.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀) := by
    have := (hsum v₀).trans (hsum v).symm; exact_mod_cast this

  have hdegZ : ∀ u : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀),
      (∑ w ∈ u.fiber ↥(modularFunctionFieldBar (N₀ * p)), (w.ramificationIndex ↥(modularFunctionFieldBar N₀) : ℤ) • Finsupp.single w 1 -
        ((∑ w ∈ u.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀) : ℕ) : ℤ) • Finsupp.single (𝔓.Meta.pointEquivPlace εbar) 1 :
          Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p))) := by
    intro u
    rw [Divisor.mem_degZero, map_sub, map_sum, map_zsmul, Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar]
    simp only [map_zsmul, Divisor.degree_single, ModularCurve.deg_eq_one_modularFunctionFieldBar, Nat.cast_one, smul_eq_mul, mul_one,
      Nat.cast_sum, sub_self]
  let Dz : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀) → Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p))) := fun u => ⟨_, hdegZ u⟩
  obtain ⟨ix⟩ := ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂
    ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hpts_galois hpts_aj
    (v.fiber ↥(modularFunctionFieldBar (N₀ * p))) (fun w => w.ramificationIndex ↥(modularFunctionFieldBar N₀)) ybar hybar (Dz v) rfl
  obtain ⟨is⟩ := ModularCurve.DRModelPackageLevel.nonempty_poincare_pullbackAlong_pts_mk_iso_invModule_prod_pow_tensor_module_pow N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂
    ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hpts_galois hpts_aj
    (v₀.fiber ↥(modularFunctionFieldBar (N₀ * p))) (fun w => w.ramificationIndex ↥(modularFunctionFieldBar N₀)) ybar hybar (Dz v₀) rfl

  have hconorm : ∀ u : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N₀),
      Divisor.pullbackAlong (heckeBetaBar (AlgebraicClosure ℚ) N₀ p) hint (Finsupp.single u 1) =
        ∑ w ∈ u.fiber ↥(modularFunctionFieldBar (N₀ * p)), (w.ramificationIndex ↥(modularFunctionFieldBar N₀) : ℤ) • Finsupp.single w 1 := by
    intro u
    change Divisor.pullback ↥(modularFunctionFieldBar (N₀ * p)) (Finsupp.single u 1) = _
    rw [Divisor.pullback_single]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [one_mul, Finsupp.smul_single, smul_eq_mul, mul_one]
  have hE'D : Pic0.mk E' + Pic0.mk (Dz v₀) = Pic0.mk (Dz v) := by
    rw [← Pic0.mk_add]; congr 1; apply Subtype.ext
    rw [AddMemClass.coe_add, hE', hconorm, hconorm]
    show _ + (_ - _) = (_ - _ : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
    rw [hnn]; abel

  let b : SchemeHomOver (genPt p) M.D₀.toBase :=
    ⟨(zbar x).1 ≫ M.aj₀.1, (Category.assoc _ _ _).trans ((congrArg ((zbar x).1 ≫ ·) M.aj₀.2).trans (zbar x).2)⟩
  obtain ⟨hbM⟩ := M.haj₀ (AlgebraicClosure ℚ) (genPt p) (zbar x)
  let a : SchemeHomOver (genPt p) D.toBase := NeronModelInfra.schemeHomOverComp b βstar
  have ha1 : a.1 = (x.1 ≫ M.eeta₀ ≫ pullback.fst (IgusaScheme.igusaTo N₀ p) (genPt p) ≫ M.aj₀.1) ≫ βstar.1 := by
    rw [NeronModelInfra.schemeHomOverComp_coe]; simp only [Category.assoc]; rfl
  let Mb : RigidifiedLineBundle (IgusaScheme.igusaTo N₀ p) M.ε₀ (genPt p) := M.rep.poincare.pullbackAlong b
  have hinvM : Scheme.Modules.IsInvertible ((Scheme.Modules.pullback cc).obj Mb.L) := Mb.isInvertible.pullback _
  obtain ⟨e1⟩ : Nonempty ((hD.poincare.pullbackAlong a).L ≅
      (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) ((Scheme.Modules.pullback cc).obj Mb.L) hinvM).L) := hβ (genPt p) b

  have hIx : (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (zbar x).1 (zbar x).2).I.IsInvertible :=
    isInvertible_I_ofPoint_field (IgusaScheme.igusaTo N₀ p) (genPt p) _ (zbar x).2
  have hIε₀ : (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (genPt p ≫ M.ε₀.1) pε₀).I.IsInvertible :=
    isInvertible_I_ofPoint_field (IgusaScheme.igusaTo N₀ p) (genPt p) _ pε₀
  have kx := key2 x (zbar x) rfl
  have kε : (RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (genPt p ≫ M.ε₀.1) pε₀).I.comap cc =
      ∏ w ∈ v₀.fiber ↥(modularFunctionFieldBar (N₀ * p)), (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀)) :=
    key2 s₀ ⟨genPt p ≫ M.ε₀.1, pε₀⟩ hs₀.symm
  have hIx' : ((RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (zbar x).1 (zbar x).2).I.comap cc).IsInvertible := by
    rw [kx]; exact hPI _
  have hIε₀' : ((RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (genPt p ≫ M.ε₀.1) pε₀).I.comap cc).IsInvertible := by
    rw [kε]; exact hPI _
  obtain ⟨n1⟩ := Scheme.IdealSheafData.IsInvertible.nonempty_pullback_invModule_iso cc hIx hIx'
  have h2 := Scheme.IdealSheafData.IsInvertible.isIso_pullbackModuleComparison cc hIε₀ hIε₀'
  let n2 := @asIso _ _ _ _ ((RelEffCartierDiv.ofPoint (IgusaScheme.igusaTo N₀ p) (genPt p ≫ M.ε₀.1) pε₀).I.pullbackModuleComparison cc) h2
  let Px := ∏ w ∈ v.fiber ↥(modularFunctionFieldBar (N₀ * p)), (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀))
  let Ps := ∏ w ∈ v₀.fiber ↥(modularFunctionFieldBar (N₀ * p)), (RelEffCartierDiv.ofPoint (toBase N₀ p) (ybar w).1 (ybar w).2).I ^ (w.ramificationIndex ↥(modularFunctionFieldBar N₀))
  let Iε := (RelEffCartierDiv.ofPoint (toBase N₀ p) (genPt p ≫ 𝔓.εinf.1) pε).I
  have pull : (Scheme.Modules.pullback cc).obj Mb.L ≅ Px.invModule ⊗ Ps.module :=
    (Scheme.Modules.pullback cc).mapIso hbM ≪≫ Scheme.Modules.pullbackTensorObjIso cc _ _ ≪≫
      ((n1 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.invModule kx)) ⊗ᵢ (n2 ≪≫ eqToIso (congrArg Scheme.IdealSheafData.module kε)))
  have hinvP : Scheme.Modules.IsInvertible (Px.invModule ⊗ Ps.module) :=
    ((hPI _).isInvertible_invModule).tensor ((hPI _).isInvertible_module)

  obtain ⟨mi, -⟩ := (hPI (v₀.fiber ↥(modularFunctionFieldBar (N₀ * p)))).nonempty_module_tensor_invModule_iso
  obtain ⟨mi⟩ := mi
  have hpow : (Iε ^ (∑ w ∈ v₀.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀))).module =
      (Iε ^ (∑ w ∈ v.fiber ↥(modularFunctionFieldBar (N₀ * p)), w.ramificationIndex ↥(modularFunctionFieldBar N₀))).module := by rw [hnn]
  have raw : (Scheme.Modules.pullback cc).obj Mb.L ⊗ (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v₀)))).L ≅
      (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v)))).L :=
    (pull ⊗ᵢ is) ≪≫ α_ _ _ _ ≪≫
      (Iso.refl _ ⊗ᵢ ((α_ _ _ _).symm ≪≫ (mi ⊗ᵢ Iso.refl _) ≪≫ λ_ _ ≪≫ eqToIso hpow)) ≪≫ ix.symm

  obtain ⟨r1⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v₀))))
  obtain ⟨r2⟩ := RigidifiedLineBundle.nonempty_ofInvertible_tensor_iso (ε := 𝔓.εinf) hinvM
    (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v₀)))).isInvertible
  obtain ⟨r3⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_iso (ε := 𝔓.εinf)
    (hinvM.tensor (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v₀)))).isInvertible)
    (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v)))).isInvertible raw
  obtain ⟨r4⟩ := RigidifiedLineBundle.nonempty_ofInvertible_iso_of_rigidified (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v))))
  have keyIso : (RigidifiedLineBundle.ofInvertible (ε := 𝔓.εinf) ((Scheme.Modules.pullback cc).obj Mb.L) hinvM).L ⊗
      (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v₀)))).L ≅ (hD.poincare.pullbackAlong (pts (Pic0.mk (Dz v)))).L :=
    (Iso.refl _ ⊗ᵢ r1.symm) ≪≫ r2.symm ≪≫ r3 ≪≫ r4

  obtain ⟨emul⟩ := poincare_mul (P := algEquivZeroGroupCut (toBase N₀ p) 𝔓.εinf) hD (genPt p) a (pts (Pic0.mk (Dz v₀)))
  have hmul : (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul (genPt p) a (pts (Pic0.mk (Dz v₀))) =
      pts (Pic0.mk (Dz v)) :=
    hD.ext_of_iso (genPt p) _ _ ⟨emul ≪≫ (e1 ⊗ᵢ Iso.refl _) ≪≫ keyIso⟩
  have hkey : pts (Pic0.mk E') = a := by
    have h1 : pts (Pic0.mk E' + Pic0.mk (Dz v₀)) = pts (pts.symm a + Pic0.mk (Dz v₀)) := by
      rw [hE'D, hpts_add, Equiv.apply_symm_apply, hmul]
    have h2 := add_right_cancel (pts.injective h1)
    rw [h2, Equiv.apply_symm_apply]
  rw [hkey, ha1]

end S_ModularCurve_DRModelPackageLevel_pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_pts_mk_pullbackAlong_heckeBetaBar_single_sub_eq_abelJacobi_comp_degeneracyPullbackHom (solution)
