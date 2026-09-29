-- Prove2me | solution 1 for ModularCurve.XOneP.addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e699637d-ec91-560c-94df-1767499d1e4a

import Mathlib
import Definitions.Def_ModularCurve_TwoChartModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_JOnePGeom
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_JacJ1Iface
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_ModularCurve_JOnePOpsV2
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_IgusaFunctionFieldX1
import Definitions.Def_AlgebraicCurve_GluedPic0
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicCurve_RelCartier
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing
import Theorems.Thm_ModularCurve_XOneP_pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
import Theorems.Thm_ModularCurve_XOneP_mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion"
p2m_attr_erase "instance" "ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin"
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk"
p2m_attr_erase "simp" "AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X"
p2m_attr_erase "simp" "AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq"
p2m_attr_erase "simp" "CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP"
p2m_attr_erase "simp" "ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub"
p2m_attr_erase "simp" "KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen"
p2m_attr_erase "simp" "ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve"

universe u

namespace Ws5B13PicTwist

theorem induce {J : Type*} [AddCommGroup J] (S : Set J) (hS : AddSubgroup.closure S = ⊤)
    (T Q : J → J → Prop)
    (huniq : ∀ g g' g'', T g g' → T g g'' → g' = g'')
    (hbase : ∀ g ∈ S, ∃ g', T g g' ∧ Q g g')
    (hzero : ∃ z, T 0 z ∧ Q 0 z)
    (hadd : ∀ a a' b b', T a a' → Q a a' → T b b' → Q b b' → T (a + b) (a' + b') ∧ Q (a + b) (a' + b'))
    (hneg : ∀ a a', T a a' → Q a a' → T (-a) (-a') ∧ Q (-a) (-a')) :
    ∀ g g', T g g' → Q g g' := by
  have key : ∀ g, ∃ g', T g g' ∧ Q g g' := by
    intro g
    have hg : g ∈ AddSubgroup.closure S := by rw [hS]; trivial
    induction hg using AddSubgroup.closure_induction with
    | mem x hx => exact hbase x hx
    | zero => exact hzero
    | add a b _ _ iha ihb =>
      obtain ⟨a', hTa, hQa⟩ := iha
      obtain ⟨b', hTb, hQb⟩ := ihb
      exact ⟨a' + b', hadd a a' b b' hTa hQa hTb hQb⟩
    | neg a _ ih =>
      obtain ⟨a', hTa, hQa⟩ := ih
      exact ⟨-a', hneg a a' hTa hQa⟩
  intro g g' hT
  obtain ⟨g'', hT'', hQ''⟩ := key g
  rw [huniq g g' g'' hT hT'']
  exact hQ''

variable {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
  {ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c} {P : SubPicCondition c ε} {D : RelativePic0Designation R c}

theorem eq_of_poincare_iso (h : RepresentsRelSubPic c ε P D) {J : Type*} (φ : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    {N : (pullback c (𝟙 (Spec (CommRingCat.of R)))).Modules} {g' g'' : J}
    (h' : Nonempty ((h.poincare.pullbackAlong (φ g')).L ≅ N)) (h'' : Nonempty ((h.poincare.pullbackAlong (φ g'')).L ≅ N)) :
    g' = g'' :=
  φ.injective (h.ext_of_iso (𝟙 _) _ _ ⟨h'.some ≪≫ h''.some.symm⟩)

theorem twist_add (h : RepresentsRelSubPic c ε P D) {J : Type*} [Add J]
    (φ : J → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (hadd : ∀ a b : J, Nonempty ((h.poincare.pullbackAlong (φ (a + b))).L ≅
      (h.poincare.pullbackAlong (φ a)).L ⊗ (h.poincare.pullbackAlong (φ b)).L))
    (Φ : pullback c (𝟙 (Spec (CommRingCat.of R))) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) (a a' b b' : J)
    (ha : Nonempty ((h.poincare.pullbackAlong (φ a')).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ a)).L))
    (hb : Nonempty ((h.poincare.pullbackAlong (φ b')).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ b)).L)) :
    Nonempty ((h.poincare.pullbackAlong (φ (a' + b'))).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ (a + b))).L) :=
  ⟨(hadd a' b').some ≪≫ (ha.some ⊗ᵢ hb.some) ≪≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback Φ) _ _) ≪≫
    (Scheme.Modules.pullback Φ).mapIso (hadd a b).some.symm⟩

theorem twist_zero (h : RepresentsRelSubPic c ε P D) {J : Type*} [Zero J]
    (φ : J → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (h0 : Nonempty ((h.poincare.pullbackAlong (φ 0)).L ≅ 𝟙_ _))
    (Φ : pullback c (𝟙 (Spec (CommRingCat.of R))) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) :
    Nonempty ((h.poincare.pullbackAlong (φ 0)).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ 0)).L) :=
  ⟨h0.some ≪≫ (Scheme.Modules.pullbackUnitIso Φ).symm ≪≫ (Scheme.Modules.pullback Φ).mapIso h0.some.symm⟩

theorem twist_neg (h : RepresentsRelSubPic c ε P D) {J : Type*} [AddGroup J]
    (φ : J → SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (h0 : Nonempty ((h.poincare.pullbackAlong (φ 0)).L ≅ 𝟙_ _))
    (hadd : ∀ a b : J, Nonempty ((h.poincare.pullbackAlong (φ (a + b))).L ≅
      (h.poincare.pullbackAlong (φ a)).L ⊗ (h.poincare.pullbackAlong (φ b)).L))
    (Φ : pullback c (𝟙 (Spec (CommRingCat.of R))) ⟶ pullback c (𝟙 (Spec (CommRingCat.of R)))) (a a' : J)
    (ha : Nonempty ((h.poincare.pullbackAlong (φ a')).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ a)).L)) :
    Nonempty ((h.poincare.pullbackAlong (φ (-a'))).L ≅ (Scheme.Modules.pullback Φ).obj (h.poincare.pullbackAlong (φ (-a))).L) := by
  have e0 : ∀ x : J, (h.poincare.pullbackAlong (φ (x + -x))).L ≅ 𝟙_ _ := fun x => by
    rw [add_neg_cancel]; exact h0.some
  refine CategoryTheory.MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit ha.some ⟨?_⟩ ⟨?_⟩
  · exact (hadd a' (-a')).some.symm ≪≫ e0 a'
  · exact (Functor.Monoidal.μIso (Scheme.Modules.pullback Φ) _ _) ≪≫
      (Scheme.Modules.pullback Φ).mapIso ((hadd a (-a)).some.symm ≪≫ e0 a) ≪≫ Scheme.Modules.pullbackUnitIso Φ

theorem eq_zero_of_poincare_iso_unit (h : RepresentsRelSubPic c ε P D)
    {J : Type*} [AddCommGroup J] (φ : J ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) D.toBase)
    (hadd : ∀ a b : J, Nonempty ((h.poincare.pullbackAlong (φ (a + b))).L ≅
      (h.poincare.pullbackAlong (φ a)).L ⊗ (h.poincare.pullbackAlong (φ b)).L))
    (x : J) (hx : Nonempty ((h.poincare.pullbackAlong (φ x)).L ≅ 𝟙_ (pullback c (𝟙 (Spec (CommRingCat.of R)))).Modules)) :
    x = 0 := by
  obtain ⟨e⟩ := hx
  have key : φ (x + x) = φ x :=
    h.ext_of_iso (𝟙 _) _ _ ⟨(hadd x x).some ≪≫ (e ⊗ᵢ e) ≪≫ (λ_ _) ≪≫ e.symm⟩
  exact add_left_cancel ((φ.injective key).trans (add_zero x).symm)

end Ws5B13PicTwist

namespace Ws5B13PicTwist

theorem nonempty_pullback_ofPoint_iso {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsSeparated c] [SmoothOfRelativeDimension 1 c]
    (φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k)) [IsIso φ]
    (Φ : pullback c (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback c (𝟙 (Spec (CommRingCat.of k)))) [IsIso Φ]
    (x x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c)
    (hx : graphOver c x'.1 x'.2 ≫ Φ = φ ≫ graphOver c x.1 x.2) :
    Nonempty ((Scheme.Modules.pullback Φ).obj (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ≅
        (RelEffCartierDiv.ofPoint c x'.1 x'.2).lineBundle) ∧
      Nonempty ((Scheme.Modules.pullback Φ).obj (RelEffCartierDiv.ofPoint c x.1 x.2).idealModule ≅
        (RelEffCartierDiv.ofPoint c x'.1 x'.2).idealModule) := by
  have hp : (inv φ ≫ graphOver c x'.1 x'.2) ≫ Φ = graphOver c x.1 x.2 := by
    rw [Category.assoc, hx, IsIso.inv_hom_id_assoc]
  have hI : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c, (graphOver c z.1 z.2).ker.IsInvertible := fun z =>
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c (𝟙 _)) (graphOver c z.1 z.2) (graphOver_snd c z.1 z.2)
  have hI' : (inv φ ≫ graphOver c x'.1 x'.2).ker.IsInvertible := by
    rw [Scheme.Hom.ker_comp_of_isIso]; exact hI x'
  obtain ⟨⟨e₁⟩, ⟨e₂⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Φ (graphOver c x.1 x.2)
    (inv φ ≫ graphOver c x'.1 x'.2) hp (hI x) hI' 1
  have hk : (inv φ ≫ graphOver c x'.1 x'.2).ker = (graphOver c x'.1 x'.2).ker := Scheme.Hom.ker_comp_of_isIso _ _
  refine ⟨⟨(Scheme.Modules.pullback Φ).mapIso (eqToIso ?_) ≪≫ e₁ ≪≫ eqToIso ?_⟩,
    ⟨(Scheme.Modules.pullback Φ).mapIso (eqToIso ?_) ≪≫ e₂ ≪≫ eqToIso ?_⟩⟩
  · show (RelEffCartierDiv.ofPoint c x.1 x.2).I.invModule = _
    rw [RelEffCartierDiv.ofPoint_I, pow_one]
  · show _ = (RelEffCartierDiv.ofPoint c x'.1 x'.2).I.invModule
    rw [RelEffCartierDiv.ofPoint_I, hk, pow_one]
  · show (RelEffCartierDiv.ofPoint c x.1 x.2).I.module = _
    rw [RelEffCartierDiv.ofPoint_I, pow_one]
  · show _ = (RelEffCartierDiv.ofPoint c x'.1 x'.2).I.module
    rw [RelEffCartierDiv.ofPoint_I, hk, pow_one]

end Ws5B13PicTwist

namespace Ws5B13PicTwist

section Pic
variable {K F : Type*} [Field K] [Field F] [Algebra K F]
open AlgebraicCurve

theorem q_zero (σ : SemilinearAut K F) {J : Type*} [AddCommGroup J] (θ : J ≃+ Pic0 K F) :
    θ 0 = σ • θ 0 := by rw [map_zero]; exact (smul_zero (A := Pic0 K F) σ).symm

theorem q_add (σ : SemilinearAut K F) {J : Type*} [AddCommGroup J] (θ : J ≃+ Pic0 K F) (a a' b b' : J)
    (ha : θ a' = σ • θ a) (hb : θ b' = σ • θ b) : θ (a' + b') = σ • θ (a + b) := by
  rw [map_add, map_add, smul_add, ha, hb]

theorem q_neg (σ : SemilinearAut K F) {J : Type*} [AddCommGroup J] (θ : J ≃+ Pic0 K F) (a a' : J)
    (ha : θ a' = σ • θ a) : θ (-a') = σ • θ (-a) := by
  rw [map_neg, map_neg, smul_neg, ha]

theorem q_base (σ : SemilinearAut K F) {P P' E : Place K F} (hP : P' = σ • P) (hE : E = σ • E)
    (Dv Dv' : Divisor.degZero (K := K) (F := F))
    (hDv : (Dv : Divisor K F) = Finsupp.single P 1 - Finsupp.single E 1)
    (hDv' : (Dv' : Divisor K F) = Finsupp.single P' 1 - Finsupp.single E 1) :
    Pic0.mk Dv' = σ • Pic0.mk Dv := by
  rw [SemilinearAut.pic0_smul_mk]
  congr 1
  apply Subtype.ext
  rw [SemilinearAut.coe_degZeroSMulHom, hDv, hDv', smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, ← hP, ← hE]

theorem mk_single_sub_single_eq (Dc Dc' : Divisor.degZero (K := K) (F := F)) {P P' E : Place K F}
    (hc : (Dc : Divisor K F) = Finsupp.single P 1 - Finsupp.single E 1)
    (hc' : (Dc' : Divisor K F) = Finsupp.single P' 1 - Finsupp.single E 1)
    (hdeg : Finsupp.single P (1 : ℤ) - Finsupp.single P' 1 ∈ Divisor.degZero (K := K) (F := F)) :
    Pic0.mk ⟨Finsupp.single P 1 - Finsupp.single P' 1, hdeg⟩ = Pic0.mk Dc - Pic0.mk Dc' := by
  have : (⟨Finsupp.single P 1 - Finsupp.single P' 1, hdeg⟩ : Divisor.degZero (K := K) (F := F)) = Dc - Dc' := by
    apply Subtype.ext
    simp only [AddSubgroupClass.coe_sub, hc, hc', sub_sub_sub_cancel_right]
  rw [this]
  rfl

end Pic

end Ws5B13PicTwist

open Ws5B13PicTwist in

theorem solution
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hM : 5 ≤ M) (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ)
    [Algebra A ↥K] [IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]

    (k : Type) [Field k] [IsAlgClosed k] [CharP k p] [Algebra A k]
    (C₁ C₂ : Scheme.{0}) (c₁ : C₁ ⟶ Spec (CommRingCat.of k)) (c₂ : C₂ ⟶ Spec (CommRingCat.of k))
    [IsProper c₁] [SmoothOfRelativeDimension 1 c₁] [GeometricallyIntegral c₁]
    [IsProper c₂] [SmoothOfRelativeDimension 1 c₂] [GeometricallyIntegral c₂]
    (i₁ : SchemeHomOver c₁ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k)) (i₂ : SchemeHomOver c₂ (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k))
    [IsClosedImmersion i₁.1] [IsClosedImmersion i₂.1]
    (hcover : ∀ z : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), z ∈ Set.range i₁.1.base ∨ z ∈ Set.range i₂.1.base)
    (hred : IsReduced (pullback i₁.1 i₂.1)) (n : ℕ) (hn : Nat.card ↥(pullback i₁.1 i₂.1) = n) (hn0 : 0 < n)

    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of A))) (ModularCurve.TwoChart.modelTo A (↥K) j))
    (ε₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁) (ε₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
    (hε₁ : ε₁.1 ≫ i₁.1 = (sectionBaseChange k ε).1)

    (D : RelativePic0Designation A (ModularCurve.TwoChart.modelTo A (↥K) j))
    (hrep : Nonempty (RepresentsRelSubPic (ModularCurve.TwoChart.modelTo A (↥K) j) ε (algEquivZeroCut (ModularCurve.TwoChart.modelTo A (↥K) j) ε) D))
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase)

    (hreps : RepresentsRelSubPic (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)
      (algEquivZeroCut (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) k) (sectionBaseChange k ε)) (D.baseChange k))
    (hPk : Nonempty (hreps.poincare.L ≅ (BaseChange.ofR (ModularCurve.TwoChart.modelTo A (↥K) j) ε k
      (hrep.some.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap A k), pullback.condition⟩)).L))
    (D₁ : RelativePic0Designation k c₁) (hrep₁ : Nonempty (RepresentsRelSubPic c₁ ε₁ (algEquivZeroCut c₁ ε₁) D₁))
    (D₂ : RelativePic0Designation k c₂) (hrep₂ : Nonempty (RepresentsRelSubPic c₂ ε₂ (algEquivZeroCut c₂ ε₂) D₂))

    (ν₂ : SchemeHomOver (D.baseChange k).toBase D₂.toBase)
    (hν₂ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of k)) (a : SchemeHomOver t (D.baseChange k).toBase),
        Nonempty ((hrep₂.some.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a ν₂)).L ≅
          Scheme.Modules.rigidify (rigSection c₂ t ε₂) (pullback.snd c₂ t)
            ((Scheme.Modules.pullback (curveChange i₂.1 i₂.2 t)).obj (hreps.poincare.pullbackAlong a).L)))

    (G : ModularCurve.JOneP.NeronSpecialFibreGeom p)
    (pts : G.J0s ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) (D.baseChange k).toBase)
    (ptsI : G.JI ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₁.toBase)
    (ptsE : G.JE ≃ SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) D₂.toBase)
    (hadd : ∀ a b : G.J0s, Nonempty
      ((hreps.poincare.pullbackAlong (pts (a + b))).L ≅
        (hreps.poincare.pullbackAlong (pts a)).L ⊗ (hreps.poincare.pullbackAlong (pts b)).L))
    (haddI : ∀ a b : G.JI, Nonempty
      ((hrep₁.some.poincare.pullbackAlong (ptsI (a + b))).L ≅
        (hrep₁.some.poincare.pullbackAlong (ptsI a)).L ⊗ (hrep₁.some.poincare.pullbackAlong (ptsI b)).L))
    (haddE : ∀ a b : G.JE, Nonempty
      ((hrep₂.some.poincare.pullbackAlong (ptsE (a + b))).L ≅
        (hrep₂.some.poincare.pullbackAlong (ptsE a)).L ⊗ (hrep₂.some.poincare.pullbackAlong (ptsE b)).L))
    (hproj : ∀ x : G.J0s,
      ptsI (G.proj x).1 =
        postComp (RepresentsRelSubPic.pullbackHom i₁.1 i₁.2 hε₁ hreps hrep₁.some) (pts x) ∧
      ptsE (G.proj x).2 = postComp ν₂ (pts x))

    (w : ModularCurve.IntegralWeightOneForm k M)
    (Mdl₁ : AlgebraicCurve.CurveModel k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (e₁ : Mdl₁.C ≅ C₁)
    (he₁ : e₁.hom ≫ c₁ = Mdl₁.toBase)

    [hne₁ : Nonempty (Scheme.Opens.toScheme ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)))]
    (hgauss₁ : ∀ (a : ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j)) (x y : PowerSeries A),
      y.map (algebraMap A k) ≠ 0 →
      ((a : ↥K) : LaurentSeries L) * HahnSeries.ofPowerSeries ℤ L (y.map (algebraMap A L)) =
        HahnSeries.ofPowerSeries ℤ L (x.map (algebraMap A L)) →
      ((Mdl₁.ffEquiv.symm
          (Mdl₁.C.germToFunctionField ((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)) ⁻¹ᵁ ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤))
            (((e₁.hom ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)).app ((ModularCurve.TwoChart.ιFin A (↥K) j) ''ᵁ ⊤)).hom
              (((ModularCurve.TwoChart.ιFin A (↥K) j).appIso ⊤).inv
                ((Scheme.ΓSpecIso (CommRingCat.of ↥(ModularCurve.TwoChart.chartAlgFin A (↥K) j))).inv a))))
          : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k) =
        HahnSeries.ofPowerSeries ℤ k (x.map (algebraMap A k)) / HahnSeries.ofPowerSeries ℤ k (y.map (algebraMap A k)))

    (θ₁ : G.JI ≃+ AlgebraicCurve.Pic0 k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hθpin₁ : ∀ (g : G.JI) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) →
      ∃ Dv : Divisor.degZero (K := k) (F := ↥(ModularCurve.igusaFunctionFieldX1C k M w)),
        (Dv : Divisor k ↥(ModularCurve.igusaFunctionFieldX1C k M w)) =
          Finsupp.single (Mdl₁.pointEquivPlace ⟨x.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact x.2⟩) 1 -
            Finsupp.single (Mdl₁.pointEquivPlace ⟨ε₁.1 ≫ e₁.inv, by rw [← he₁, Category.assoc, e₁.inv_hom_id_assoc]; exact ε₁.2⟩) 1 ∧
        θ₁ g = Pic0.mk Dv)

    (frobIg : SemilinearAut k ↥(ModularCurve.igusaFunctionFieldX1C k M w))
    (hfrobIg : ∀ (x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) (n : ℤ),
      ((frobIg • x : ↥(ModularCurve.igusaFunctionFieldX1C k M w)) : LaurentSeries k).coeff n = ((x : LaurentSeries k).coeff n) ^ p)

    (F₁ : C₁ ⟶ C₁) (hF₁c : IsPullback F₁ c₁ c₁ (Spec.map (CommRingCat.ofHom (frobenius k p))))
    (hF₁X : F₁ ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k))

    (F₁k : pullback c₁ (𝟙 (Spec (CommRingCat.of k))) ⟶ pullback c₁ (𝟙 (Spec (CommRingCat.of k))))
    (hF₁k₁ : F₁k ≫ pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) = pullback.fst c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ F₁)
    (hF₁k₂ : F₁k ≫ pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) =
      pullback.snd c₁ (𝟙 (Spec (CommRingCat.of k))) ≫ Spec.map (CommRingCat.ofHom (frobenius k p))) :

    ∀ (g g' : G.JI),
      Nonempty ((hrep₁.some.poincare.pullbackAlong (ptsI g')).L ≅
        (Scheme.Modules.pullback F₁k).obj (hrep₁.some.poincare.pullbackAlong (ptsI g)).L) →
      θ₁ g' = frobIg • θ₁ g := by
  intro g g' hgg'
  classical

  let h₁ := hrep₁.some
  let φ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k) := Spec.map (CommRingCat.ofHom (frobenius k p))
  haveI : PerfectRing k p := PerfectField.toPerfectRing p
  haveI hφiso : IsIso φ := by
    haveI : IsIso (CommRingCat.ofHom (frobenius k p)) := (RingEquiv.toCommRingCatIso (frobeniusEquiv k p)).isIso_hom
    exact inferInstance
  haveI hF₁iso : IsIso F₁ := hF₁c.isIso_fst_of_isIso
  have hF₁k_eq : F₁k = pullback.map _ _ _ _ F₁ φ φ hF₁c.w.symm (by rw [Category.id_comp, Category.comp_id]) := by
    apply pullback.hom_ext
    · rw [hF₁k₁, pullback.lift_fst]
    · rw [hF₁k₂, pullback.lift_snd]
  haveI hF₁kiso : IsIso F₁k := by rw [hF₁k_eq]; infer_instance
  have hi₁' : i₁.1 ≫ pullback.snd (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = c₁ := i₁.2

  have twistPt : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
      ∃ x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁, x'.1 ≫ F₁ = φ ≫ x.1 := fun x =>
    ⟨⟨hF₁c.lift (φ ≫ x.1) (𝟙 _) (by rw [Category.assoc, x.2, Category.comp_id, Category.id_comp]), hF₁c.lift_snd _ _ _⟩,
      hF₁c.lift_fst _ _ _⟩

  have hφA : φ ≫ specMap A k = specMap A k := by
    obtain ⟨e', he'⟩ := twistPt ε₁
    have key : ∀ z : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
        z.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) = specMap A k := fun z => by
      rw [pullback.condition, reassoc_of% hi₁', reassoc_of% z.2]
    calc φ ≫ specMap A k = φ ≫ (ε₁.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) := by rw [key ε₁]
      _ = (e'.1 ≫ F₁) ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) := by rw [he', Category.assoc]
      _ = e'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) ≫ (ModularCurve.TwoChart.modelTo A (↥K) j) := by
          simp only [Category.assoc]; rw [reassoc_of% hF₁X]
      _ = specMap A k := key e'

  have hgraph : ∀ (x x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁), x'.1 ≫ F₁ = φ ≫ x.1 →
      graphOver c₁ x'.1 x'.2 ≫ F₁k = φ ≫ graphOver c₁ x.1 x.2 := by
    intro x x' hx
    apply pullback.hom_ext
    · rw [Category.assoc, hF₁k₁, ← Category.assoc, graphOver_fst, hx, Category.assoc, graphOver_fst]
    · rw [Category.assoc, hF₁k₂, ← Category.assoc, graphOver_snd, Category.assoc, graphOver_snd, Category.id_comp,
        Category.comp_id]

  have hε₁F : ε₁.1 ≫ F₁ = φ ≫ ε₁.1 := by
    haveI : Mono i₁.1 := inferInstance
    rw [← cancel_mono i₁.1]
    apply pullback.hom_ext
    · simp only [Category.assoc]
      rw [hF₁X, reassoc_of% hε₁, sectionBaseChange_coe_fst, reassoc_of% hφA]
    · simp only [Category.assoc]
      rw [hi₁', hF₁c.w, reassoc_of% ε₁.2, ε₁.2, Category.comp_id]

  have hprem : ∀ (x x' : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁), x'.1 ≫ F₁ = φ ≫ x.1 →
      x'.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = φ ≫ x.1 ≫ i₁.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) := by
    intro x x' hx
    rw [← reassoc_of% hx, hF₁X]

  have hIε : (graphOver c₁ ε₁.1 ε₁.2).ker.IsInvertible :=
    Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c₁ (𝟙 _)) (graphOver c₁ ε₁.1 ε₁.2) (graphOver_snd c₁ ε₁.1 ε₁.2)
  have AJpt : ∀ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁, ∃ a : G.JI,
      Nonempty ((h₁.poincare.pullbackAlong (ptsI a)).L ≅
        (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule) := by
    intro x
    obtain ⟨s₀, hs₀⟩ := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_schemeHomOver_poincare_pullbackAlong_iso_ofPoint_lineBundle_tensor_ofPoint_idealModule_of_isLocalRing c₁ ε₁ h₁ (𝟙 (Spec (CommRingCat.of k))) x ε₁
    exact ⟨ptsI.symm s₀, by rw [Equiv.apply_symm_apply]; exact hs₀⟩
  have h0 : Nonempty ((h₁.poincare.pullbackAlong (ptsI 0)).L ≅ 𝟙_ _) := by
    obtain ⟨a₀, ⟨ea⟩⟩ := AJpt ε₁
    obtain ⟨-, ⟨eu⟩⟩ := hIε.nonempty_module_tensor_invModule_iso
    have hz : a₀ = 0 := Ws5B13PicTwist.eq_zero_of_poincare_iso_unit h₁ ptsI haddI a₀ ⟨ea ≪≫ eu⟩
    rw [← hz]
    exact ⟨ea ≪≫ eu⟩

  let S : Set G.JI := {a | ∃ x : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₁,
    Nonempty ((h₁.poincare.pullbackAlong (ptsI a)).L ≅
      (RelEffCartierDiv.ofPoint c₁ x.1 x.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c₁ ε₁.1 ε₁.2).idealModule)}
  let T : G.JI → G.JI → Prop := fun a a' =>
    Nonempty ((h₁.poincare.pullbackAlong (ptsI a')).L ≅ (Scheme.Modules.pullback F₁k).obj (h₁.poincare.pullbackAlong (ptsI a)).L)
  let Q : G.JI → G.JI → Prop := fun a a' => θ₁ a' = frobIg • θ₁ a

  have hS : AddSubgroup.closure S = ⊤ := by
    rw [eq_top_iff]
    intro a _
    have hθa := ModularCurve.XOneP.mem_closure_pic0Mk_single_pointEquivPlace_sub_single_of_notMem_range_crossings_of_mem_range_iotaFin_igusaModel_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 w Mdl₁ e₁ he₁ (θ₁ a)
    have hmem : θ₁ a ∈ (AddSubgroup.closure S).map θ₁.toAddMonoidHom := by
      refine (AddSubgroup.closure_le _).mpr ?_ hθa
      rintro _ ⟨c, c', -, -, -, -, hdeg, rfl⟩
      obtain ⟨ac, hac⟩ := AJpt c
      obtain ⟨ac', hac'⟩ := AJpt c'
      obtain ⟨Dc, hDc, hθc⟩ := hθpin₁ ac c hac
      obtain ⟨Dc', hDc', hθc'⟩ := hθpin₁ ac' c' hac'
      refine ⟨ac - ac', AddSubgroup.sub_mem _ (AddSubgroup.subset_closure ⟨c, hac⟩) (AddSubgroup.subset_closure ⟨c', hac'⟩), ?_⟩
      show θ₁ (ac - ac') = _
      rw [map_sub, hθc, hθc']
      exact (Ws5B13PicTwist.mk_single_sub_single_eq Dc Dc' hDc hDc' hdeg).symm
    obtain ⟨b, hb, hθb⟩ := hmem
    have : b = a := θ₁.injective hθb
    rw [← this]
    exact hb
  refine Ws5B13PicTwist.induce S hS T Q ?_ ?_ ?_ ?_ ?_ g g' hgg'
  ·
    intro a a' a'' hT' hT''
    exact Ws5B13PicTwist.eq_of_poincare_iso h₁ ptsI hT' hT''
  ·
    rintro a ⟨x, ⟨ex⟩⟩
    obtain ⟨x', hx'⟩ := twistPt x
    obtain ⟨a', ⟨ex'⟩⟩ := AJpt x'
    obtain ⟨⟨eLx⟩, -⟩ := Ws5B13PicTwist.nonempty_pullback_ofPoint_iso c₁ φ F₁k x x' (hgraph x x' hx')
    obtain ⟨-, ⟨eIε⟩⟩ := Ws5B13PicTwist.nonempty_pullback_ofPoint_iso c₁ φ F₁k ε₁ ε₁ (hgraph ε₁ ε₁ hε₁F)
    refine ⟨a', ⟨ex' ≪≫ (eLx.symm ⊗ᵢ eIε.symm) ≪≫ (Functor.Monoidal.μIso (Scheme.Modules.pullback F₁k) _ _) ≪≫
      (Scheme.Modules.pullback F₁k).mapIso ex.symm⟩, ?_⟩
    obtain ⟨Dv, hDv, hθa⟩ := hθpin₁ a x ⟨ex⟩
    obtain ⟨Dv', hDv', hθa'⟩ := hθpin₁ a' x' ⟨ex'⟩
    have hfx := ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep hsm hsep hreps hPk D₁ hrep₁ D₂ hrep₂ ν₂ hν₂ G pts ptsI ptsE hadd haddI haddE hproj w Mdl₁ e₁ he₁ hgauss₁ θ₁ hθpin₁ frobIg hfrobIg x x' (hprem x x' hx')
    have hfε := ModularCurve.XOneP.pointEquivPlace_eq_frob_smul_pointEquivPlace_of_comp_eq_frobenius_comp_of_gaussReading_twoChartModel_x1_mul
      p M hM hpM L ζ hζ K hK A hAp hζA j hj k C₁ C₂ c₁ c₂ i₁ i₂ hcover hred n hn hn0 ε ε₁ ε₂ hε₁ D hrep hsm hsep hreps hPk D₁ hrep₁ D₂ hrep₂ ν₂ hν₂ G pts ptsI ptsE hadd haddI haddE hproj w Mdl₁ e₁ he₁ hgauss₁ θ₁ hθpin₁ frobIg hfrobIg ε₁ ε₁ (hprem ε₁ ε₁ hε₁F)
    show θ₁ a' = frobIg • θ₁ a
    rw [hθa, hθa']
    exact Ws5B13PicTwist.q_base frobIg hfx hfε Dv Dv' hDv hDv'
  ·
    exact ⟨0, Ws5B13PicTwist.twist_zero h₁ ptsI h0 F₁k, Ws5B13PicTwist.q_zero frobIg θ₁⟩
  ·
    intro a a' b b' hTa hQa hTb hQb
    refine ⟨Ws5B13PicTwist.twist_add h₁ ptsI haddI F₁k a a' b b' hTa hTb, ?_⟩
    exact Ws5B13PicTwist.q_add frobIg θ₁ a a' b b' hQa hQb
  ·
    intro a a' hTa hQa
    refine ⟨Ws5B13PicTwist.twist_neg h₁ ptsI h0 haddI F₁k a a' hTa, ?_⟩
    exact Ws5B13PicTwist.q_neg frobIg θ₁ a a' hQa

end S_ModularCurve_XOneP_addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_addEquiv_eq_frob_smul_of_nonempty_poincare_pullbackAlong_iso_pullback_frobeniusTwist_fst_twoChartModel_x1_mul (solution)
