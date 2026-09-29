-- Prove2me | solution 1 for ModularCurve.XOneP.exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/e21e23d2-bc5c-5f07-a3dd-cbacbb6a300d

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
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivSupportedIn
import Theorems.Thm_AlgebraicGeometry_RelPicard_isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_foldr_twist_iso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_pullbackAlong_ofPoint
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_CategoryTheory_MonoidalCategory_nonempty_iso_of_tensor_iso_tensorUnit
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_nonempty_iso_tensorUnit_of_isLocalRing
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
import Theorems.Thm_AlgebraicGeometry_IsClosedImmersion_existsUnique_comp_eq_of_range_subset_of_isReduced
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I_of_supportedIn
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_supportedIn_ofPoint
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_comap_of_isOpenImmersion
import Theorems.Thm_ModularCurve_XOneP_isReduced_pullback_modelTo_of_isAlgClosed_twoChartModel_x1_mul
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
p2m_attr_erase "instance" "AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fInf AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_ιFin AlgebraicCurve.TwoChartIntegralModel.isOpenImmersion_fFin ModularCurve.PhiGen.instNeZeroPhiGenCosetA CohCarrier.iotaDeg_range_finiteIndex CohCarrier.Gamma0Upper_finiteIndex CohCarrier.HeckeData.V_isScalarTower CohCarrier.HeckeData.opSubalgebra_isMulCommutative CohCarrier.HeckeData.mTheta_isPrime ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instIsElliptic_tateBase ModularCurve.instIsElliptic_tateLaurent ModularCurve.KatzGamma0Form.instModule ModularCurve.KatzGamma0Form.instZero ModularCurve.KatzLevelPForm.instSMul ModularCurve.KatzGamma0Form.instAdd ModularCurve.KatzLevelPForm.instAddCommGroup ModularCurve.KatzGamma0Form.instNeg ModularCurve.KatzGamma0Form.instAddCommGroup ModularCurve.KatzLevelPForm.instAdd ModularCurve.KatzLevelPForm.instSub ModularCurve.KatzLevelPForm.instNeg ModularCurve.KatzGamma0Form.instSMul ModularCurve.KatzGamma0Form.instSub"
p2m_attr_erase "instance" "ModularCurve.KatzLevelPForm.instZero ModularCurve.KatzLevelPForm.instModule KatzModularForm.instAddCommGroup KatzModularForm.instSub KatzModularForm.instZero KatzModularForm.instModule KatzModularForm.instAdd KatzModularForm.instNeg KatzModularForm.instSMul WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.Gamma0Pair.isElliptic AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "simp" "AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin_X AlgebraicCurve.TwoChartIntegralModel.coe_chartBaseChange AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf_X AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase AlgebraicCurve.TwoChartIntegralModel.ιFin_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jChartFin AlgebraicCurve.TwoChartIntegralModel.ιInf_toBase_assoc AlgebraicCurve.TwoChartIntegralModel.coe_jInvChartInf ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ CohCarrier.conjUpperMat_apply_11 CohCarrier.conjUpperMat_apply_10 CohCarrier.mem_Gamma0Upper CohCarrier.val_gamma0Units ModularCurve.JH.torsionGaloisRep_apply ModularCurve.qExpandAlgHomC_apply CohCarrier.Gen.dia.sizeOf_spec CohCarrier.Gen.U.injEq CohCarrier.Gen.T.sizeOf_spec CohCarrier.Gen.U.sizeOf_spec CohCarrier.Gen.T.injEq CohCarrier.Gen.dia.injEq CohCarrier.HeckeData.mk.sizeOf_spec CohCarrier.HeckeData.opAlgHom_X CohCarrier.HeckeData.toMLₒ_apply CohCarrier.HeckeData.mk.injEq CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₃ ModularCurve.cuspData_yP ModularCurve.qTwistAlgHom_apply ModularCurve.cuspData_yQ ModularCurve.cuspData_xP ModularCurve.cuspData_xQ ModularCurve.val_cyclZeta ModularCurve.cuspShift_one ModularCurve.cuspShift_zero ModularCurve.LevelPData.mk.sizeOf_spec ModularCurve.KatzLevelPForm.neg_toFun ModularCurve.LevelP.coe_swapW ModularCurve.KatzLevelPForm.swap_swap KatzModularForm.pullbackLevelP_toFun ModularCurve.LevelPData.swap_xQ KatzModularForm.pullbackLevelP_zero ModularCurve.LevelPData.map_yP ModularCurve.KatzLevelPForm.swap_neg ModularCurve.KatzGamma0Form.toKatzLevelPForm_sub ModularCurve.KatzLevelPForm.swap_add KatzModularForm.swap_pullbackLevelP ModularCurve.KatzGamma0Form.toKatzLevelPForm_add ModularCurve.KatzLevelPForm.swap_smul ModularCurve.LevelPData.map_yQ ModularCurve.KatzLevelPForm.mk.injEq ModularCurve.KatzLevelPForm.zero_toFun KatzModularForm.pullbackLevelP_smul ModularCurve.LevelPData.swap_xP ModularCurve.KatzGamma0Form.toKatzLevelPForm_mul ModularCurve.KatzGamma0Form.toKatzLevelPForm_neg ModularCurve.LevelPData.variableChange_xQ KatzModularForm.pullbackGamma0_toKatzLevelPForm ModularCurve.KatzLevelPForm.mk.sizeOf_spec ModularCurve.KatzLevelPForm.swap_zero ModularCurve.LevelP.coe_unipotentU ModularCurve.KatzLevelPForm.mul_toFun ModularCurve.LevelPData.variableChange_yP ModularCurve.LevelPData.mk.injEq ModularCurve.KatzLevelPForm.sub_toFun ModularCurve.LevelPData.variableChange_xP"
p2m_attr_erase "simp" "ModularCurve.KatzLevelPForm.smul_toFun ModularCurve.LevelPData.swap_yP ModularCurve.LevelPData.map_xP ModularCurve.LevelPData.swap_swap ModularCurve.LevelPData.swap_yQ ModularCurve.KatzGamma0Form.toKatzLevelPForm_zero ModularCurve.KatzGamma0Form.mk.injEq ModularCurve.KatzLevelPForm.swap_toFun KatzModularForm.pullbackLevelP_add ModularCurve.KatzGamma0Form.mk.sizeOf_spec ModularCurve.LevelPData.variableChange_yQ ModularCurve.KatzLevelPForm.swap_sub ModularCurve.KatzGamma0Form.toKatzLevelPForm_smul ModularCurve.LevelPData.map_xQ ModularCurve.KatzLevelPForm.add_toFun KatzModularForm.c₆_toFun KatzModularForm.neg_toFun KatzModularForm.mul_toFun KatzModularForm.qExpansion_neg KatzModularForm.discr_toFun KatzModularForm.qExpansion_sub KatzModularForm.qExpansion_add KatzModularForm.qExpansion_mul KatzModularForm.zero_toFun KatzModularForm.mk.injEq KatzModularForm.qExpansion_smul KatzModularForm.smul_toFun KatzModularForm.add_toFun KatzModularForm.sub_toFun KatzModularForm.c₄_toFun KatzModularForm.qExpansion_zero KatzModularForm.mk.sizeOf_spec TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff HahnSeries.ramScale_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.LevelN.coe_jGen ModularCurve.CharPReduction.coeffRed_coeff ModularCurve.CharPReduction.redLocHom_apply ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ComplexPlaceDictionaryOf.pt_ofGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.injEq ModularCurve.ComplexPlaceDictionaryOf.pt_toGamma0 ModularCurve.ComplexPlaceDictionaryOf.mk.sizeOf_spec ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing"

universe u

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

namespace L0aSKit

theorem mul_val_congr {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) {T : Scheme.{u}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)} (ht : t₁ = t₂)
    (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f) (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) :
    (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst ht
  obtain rfl : x₁ = x₂ := Subtype.ext hx
  obtain rfl : y₁ = y₂ := Subtype.ext hy
  rfl

def monoidalCancel {C : Type*} [Category C] [MonoidalCategory C] {M M' N N' : C}
    (eN : N ⊗ N' ≅ 𝟙_ C) (e : M ⊗ N ≅ M' ⊗ N) : M ≅ M' :=
  (ρ_ M).symm ≪≫ (whiskerLeftIso M eN.symm) ≪≫ (α_ M N N').symm ≪≫ (whiskerRightIso e N') ≪≫ α_ M' N N' ≪≫
    whiskerLeftIso M' eN ≪≫ ρ_ M'

section foldr
variable {X : Scheme.{u}} {ι : Type*}

abbrev twistStep (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (M : X.Modules) : X.Modules :=
  (K i ^ pos i).invModule ⊗ (K i ^ neg i).module ⊗ M

def foldrTwistCongr (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅ l.foldr (twistStep K pos neg) M'
  | [], _, _, e => e
  | (i :: l), _, _, e => whiskerLeftIso _ (whiskerLeftIso _ (foldrTwistCongr K pos neg l e))

theorem top_pow (n : ℕ) : (⊤ : X.IdealSheafData) ^ n = ⊤ := by
  rw [← Scheme.IdealSheafData.one_eq_top, one_pow]

end foldr

section top
variable {X : Scheme.{u}}

theorem subsingleton_sections_of_isEmpty {Z : Scheme.{u}} [IsEmpty Z] (V : Z.Opens) :
    Subsingleton Γ(Z, V) := by
  obtain rfl : V = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  exact CommRingCat.subsingleton_of_isTerminal (TopCat.Sheaf.isTerminalOfEmpty Z.sheaf)

theorem unitToPushforwardUnit_eq_zero_of_isEmpty {Z : Scheme.{u}} (i : Z ⟶ X) [IsEmpty Z] :
    i.unitToPushforwardUnit = 0 := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro U
  ext m
  haveI : Subsingleton Γ(Z, i ⁻¹ᵁ U.unop) := subsingleton_sections_of_isEmpty _
  exact Subsingleton.elim (α := Γ(Z, i ⁻¹ᵁ U.unop)) _ _

def topModuleIso : (⊤ : X.IdealSheafData).module ≅ 𝟙_ X.Modules :=
  (kernelIsoOfEq (unitToPushforwardUnit_eq_zero_of_isEmpty (⊤ : X.IdealSheafData).subschemeι) ≪≫
    kernelZeroIsoSource : (kernel ((⊤ : X.IdealSheafData).subschemeι.unitToPushforwardUnit) :
      SheafOfModules X.ringCatSheaf) ≅ SheafOfModules.unit X.ringCatSheaf)

theorem nonempty_topInvModuleIso : Nonempty ((⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules) :=
  MonoidalCategory.nonempty_iso_of_tensor_iso_tensorUnit (topModuleIso (X := X))
    (Scheme.IdealSheafData.isInvertible_top (X := X)).nonempty_module_tensor_invModule_iso.1 ⟨λ_ _⟩

def topInvModuleIso : (⊤ : X.IdealSheafData).invModule ≅ 𝟙_ X.Modules := nonempty_topInvModuleIso.some

def twistStepTopIso {ι : Type*} (K : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = ⊤)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ M' :=
  ((eqToIso (by rw [hi, top_pow]) : (K i ^ pos i).invModule ≅ (⊤ : X.IdealSheafData).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi, top_pow]) : (K i ^ neg i).module ≅ (⊤ : X.IdealSheafData).module) ⊗ᵢ e)) ≪≫
    (topInvModuleIso ⊗ᵢ (topModuleIso ⊗ᵢ Iso.refl M')) ≪≫ ((λ_ _) ≪≫ (λ_ _))

def twistStepCongr {ι : Type*} (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ) (i : ι) (hi : K i = K' i)
    {M M' : X.Modules} (e : M ≅ M') : twistStep K pos neg i M ≅ twistStep K' pos neg i M' :=
  ((eqToIso (by rw [hi]) : (K i ^ pos i).invModule ≅ (K' i ^ pos i).invModule) ⊗ᵢ
    ((eqToIso (by rw [hi]) : (K i ^ neg i).module ≅ (K' i ^ neg i).module) ⊗ᵢ e))

def foldrTwistSelectIso {ι : Type*} {κ : Type*} [DecidableEq κ] (c : ι → κ) (j : κ)
    (K K' : ι → X.IdealSheafData) (pos neg : ι → ℕ)
    (h₁ : ∀ i, c i = j → K i = K' i) (h₂ : ∀ i, c i ≠ j → K i = ⊤) :
    ∀ (l : List ι) {M M' : X.Modules} (_ : M ≅ M'),
      l.foldr (twistStep K pos neg) M ≅
        l.foldr (fun i N => if c i = j then twistStep K' pos neg i N else N) M'
  | [], _, _, e => e
  | (i :: l), M, M', e => by
    by_cases hc : c i = j
    · refine twistStepCongr K K' pos neg i (h₁ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_pos hc]
    · refine twistStepTopIso K pos neg i (h₂ i hc) (foldrTwistSelectIso c j K K' pos neg h₁ h₂ l e) ≪≫ eqToIso ?_
      simp only [List.foldr_cons, if_neg hc]

end top

theorem comap_ker_eq_ker_of_isPullback {X₀ X T Z : Scheme.{u}} {iX : Z ⟶ X₀} {g : Z ⟶ T} {f : X₀ ⟶ X}
    {iY : T ⟶ X} [IsClosedImmersion iY] (H : IsPullback iX g f iY) : iY.ker.comap f = iX.ker := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion, ← H.isoPullback_hom_fst,
    Scheme.Hom.ker_comp_of_isIso]

end L0aSKit

end

namespace L0aSKit

theorem isAlgEquivZero_fibreAt_ofPoint_invModule_tensor_ofPoint_module
    {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R)) [IsSeparated c]
    {A : Type u} [CommRing A] (tA : Spec (CommRingCat.of A) ⟶ Spec (CommRingCat.of R))
    (v₁ v₂ : SchemeHomOver tA c)
    (hK₁ : (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).I.IsInvertible) (hK₂ : (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).I.IsInvertible)
    (k : Type u) [Field k] [IsAlgClosed k] (sk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A))
    [IsProper (pullback.snd c (sk ≫ tA))] [SmoothOfRelativeDimension 1 (pullback.snd c (sk ≫ tA))]
    [GeometricallyIntegral (pullback.snd c (sk ≫ tA))] :
    IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj
      ((RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule)) := by
  classical
  let σ : Fin 2 → SchemeHomOver tA c := ![v₁, v₂]
  let pos : Fin 2 → ℕ := ![1, 0]
  let neg : Fin 2 → ℕ := ![0, 1]
  have hdeg : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 := by decide
  let K : Fin 2 → (pullback c tA).IdealSheafData := fun i => (RelEffCartierDiv.ofPoint c (σ i).1 (σ i).2).I
  have hKinv : ∀ i, (K i).IsInvertible := fun i => by
    fin_cases i
    · exact hK₁
    · exact hK₂
  let Lv : (pullback c tA).Modules :=
    (RelEffCartierDiv.ofPoint c v₁.1 v₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c v₂.1 v₂.2).idealModule
  have eT : (List.finRange 2).foldr (twistStep K pos neg) (𝟙_ (pullback c tA).Modules) ≅ Lv := by
    have hfr : List.finRange 2 = [(0 : Fin 2), 1] := rfl
    rw [hfr]
    show (K 0 ^ 1).invModule ⊗ ((K 0 ^ 0).module ⊗ ((K 1 ^ 0).invModule ⊗ ((K 1 ^ 1).module ⊗ 𝟙_ _))) ≅
      (K 0).invModule ⊗ (K 1).module
    refine (eqToIso (by rw [pow_one]) ⊗ᵢ ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topModuleIso) ⊗ᵢ
      ((eqToIso (by rw [pow_zero, Scheme.IdealSheafData.one_eq_top]) ≪≫ topInvModuleIso) ⊗ᵢ
        (eqToIso (by rw [pow_one]) ⊗ᵢ Iso.refl _)))) ≪≫ ?_
    exact whiskerLeftIso _ (λ_ _ ≪≫ λ_ _ ≪≫ ρ_ _)
  show IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj Lv)
  let ψ : SchemeHomOver (sk ≫ tA) tA := ⟨sk, rfl⟩
  let c' := pullback.snd c (sk ≫ tA)
  let x : Fin 2 → (Spec (CommRingCat.of k) ⟶ pullback c (sk ≫ tA)) := fun i =>
    graphOver c (ψ.1 ≫ (σ i).1) (by rw [Category.assoc, (σ i).2, ψ.2])
  have hx : ∀ i, x i ≫ c' = 𝟙 _ := fun i => graphOver_snd _ _ _
  let Φ₂ : pullback c (sk ≫ tA) ⟶ pullback c tA := baseChangeSnd c ψ
  let pr : pullback c' (𝟙 (Spec (CommRingCat.of k))) ⟶ _ := pullback.fst c' (𝟙 (Spec (CommRingCat.of k)))
  let Φ := pr ≫ Φ₂
  let K' : Fin 2 → (pullback c' (𝟙 (Spec (CommRingCat.of k)))).IdealSheafData := fun i =>
    (RelEffCartierDiv.ofPoint c' (x i) (hx i)).I
  have hab : ∀ i, (K i).comap Φ₂ = (x i).ker := fun i =>
    congrArg RelEffCartierDiv.I (RelEffCartierDiv.pullbackAlong_ofPoint c (σ i).1 (σ i).2 ψ.1 ψ.2)
  have hgeo : ∀ i, (x i).ker.comap pr = K' i := by
    intro i
    have sq : CommSq (graphOver c' (x i) (hx i)) (𝟙 _) pr (x i) := ⟨by rw [Category.id_comp]; exact graphOver_fst _ _ _⟩
    exact comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)
  have hKΦ : ∀ i, (K i).comap Φ = K' i := by
    intro i
    rw [Scheme.IdealSheafData.comap_comp, hab, hgeo i]
  have hK'inv : ∀ i, ((K i).comap Φ).IsInvertible := by
    intro i
    rw [hKΦ i]
    exact Scheme.Hom.isInvertible_ker_of_comp_eq_id (p := pullback.snd c' (𝟙 _)) (graphOver c' (x i) (hx i)) (graphOver_snd _ _ _)
  have h1inv : ∀ (Z : Scheme.{u}), (1 : Z.IdealSheafData).IsInvertible := fun Z => by
    rw [Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  let C0 : Fin 0 → (pullback c tA).IdealSheafData := fun _ => ⊤
  let a0 : Fin 0 → ℕ := fun _ => 0
  have hprod : (∏ F, C0 F ^ a0 F) = 1 := Fintype.prod_empty _
  have hprod' : (∏ F, (C0 F).comap Φ ^ a0 F) = 1 := Fintype.prod_empty _
  obtain ⟨eB⟩ : Nonempty ((∏ F, C0 F ^ a0 F).invModule ⊗ (∏ F, C0 F ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod]; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  obtain ⟨eB'⟩ : Nonempty ((∏ F, (C0 F).comap Φ ^ a0 F).invModule ⊗ (∏ F, (C0 F).comap Φ ^ a0 F).module ≅ 𝟙_ _) := by
    rw [hprod']; exact (h1inv _).nonempty_module_tensor_invModule_iso.2
  obtain ⟨e4⟩ := Scheme.Modules.nonempty_pullback_foldr_twist_iso Φ K pos neg C0 a0 a0 hKinv
    (fun F => F.elim0) hK'inv (fun F => F.elim0)
  let c0 : Fin 2 → Fin 1 := fun _ => 0
  have eN : (Scheme.Modules.pullback Φ).obj ((List.finRange 2).foldr (twistStep K pos neg) (𝟙_ _)) ≅
      (List.finRange 2).foldr (fun i N => if c0 i = 0 then twistStep K' pos neg i N else N) (𝟙_ _) :=
    (Scheme.Modules.pullback Φ).mapIso (foldrTwistCongr K pos neg _ eB.symm) ≪≫ e4 ≪≫
      foldrTwistCongr _ pos neg _ eB' ≪≫
      foldrTwistSelectIso c0 0 (fun i => (K i).comap Φ) K' pos neg (fun i _ => hKΦ i) (fun i h => absurd rfl h) _ (Iso.refl _)
  have hdeg' : (∑ i ∈ Finset.univ.filter (fun i => c0 i = 0), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
    rw [Finset.filter_true_of_mem (fun _ _ => rfl)]; exact hdeg
  have hS := AlgebraicGeometry.RelPicard.isAlgEquivZero_foldr_ofPoint_of_sum_filter_eq_zero c' x hx (fun i => c0 i = 0) pos neg hdeg'
  have hY : IsAlgEquivZero (pullback.snd c' (𝟙 _)) ((Scheme.Modules.pullback Φ).obj Lv) :=
    (hS.of_iso eN.symm).of_iso ((Scheme.Modules.pullback Φ).mapIso eT)
  have comm₁ : (pullback.fst (pullback.snd c tA) sk ≫ pullback.fst c tA) ≫ c =
      pullback.snd (pullback.snd c tA) sk ≫ sk ≫ tA := by
    simp only [Category.assoc, pullback.condition, pullback.condition_assoc]
  let g₁ : pullback (pullback.snd c tA) sk ⟶ pullback c (sk ≫ tA) := pullback.lift _ _ comm₁
  let g : pullback (pullback.snd c tA) sk ⟶ pullback c' (𝟙 (Spec (CommRingCat.of k))) :=
    pullback.lift g₁ (pullback.snd _ sk) (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
  have hg : g ≫ pullback.snd c' (𝟙 _) = fibreAt c tA sk := pullback.lift_snd _ _ _
  have hgΦ : g ≫ Φ = pullback.fst (pullback.snd c tA) sk := by
    dsimp only [g, g₁, Φ, Φ₂, pr, ψ]
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', pullback.lift_fst_assoc, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', pullback.lift_fst_assoc, pullback.lift_snd_assoc,
        pullback.condition]
  have hF := hY.pullback g hg
  exact hF.of_iso ((Scheme.Modules.pullbackComp g Φ).app _ ≪≫ (Scheme.Modules.pullbackCongr hgΦ).app _)

end L0aSKit

namespace L0aSKit

theorem smoothOfRelativeDimension_one_of_iso {S X Y : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} (e : X ≅ Y)
    (he : e.inv ≫ f = g) [SmoothOfRelativeDimension 1 f] : SmoothOfRelativeDimension 1 g := by
  rw [← he]
  exact (MorphismProperty.cancel_left_of_respectsIso (@SmoothOfRelativeDimension 1) e.inv f).mpr ‹_›
end L0aSKit

set_option maxHeartbeats 16000000 in
set_option synthInstance.maxHeartbeats 1600000 in

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

    [IsProper (ModularCurve.TwoChart.modelTo A (↥K) j)]

    [Algebra A (AlgebraicClosure ℚ)] [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower A L (AlgebraicClosure ℚ)]

    [Flat (ModularCurve.TwoChart.modelTo A (↥K) j)]
    (hsmL : SmoothOfRelativeDimension 1 (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))
    (hgiL : GeometricallyIntegral (baseChange A (ModularCurve.TwoChart.modelTo A (↥K) j) L))

    (U : (ModularCurve.TwoChartModel A (↥K) j).Opens) [SmoothOfRelativeDimension 1 (U.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j))]
    (hUmax : ∀ W : (ModularCurve.TwoChartModel A (↥K) j).Opens, SmoothOfRelativeDimension 1 (W.ι ≫ (ModularCurve.TwoChart.modelTo A (↥K) j)) → W ≤ U)

    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (ρ : A →+* ↥Pl) (hρ : Pl.subtype.comp ρ = algebraMap A (AlgebraicClosure ℚ))
    (πk : ↥Pl →+* k) (hAlgk : algebraMap A k = πk.comp ρ)

    (hπk : Function.Surjective πk) :
    ∀ (ξ₁ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j)) (ξ₂ : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (ModularCurve.TwoChart.modelTo A (↥K) j))
      (d₁ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂) (d₂ : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂),
      Set.range ξ₁.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → Set.range ξ₂.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      d₁.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₁.1 →
      (d₁.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      d₂.1 ≫ i₂.1 ≫ pullback.fst (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k) = Spec.map (CommRingCat.ofHom πk) ≫ ξ₂.1 →
      (d₂.1 ≫ i₂.1).base (IsLocalRing.closedPoint k) ∉ Set.range i₁.1.base →
      ∃ s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase,
        Nonempty ((hrep.some.poincare.pullbackAlong s).L ≅
          (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₁.1 ξ₁.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint (ModularCurve.TwoChart.modelTo A (↥K) j) ξ₂.1 ξ₂.2).idealModule) := by
  intro ξ₁ ξ₂ d₁ d₂ hU₁ hU₂ hsp₁ hoff₁ hsp₂ hoff₂
  classical

  let hD := hrep.some
  let c : ModularCurve.TwoChartModel A (↥K) j ⟶ Spec (CommRingCat.of A) := (ModularCurve.TwoChart.modelTo A (↥K) j)
  let tA : Spec (CommRingCat.of ↥Pl) ⟶ Spec (CommRingCat.of A) := Spec.map (CommRingCat.ofHom ρ)
  let rk : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of ↥Pl) := Spec.map (CommRingCat.ofHom πk)
  let tκ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of A) := specMap A k
  have hbase : tκ = rk ≫ tA := by
    show Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← hAlgk]
  let x : pullback c tκ ⟶ Spec (CommRingCat.of k) := pullback.snd c tκ
  let ψred : SchemeHomOver tκ tA := ⟨rk, hbase.symm⟩
  let B : pullback c tκ ⟶ pullback c tA := baseChangeSnd c ψred
  let Θ : pullback x (𝟙 _) ⟶ pullback c tκ := pullback.fst x (𝟙 _)

  have hKi : ∀ {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of A)} (u : SchemeHomOver t c),
      Set.range u.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) → (RelEffCartierDiv.ofPoint c u.1 u.2).I.IsInvertible :=
    fun u hu => RelEffCartierDiv.isInvertible_I_of_supportedIn U _
      (RelEffCartierDiv.supportedIn_ofPoint u.1 u.2 U (fun t => hu ⟨t, rfl⟩))
  let Lu : (pullback c tA).Modules :=
    (RelEffCartierDiv.ofPoint c ξ₁.1 ξ₁.2).lineBundle ⊗ (RelEffCartierDiv.ofPoint c ξ₂.1 ξ₂.2).idealModule
  have hLu : Scheme.Modules.IsInvertible Lu := (hKi ξ₁ hU₁).isInvertible_invModule.tensor (hKi ξ₂ hU₂).isInvertible_module
  let Mr : RigidifiedLineBundle c ε tA :=
    { L := Lu
      isInvertible := hLu
      rigidified := (hLu.pullback (rigSection c tA ε)).nonempty_iso_tensorUnit_of_isLocalRing }

  have hXred : IsReduced (pullback c tκ) :=
    ModularCurve.XOneP.isReduced_pullback_modelTo_of_isAlgClosed_twoChartModel_x1_mul p M hM hpM L ζ hζ K hK A hAp hζA j hj k tκ

  have hεc : (tκ ≫ ε.1) ≫ c = 𝟙 _ ≫ tκ := by
    rw [Category.assoc, ε.2, Category.comp_id, Category.id_comp]
  let εκ : SchemeHomOver (𝟙 _) x := ⟨pullback.lift _ _ hεc, pullback.lift_snd _ _ _⟩

  have hcover' : ∀ w : ↥(pullback (ModularCurve.TwoChart.modelTo A (↥K) j) (specMap A k)), w ∈ Set.range i₂.1.base ∨ w ∈ Set.range i₁.1.base :=
    fun w => (hcover w).symm
  haveI : IsReduced (pullback i₁.1 i₂.1) := hred
  have hred' : IsReduced (pullback i₂.1 i₁.1) := isReduced_of_isOpenImmersion (pullbackSymmetry i₂.1 i₁.1).hom
  have hn' : Nat.card ↥(pullback i₂.1 i₁.1) = n := by
    rw [← hn]; exact Nat.card_congr (Scheme.homeoOfIso (pullbackSymmetry i₂.1 i₁.1)).toEquiv
  obtain ⟨Mκ, ⟨eM⟩, hMκ⟩ :=
    AlgebraicGeometry.RelPicard.exists_rigidifiedLineBundle_ofPoint_tensor_ofPoint_fibrewiseAlgEquivZero_of_twoGluedSmoothCurves
      (k := k) x hXred c₂ c₁ i₂ i₁ hcover' hred' n hn' hn0 εκ d₁ d₂ hoff₁ hoff₂

  have hū : ∀ (u : SchemeHomOver tA c), (rk ≫ u.1) ≫ c = tκ := fun u => by
    rw [Category.assoc, u.2]; exact hbase.symm
  have hūsm : ∀ (u : SchemeHomOver tA c), Set.range u.1.base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) →
      Set.range (rk ≫ u.1).base ⊆ (U : Set (ModularCurve.TwoChartModel A (↥K) j)) := by
    rintro u hu _ ⟨z, rfl⟩
    exact hu ⟨rk.base z, rfl⟩
  have hgr : ∀ (u : SchemeHomOver tA c) (d : SchemeHomOver (𝟙 (Spec (CommRingCat.of k))) c₂)
      (_ : d.1 ≫ i₂.1 ≫ pullback.fst c tκ = rk ≫ u.1),
      graphOver c (rk ≫ u.1) (hū u) = d.1 ≫ i₂.1 := by
    intro u d hdf
    apply pullback.hom_ext
    · rw [graphOver_fst, Category.assoc, hdf]
    · rw [graphOver_snd, Category.assoc]
      show 𝟙 _ = d.1 ≫ i₂.1 ≫ baseChange A c k
      rw [i₂.2, d.2]
  have hgr₁ := hgr ξ₁ d₁ hsp₁
  have hgr₂ := hgr ξ₂ d₂ hsp₂
  have hd₁ : (d₁.1 ≫ i₂.1) ≫ x = 𝟙 _ := by rw [Category.assoc]; show d₁.1 ≫ i₂.1 ≫ baseChange A c k = 𝟙 _; rw [i₂.2, d₁.2]
  have hd₂ : (d₂.1 ≫ i₂.1) ≫ x = 𝟙 _ := by rw [Category.assoc]; show d₂.1 ≫ i₂.1 ≫ baseChange A c k = 𝟙 _; rw [i₂.2, d₂.2]
  have hI₁ : (d₁.1 ≫ i₂.1).ker.IsInvertible := by
    rw [← hgr₁]; exact hKi ⟨rk ≫ ξ₁.1, hū ξ₁⟩ (hūsm ξ₁ hU₁)
  have hI₂ : (d₂.1 ≫ i₂.1).ker.IsInvertible := by
    rw [← hgr₂]; exact hKi ⟨rk ≫ ξ₂.1, hū ξ₂⟩ (hūsm ξ₂ hU₂)
  haveI : IsClosedImmersion (d₁.1 ≫ i₂.1) := by rw [← hgr₁]; infer_instance
  haveI : IsClosedImmersion (d₂.1 ≫ i₂.1) := by rw [← hgr₂]; infer_instance
  let p₁ : Spec (CommRingCat.of k) ⟶ pullback x (𝟙 _) := graphOver x (d₁.1 ≫ i₂.1) hd₁
  let p₂ : Spec (CommRingCat.of k) ⟶ pullback x (𝟙 _) := graphOver x (d₂.1 ≫ i₂.1) hd₂
  have hp₁ : p₁ ≫ Θ = d₁.1 ≫ i₂.1 := graphOver_fst _ _ _
  have hp₂ : p₂ ≫ Θ = d₂.1 ≫ i₂.1 := graphOver_fst _ _ _
  have hI₁' : p₁.ker.IsInvertible := by
    have sq : CommSq p₁ (𝟙 _) Θ (d₁.1 ≫ i₂.1) := ⟨by rw [Category.id_comp]; exact hp₁⟩
    rw [← L0aSKit.comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)]
    exact hI₁.comap_of_isOpenImmersion Θ
  have hI₂' : p₂.ker.IsInvertible := by
    have sq : CommSq p₂ (𝟙 _) Θ (d₂.1 ≫ i₂.1) := ⟨by rw [Category.id_comp]; exact hp₂⟩
    rw [← L0aSKit.comap_ker_eq_ker_of_isPullback (IsPullback.of_vert_isIso sq)]
    exact hI₂.comap_of_isOpenImmersion Θ

  have bridge : Nonempty ((Scheme.Modules.pullback (Θ ≫ B)).obj Lu ≅
      (RelEffCartierDiv.ofPoint x (d₁.1 ≫ i₂.1) hd₁).lineBundle ⊗
        (RelEffCartierDiv.ofPoint x (d₂.1 ≫ i₂.1) hd₂).idealModule) := by
    obtain ⟨⟨e₁⟩, -⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      A c U ξ₁ hU₁ ψred (hū ξ₁)
    obtain ⟨-, ⟨e₂⟩⟩ := AlgebraicGeometry.RelEffCartierDiv.nonempty_pullback_ofPoint_lineBundle_iso_and_idealModule_iso_of_range_subset
      A c U ξ₂ hU₂ ψred (hū ξ₂)
    obtain ⟨⟨j₁⟩, -⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Θ (d₁.1 ≫ i₂.1) p₁ hp₁ hI₁ hI₁' 1
    obtain ⟨-, ⟨j₂⟩⟩ := Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso Θ (d₂.1 ≫ i₂.1) p₂ hp₂ hI₂ hI₂' 1
    have j₁' : (Scheme.Modules.pullback Θ).obj (RelEffCartierDiv.ofPoint c (rk ≫ ξ₁.1) (hū ξ₁)).lineBundle ≅
        (RelEffCartierDiv.ofPoint x (d₁.1 ≫ i₂.1) hd₁).lineBundle :=
      (Scheme.Modules.pullback Θ).mapIso (eqToIso (by
          show (graphOver c (rk ≫ ξ₁.1) (hū ξ₁)).ker.invModule = _
          rw [hgr₁, pow_one])) ≪≫ j₁ ≪≫ eqToIso (by rw [pow_one]; rfl)
    have j₂' : (Scheme.Modules.pullback Θ).obj (RelEffCartierDiv.ofPoint c (rk ≫ ξ₂.1) (hū ξ₂)).idealModule ≅
        (RelEffCartierDiv.ofPoint x (d₂.1 ≫ i₂.1) hd₂).idealModule :=
      (Scheme.Modules.pullback Θ).mapIso (eqToIso (by
          show (graphOver c (rk ≫ ξ₂.1) (hū ξ₂)).ker.module = _
          rw [hgr₂, pow_one])) ≪≫ j₂ ≪≫ eqToIso (by rw [pow_one]; rfl)
    exact ⟨((Scheme.Modules.pullbackComp Θ B).app Lu).symm ≪≫
      (Scheme.Modules.pullback Θ).mapIso (Scheme.Modules.pullbackTensorObjIso B _ _ ≪≫ (e₁ ⊗ᵢ e₂)) ≪≫
      Scheme.Modules.pullbackTensorObjIso Θ _ _ ≪≫ (j₁' ⊗ᵢ j₂')⟩

  have hAEZ : FibrewiseAlgEquivZero Mr := by
    intro k' _ _ sk
    show IsAlgEquivZero (fibreAt c tA sk) ((Scheme.Modules.pullback (pullback.fst (pullback.snd c tA) sk)).obj Lu)
    by_cases hpt : IsLocalRing.closedPoint ↥Pl ∈ Set.range sk.base
    ·
      obtain ⟨φ, hφ⟩ : ∃ φ : k →+* k', sk = Spec.map (CommRingCat.ofHom φ) ≫ rk := by
        obtain ⟨ψ, hψ⟩ : ∃ g, Spec.map g = sk := ⟨Spec.preimage sk, Spec.map_preimage sk⟩
        subst hψ
        obtain ⟨z, hz⟩ := hpt
        have hz' : z = IsLocalRing.closedPoint k' := Subsingleton.elim _ _
        subst hz'
        haveI : IsLocalHom ψ.hom := by
          rw [IsLocalRing.isLocalHom_iff_comap_closedPoint]
          exact hz
        have hle : RingHom.ker πk ≤ RingHom.ker ψ.hom := by
          intro a ha
          rw [RingHom.mem_ker] at ha ⊢
          by_contra hne
          have hu : IsUnit (ψ.hom a) := (Ne.isUnit hne)
          have := (isUnit_map_iff ψ.hom a).mp hu
          exact (this.map πk).ne_zero ha
        refine ⟨RingHom.liftOfSurjective πk hπk ⟨ψ.hom, hle⟩, ?_⟩
        rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, RingHom.liftOfSurjective_comp]
        rfl

      have comm₂ : (pullback.fst (pullback.snd c tA) sk ≫ pullback.fst c tA) ≫ c =
          (pullback.snd (pullback.snd c tA) sk ≫ Spec.map (CommRingCat.ofHom φ)) ≫ tκ := by
        rw [hbase]; simp only [Category.assoc, pullback.condition, pullback.condition_assoc, hφ]
      let g₂' : pullback (pullback.snd c tA) sk ⟶ pullback c tκ := pullback.lift _ _ comm₂
      let g₁' : pullback (pullback.snd c tA) sk ⟶ pullback x (𝟙 _) :=
        pullback.lift g₂' (pullback.snd _ sk ≫ Spec.map (CommRingCat.ofHom φ)) (by rw [Category.comp_id]; exact pullback.lift_snd _ _ _)
      let g : pullback (pullback.snd c tA) sk ⟶ pullback (pullback.snd x (𝟙 _)) (Spec.map (CommRingCat.ofHom φ)) :=
        pullback.lift g₁' (pullback.snd _ sk) (pullback.lift_snd _ _ _)
      have hg : g ≫ pullback.snd _ _ = fibreAt c tA sk := pullback.lift_snd _ _ _
      have hgΘB : (g ≫ pullback.fst _ _) ≫ Θ ≫ B = pullback.fst (pullback.snd c tA) sk := by
        have h1 : (g ≫ pullback.fst _ _) ≫ Θ = g₂' := by
          rw [Category.assoc]
          show g ≫ pullback.fst _ _ ≫ pullback.fst x (𝟙 _) = g₂'
          rw [pullback.lift_fst_assoc, pullback.lift_fst]
        rw [← Category.assoc, h1]
        apply pullback.hom_ext
        · rw [Category.assoc, BaseChange.baseChangeSnd_fst', pullback.lift_fst]
        · rw [Category.assoc, BaseChange.baseChangeSnd_snd', pullback.lift_snd_assoc, pullback.condition, hφ]
          simp only [Category.assoc]
          rfl
      have h2 := (hMκ k' (Spec.map (CommRingCat.ofHom φ))).pullback g hg
      obtain ⟨br⟩ := bridge
      refine h2.of_iso ?_
      exact (Scheme.Modules.pullbackComp g _).app _ ≪≫
        (Scheme.Modules.pullback (g ≫ pullback.fst _ _)).mapIso (eM ≪≫ br.symm) ≪≫
        (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackCongr hgΘB).app _
    ·
      obtain ⟨ψ, rfl⟩ : ∃ g, Spec.map g = sk := ⟨Spec.preimage sk, Spec.map_preimage sk⟩
      have hker : RingHom.ker ψ.hom ≠ IsLocalRing.maximalIdeal ↥Pl := by
        intro hkm
        apply hpt
        haveI : IsLocalHom ψ.hom := by
          refine ⟨fun a ha => ?_⟩
          by_contra hna
          have hm : a ∈ IsLocalRing.maximalIdeal ↥Pl := hna
          rw [← hkm, RingHom.mem_ker] at hm
          exact ha.ne_zero hm
        exact ⟨IsLocalRing.closedPoint k', IsLocalRing.comap_closedPoint ψ.hom⟩
      haveI : (RingHom.ker ψ.hom).IsPrime := RingHom.ker_isPrime _
      have hbot : RingHom.ker ψ.hom = ⊥ :=
        ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (Fact.out) Pl hPl _ hker
      have hinj : Function.Injective ψ.hom := (RingHom.injective_iff_ker_eq_bot _).mpr hbot
      let φ : AlgebraicClosure ℚ →+* k' := IsFractionRing.lift hinj
      have hφ : φ.comp Pl.subtype = ψ.hom := by
        ext a
        exact IsFractionRing.lift_algebraMap hinj a

      let sL : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of A) := specMap A L
      let sLk : Spec (CommRingCat.of k') ⟶ Spec (CommRingCat.of L) :=
        Spec.map (CommRingCat.ofHom (φ.comp (algebraMap L (AlgebraicClosure ℚ))))
      have hsk : Spec.map ψ ≫ tA = sLk ≫ sL := by
        show Spec.map ψ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        rw [CommRingCat.hom_comp, CommRingCat.hom_comp, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom, CommRingCat.hom_ofHom,
          ← hφ, RingHom.comp_assoc, hρ, IsScalarTower.algebraMap_eq A L (AlgebraicClosure ℚ), ← RingHom.comp_assoc]
      let e : pullback c (Spec.map ψ ≫ tA) ≅ pullback (pullback.snd c sL) sLk :=
        pullback.congrHom rfl hsk ≪≫ (pullbackLeftPullbackSndIso c sL sLk).symm
      have he : e.hom ≫ pullback.snd (pullback.snd c sL) sLk = pullback.snd c (Spec.map ψ ≫ tA) := by
        rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, ← pullbackLeftPullbackSndIso_hom_snd c sL sLk, Iso.inv_hom_id_assoc,
          pullback.congrHom_hom, pullback.lift_snd, Category.comp_id]
      haveI : SmoothOfRelativeDimension 1 (pullback.snd c sL) := hsmL
      haveI : GeometricallyIntegral (pullback.snd c sL) := hgiL
      haveI : IsProper (pullback.snd c (Spec.map ψ ≫ tA)) := by rw [← he]; infer_instance
      haveI : SmoothOfRelativeDimension 1 (pullback.snd c (Spec.map ψ ≫ tA)) :=
        L0aSKit.smoothOfRelativeDimension_one_of_iso e.symm he
      haveI : GeometricallyIntegral (pullback.snd c (Spec.map ψ ≫ tA)) := by
        rw [← he]
        exact (MorphismProperty.cancel_left_of_respectsIso @GeometricallyIntegral e.hom _).mpr inferInstance
      exact L0aSKit.isAlgEquivZero_fibreAt_ofPoint_invModule_tensor_ofPoint_module c tA ξ₁ ξ₂ (hKi ξ₁ hU₁) (hKi ξ₂ hU₂) k' (Spec.map ψ)

  obtain ⟨s, hs, -⟩ := hD.univ tA Mr hAEZ
  exact ⟨s, hs⟩

end S_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul
end P2MW
export P2MW.S_ModularCurve_XOneP_exists_schemeHomOver_poincare_iso_ofPoint_tensor_idealModule_of_reduction_snd_valuationSubring_twoChartModel_x1_mul (solution)
