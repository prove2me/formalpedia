-- Prove2me | solution 1 for ModularCurve.DRResolvedModelPackage.exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.339302+00:00
-- url     : https://prove2.me/submissions/5b4d7a45-3aeb-5cf4-87ef-5b3a7d65ed2a

import Mathlib
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_ModularCurve_DRResolvedModelPackageV4
import Definitions.Def_MvPolynomial_CrossingResolutionScheme
import Definitions.Def_ModularCurve_DRResolvedModelCharts
import Definitions.Def_ModularCurve_X0MqResolvedTable
import Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import Theorems.Thm_ModularCurve_DRModelPackage_locallyOfFinitePresentation_toBase
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id_of_mem_opens
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_not_ringKrullDim_stalk_crossingPt_le_one
import Theorems.Thm_ModularCurve_DRResolvedModelPackage_DRResolvedModelCharts_exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_exists_isInvertible_and_pullback_iso_of_isIso_app
import Theorems.Thm_AlgebraicGeometry_Scheme_bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map
import Theorems.Thm_ModularCurve_DRModelPackage_isIntegrallyClosed_stalk_pullback_toBase
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_specialFibrePackage_of_chartTable
import Theorems.Thm_MvPolynomial_CrossingQuotient_Resolution_exists_open_pullback_twist_iso_tensorUnit_of_degree_eq_zero
import Theorems.Thm_ModularCurve_DRModelPackage_mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRResolvedModelPackage_exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial SheafOfModules.isIso_ihomModelToIhom WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicGeometry.Scheme.branchIdeal_isPrime ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler"
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions"
p2m_attr_erase "instance" "instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.HpoolLevelRing.instCommRingAfin ModularCurve.HpoolLevelRing.instCommRingLevelRing ModularCurve.HpoolLevelRing.instSMulAway ModularCurve.HpoolLevelRing.instModuleAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraAfinAfinAway ModularCurve.HpoolLevelRing.instModuleAway ModularCurve.HpoolLevelRing.instModuleLevelRing ModularCurve.HpoolLevelRing.instCommRingAfinAway ModularCurve.HpoolLevelRing.instModuleAfinSelf ModularCurve.HpoolLevelRing.instSMulAfinAfinAway ModularCurve.HpoolLevelRing.instAlgebraLevelRing ModularCurve.HpoolLevelRing.instAlgebraIntAfinAway ModularCurve.HpoolLevelRing.instIsDomainAfin ModularCurve.HpoolLevelRing.instAlgebraIntAfin ModularCurve.HpoolLevelRing.instSMulLevelRing ModularCurve.HpoolLevelRing.algebraAway ModularCurve.HpoolLevelRing.instAlgebraAfinAwayLevelRing ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.jqNModC_one ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong"
p2m_attr_erase "simp" "ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.CharPReduction.coeffRed_coeff"
p2m_attr_erase "simp" "ModularCurve.CharPReduction.redLocHom_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.PlaceSpecialization.mk.injEq ModularCurve.PlaceSpecialization.mk.sizeOf_spec ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd"
p2m_attr_erase "simp" "ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit"

set_option autoImplicit false

universe u v

p2m_open "CategoryTheory CategoryTheory.Limits AlgebraicGeometry P2MW.S_ModularCurve_DRResolvedModelPackage_exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero.AlgebraicGeometry TopologicalSpace CategoryTheory.MonoidalCategory MvPolynomial MvPolynomial.CrossingQuotient ModularCurve~nodeEquiv P2MW.S_ModularCurve_DRResolvedModelPackage_exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero.ModularCurve NeronModelInfra"

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.IdealSheafData.one_eq_top Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom morphismRestrictRestrict Scheme.Hom.image_preimage_eq_opensRange_inf IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.Modules Scheme.Opens morphismRestrictEq Scheme.IdealSheafData.ofIdealTop Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "ringCatSheaf IdealSheafData.one_eq_top Modules.pullback Hom Γ Hom.image_preimage_eq_opensRange_inf basicOpen Modules Opens residue IdealSheafData.ofIdealTop Opens.opensRange_ι IdealSheafData ΓSpecIso Modules.IsInvertible IdealSheafData.isInvertible_top Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "pullback presheaf Hom IsInvertible tensor IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app" namespace IsInvertible p2m_export "AlgebraicGeometry.Scheme.Modules.IsInvertible" "pullback tensor exists_isInvertible_and_pullback_iso_of_isIso_app" end AlgebraicGeometry.Scheme.Modules.IsInvertible
p2m_open_scoped "AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Modules AlgebraicGeometry.Scheme.Modules.IsInvertible" in

theorem AlgebraicGeometry.Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_forall_exists_trivial_nhd
    {X Y : Scheme.{u}} (f : Y ⟶ X) [IsIntegral Y] [IsLocallyNoetherian X]
    (U : X.Opens) (hU : IsIso (f ∣_ U))
    {N : Type v} (x : N → X) (hcover : ∀ y : X, y ∉ U → ∃ n, y = x n)
    (W : N → X.Opens) (hxW : ∀ n, x n ∈ W n) (hWx : ∀ n m, m ≠ n → x m ∉ W n)
    (hnorm : ∀ n (y : X), y ∈ W n → IsDomain (X.presheaf.stalk y) ∧ IsIntegrallyClosed (X.presheaf.stalk y))
    (hdim : ∀ n, ¬ ringKrullDim (X.presheaf.stalk (x n)) ≤ 1)
    (L : Y.Modules) (hL : Scheme.Modules.IsInvertible L)
    (hloc : ∀ n, ∃ V : X.Opens, x n ∈ V ∧ V ≤ W n ∧
      Nonempty ((Scheme.Modules.pullback (f ⁻¹ᵁ V).ι).obj L ≅ SheafOfModules.unit (f ⁻¹ᵁ V).toScheme.ringCatSheaf)) :
    ∃ M : X.Modules, Scheme.Modules.IsInvertible M ∧ Nonempty ((Scheme.Modules.pullback f).obj M ≅ L) := by
  choose V hxV hVW hτ using hloc

  have hH : ∀ n (y : X), y ∈ V n → ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U := by
    intro n y hy hd
    by_contra hyU
    obtain ⟨m, rfl⟩ := hcover y hyU
    by_cases hmn : m = n
    · subst hmn; exact hdim m hd
    · exact hWx n m hmn (hVW n hy)
  have hO : ∀ n (V' : X.Opens), V' ≤ V n → IsIso (f.app V') := fun n V' hV' =>
    Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map f U hU V'
      (Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk V' U
        (fun y hy => hnorm n y (hVW n (hV' hy))) (fun y hy hd => hH n y (hV' hy) hd))
  have hcov : U ⊔ ⨆ n, V n = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    rw [Opens.mem_sup, Opens.mem_iSup]
    by_cases hy : y ∈ U
    · exact Or.inl hy
    · obtain ⟨n, rfl⟩ := hcover y hy
      exact Or.inr ⟨n, hxV n⟩
  exact Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app f U hU V hcov hO L hL hτ

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "IsLocallyNoetherian Scheme.IdealSheafData.one_eq_top Scheme.Modules.pullback LocallyOfFiniteType.isLocallyNoetherian Scheme.Hom morphismRestrictRestrict Scheme.Hom.image_preimage_eq_opensRange_inf IsZariskiLocalAtTarget LocallyOfFiniteType Spec IsIntegral Spec.map Scheme IsZariskiLocalAtTarget.of_iSup_eq_top Scheme.Modules Scheme.Opens morphismRestrictEq Scheme.IdealSheafData.ofIdealTop Scheme.Opens.opensRange_ι Scheme.IdealSheafData Scheme.ΓSpecIso Scheme.Modules.IsInvertible Scheme.IdealSheafData.isInvertible_top Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_isIso_app Scheme.bijective_presheaf_map_inf_of_isIntegrallyClosed_stalk Scheme.Hom.isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map" end AlgebraicGeometry
p2m_open_scoped "AlgebraicGeometry" in

theorem AlgebraicGeometry.isIso_morphismRestrict_sup {X Y : Scheme.{u}} (f : Y ⟶ X) (A B : X.Opens)
    (hA : IsIso (f ∣_ A)) (hB : IsIso (f ∣_ B)) : IsIso (f ∣_ (A ⊔ B)) := by
  let W : X.Opens := A ⊔ B
  let V : Bool → W.toScheme.Opens := fun b => cond b (W.ι ⁻¹ᵁ A) (W.ι ⁻¹ᵁ B)
  have hcov : iSup V = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨y, hy⟩ -
    rw [Opens.mem_iSup]
    rcases Opens.mem_sup.mp hy with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have himg : ∀ b, W.ι ''ᵁ V b = cond b A B := by
    intro b
    cases b <;>
    · simp only [V, cond]
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_eq_right]
      first | exact le_sup_left | exact le_sup_right
  have key : ∀ b, (MorphismProperty.isomorphisms Scheme) ((f ∣_ W) ∣_ V b) := by
    intro b
    refine ((MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
      (morphismRestrictRestrict f W (V b) ≪≫ morphismRestrictEq f (himg b))).mpr ?_
    cases b
    · exact hB
    · exact hA
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme) V hcov key

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "DRModel.baseChangeMap DRResolvedModelPackage DRModel DRModel.toBase DRModelPackage X0MqComponents x0MqResolvedTable DRResolvedModelPackage.DRResolvedModelCharts DRModelPackage.locallyOfFinitePresentation_toBase DRResolvedModelPackage.DRResolvedModelCharts.not_ringKrullDim_stalk_crossingPt_le_one DRResolvedModelPackage.DRResolvedModelCharts.exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero DRModelPackage.isIntegrallyClosed_stalk_pullback_toBase DRModelPackage.mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase"
p2m_open "ModularCurve~nodeEquiv"

variable {p : ℕ} [Fact p.Prime]

namespace DRModelPackage p2m_export "ModularCurve.DRModelPackage" "smoothLocus normal compZero compInf w locallyOfFinitePresentation_toBase isIntegrallyClosed_stalk_pullback_toBase mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase" end DRModelPackage
p2m_open_scoped "ModularCurve.DRModelPackage" in

abbrev DRModelPackage.XO (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] : Scheme.{0} :=
  pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))

namespace DRModelPackage
p2m_open_scoped "ModularCurve.DRModelPackage" in

private def _root_.ModularCurve.DRModelPackage.isoLocus (𝔛 : DRModelPackage p) (O : Type) [CommRing O] : (DRModelPackage.XO p O).Opens :=
  (pullback.fst (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ 𝔛.smoothLocus) ⊔
    (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) ⁻¹ᵁ
      (PrimeSpectrum.basicOpen ((p : ℕ) : O) : (Spec (CommRingCat.of O)).Opens))

end DRModelPackage
p2m_export "ModularCurve" "DRModelPackage.isoLocus"
namespace DRResolvedModelPackage
p2m_export "ModularCurve.DRResolvedModelPackage" "toBase toDR_iso_smoothLocus node comp_isInvertible width Y nodeEquiv toDR_iso_generic isLocallyNoetherian smoothOffEdges comp toDR crossingPt DRResolvedModelCharts DRResolvedModelCharts.not_ringKrullDim_stalk_crossingPt_le_one DRResolvedModelCharts.exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero"
p2m_open "ModularCurve.DRResolvedModelPackage"

p2m_open "MvPolynomial MvPolynomial.CrossingQuotient CategoryTheory.MonoidalCategory"

variable {𝔛 : DRModelPackage p} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
  (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)

omit [IsDomain O] [IsDiscreteValuationRing O] in
private theorem _root_.ModularCurve.DRResolvedModelPackage.isIso_toDR_restrict_isoLocus : IsIso (𝔛reg.toDR ∣_ 𝔛.isoLocus O) :=
  AlgebraicGeometry.isIso_morphismRestrict_sup _ _ _ 𝔛reg.toDR_iso_smoothLocus 𝔛reg.toDR_iso_generic

p2m_export "ModularCurve.DRResolvedModelPackage" "isIso_toDR_restrict_isoLocus"

private abbrev _root_.ModularCurve.DRResolvedModelPackage.ChartWitness (ϖ : O) (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ϖ e).IdealSheafData) :=
  𝔛reg.DRResolvedModelCharts ϖ Fc

p2m_export "ModularCurve.DRResolvedModelPackage" "ChartWitness"

private noncomputable def _root_.ModularCurve.DRResolvedModelPackage.divisorialSheaf {m : ℕ} (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (pos neg : Fin m → ℕ) (aplus aminus : X0MqComponents 𝔛reg.width → ℕ) : 𝔛reg.Y.Modules :=
  (List.finRange m).foldr (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
    ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module)

p2m_export "ModularCurve.DRResolvedModelPackage" "divisorialSheaf"

theorem isInvertible_prod_pow' {X : Scheme.{0}} {ι : Type*} [Fintype ι] [DecidableEq ι] (I : ι → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (n : ι → ℕ) : (∏ i, I i ^ n i).IsInvertible := by
  classical
  refine Finset.induction_on (Finset.univ : Finset ι) ?_ ?_
  · rw [Finset.prod_empty, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_top
  · intro i s hi ih
    rw [Finset.prod_insert hi]
    exact ((hI i).pow (n i)).mul ih

theorem isInvertible_foldr' {X : Scheme.{0}} {m : ℕ} (A B : Fin m → X.Modules)
    (hA : ∀ j, Scheme.Modules.IsInvertible (A j)) (hB : ∀ j, Scheme.Modules.IsInvertible (B j))
    (V : X.Modules) (hV : Scheme.Modules.IsInvertible V) (l : List (Fin m)) :
    Scheme.Modules.IsInvertible (l.foldr (fun j N => A j ⊗ B j ⊗ N) V) := by
  induction l with
  | nil => exact hV
  | cons j l ih => exact (hA j).tensor ((hB j).tensor ih)

private theorem _root_.ModularCurve.DRResolvedModelPackage.isInvertible_divisorialSheaf {m : ℕ}
    (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase)
    (pos neg : Fin m → ℕ) (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ) :
    Scheme.Modules.IsInvertible (𝔛reg.divisorialSheaf σ pos neg aplus aminus) := by
  classical
  have hker : ∀ j, ((σ j).1).ker.IsInvertible := fun j =>
    AlgebraicGeometry.Scheme.Hom.isInvertible_ker_of_comp_eq_id_of_mem_opens 𝔛reg.toBase 𝔛reg.smoothOffEdges
      (σ j).1 (σ j).2 (hv j).1
  unfold divisorialSheaf
  refine isInvertible_foldr' _ _ (fun j => ((hker j).pow (pos j)).isInvertible_invModule)
    (fun j => ((hker j).pow (neg j)).isInvertible_module) _ ?_ (List.finRange m)
  exact (isInvertible_prod_pow' _ 𝔛reg.comp_isInvertible aplus).isInvertible_invModule.tensor
    (isInvertible_prod_pow' _ 𝔛reg.comp_isInvertible aminus).isInvertible_module

p2m_export "ModularCurve.DRResolvedModelPackage" "isInvertible_divisorialSheaf"

private theorem _root_.ModularCurve.DRResolvedModelPackage.exists_isInvertible_and_pullback_toDR_iso_divisorialSheaf (hp : 5 ≤ p)
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    [hint : IsIntegral (DRModelPackage.XO p O)]

    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base x) =
          (DRModel.baseChangeMap (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))
    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((p : ℕ) : O) e).IdealSheafData)
    (𝒞 : 𝔛reg.ChartWitness ((p : ℕ) : O) Fc)

    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ((p : ℕ) : O) e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((p : ℕ) : O)))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {V ((p : ℕ) : O)} else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {U ((p : ℕ) : O)} else ⊤)))
    {m : ℕ} (σ : Fin m → NeronModelInfra.SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ (nd : 𝔛reg.node) (i : Fin (𝔛reg.width nd - 1)),
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inr ⟨nd, i⟩) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inr ⟨nd, i⟩) = 0) :
    ∃ M : (DRModelPackage.XO p O).Modules, Scheme.Modules.IsInvertible M ∧
      Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj M ≅ 𝔛reg.divisorialSheaf σ pos neg aplus aminus) := by

  haveI := ModularCurve.DRModelPackage.locallyOfFinitePresentation_toBase p 𝔛
  haveI : IsLocallyNoetherian (DRModelPackage.XO p O) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))

  have hL : Scheme.Modules.IsInvertible (𝔛reg.divisorialSheaf σ pos neg aplus aminus) :=
    𝔛reg.isInvertible_divisorialSheaf σ pos neg v hv aplus aminus

  have hnorm : ∀ n (y : ↥(DRModelPackage.XO p O)), y ∈ 𝒞.U n →
      IsDomain ((DRModelPackage.XO p O).presheaf.stalk y) ∧ IsIntegrallyClosed ((DRModelPackage.XO p O).presheaf.stalk y) :=
    fun n y _ => ⟨inferInstance,
      ModularCurve.DRModelPackage.isIntegrallyClosed_stalk_pullback_toBase p hp 𝔛 O hϖ κ toκ hrat y⟩

  have hcover : ∀ y : ↥(DRModelPackage.XO p O), y ∉ 𝔛.isoLocus O → ∃ n, y = 𝔛reg.crossingPt n := by
    intro y hy
    rcases ModularCurve.DRModelPackage.mem_preimage_basicOpen_or_mem_preimage_smoothLocus_or_exists_eq_of_pullback_toBase
        p 𝔛 O hϖ κ toκ y with h | h | ⟨n', hn'⟩
    · exact absurd (Opens.mem_sup.mpr (Or.inr h)) hy
    · exact absurd (Opens.mem_sup.mpr (Or.inl h)) hy
    · refine ⟨𝔛reg.nodeEquiv.symm n', ?_⟩
      rw [hn', crossingPt, Equiv.apply_symm_apply]
  refine Scheme.Modules.IsInvertible.exists_isInvertible_and_pullback_iso_of_forall_exists_trivial_nhd
    𝔛reg.toDR (𝔛.isoLocus O) 𝔛reg.isIso_toDR_restrict_isoLocus 𝔛reg.crossingPt hcover 𝒞.U 𝒞.mem_U 𝒞.not_mem_U
    hnorm (fun n => ModularCurve.DRResolvedModelPackage.DRResolvedModelCharts.not_ringKrullDim_stalk_crossingPt_le_one ((p : ℕ) : O) hϖ 𝒞 n)
    _ hL (fun n => ModularCurve.DRResolvedModelPackage.DRResolvedModelCharts.exists_open_pullback_iso_unit_of_forall_exceptional_degree_eq_zero
      ((p : ℕ) : O) hϖ Fc hF 𝒞 σ pos neg v hv aplus aminus hdeg n)

p2m_export "ModularCurve.DRResolvedModelPackage" "exists_isInvertible_and_pullback_toDR_iso_divisorialSheaf"
end DRResolvedModelPackage

end ModularCurve

end

theorem solution
    {p : ℕ} [Fact p.Prime] (hp : 5 ≤ p) {𝔛 : DRModelPackage p}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hϖ : IsLocalRing.maximalIdeal O = Ideal.span {((p : ℕ) : O)})
    {κ : Type} [Field κ] [CharP κ p] [IsAlgClosed κ] {toκ : O →+* κ}
    (𝔛reg : DRResolvedModelPackage p 𝔛 O κ toκ)
    [IsIntegral (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))))]
    (hrat : ∀ x : ↥(pullback (𝔛.compInf κ) (𝔛.compZero κ)),
      ∃ s : Spec (CommRingCat.of (IsLocalRing.ResidueField O)) ⟶
          pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (IsLocalRing.ResidueField O)))),
        s ≫ pullback.snd _ _ = 𝟙 _ ∧
        (DRModel.baseChangeMap toκ).base ((pullback.fst (𝔛.compInf κ) (𝔛.compZero κ) ≫ 𝔛.compInf κ).base x) =
          (DRModel.baseChangeMap (IsLocalRing.residue O)).base
            (s.base (IsLocalRing.closedPoint (IsLocalRing.ResidueField O))))
    (Fc : ∀ e : ℕ, Fin (e + 1) → (Resolution ((p : ℕ) : O) e).IdealSheafData)
    (hF : ∀ (e : ℕ) (i : Fin e) (k : Fin (e + 1)), (Fc e k).comap (Resolution.ι ((p : ℕ) : O) e i) =
      Scheme.IdealSheafData.ofIdealTop (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of (CrossingQuotient O ((p : ℕ) : O)))).inv.hom
        (if (k : ℕ) = (i : ℕ) then Ideal.span {CrossingQuotient.V ((p : ℕ) : O)}
          else if (k : ℕ) = (i : ℕ) + 1 then Ideal.span {CrossingQuotient.U ((p : ℕ) : O)} else ⊤)))
    (ch : 𝔛reg.DRResolvedModelCharts ((p : ℕ) : O) Fc)
    (m : ℕ) (σ : Fin m → SchemeHomOver (𝟙 (Spec (CommRingCat.of O))) 𝔛reg.toBase) (pos neg : Fin m → ℕ)
    (v : Fin m → X0MqComponents 𝔛reg.width)
    (hv : ∀ j, (σ j).1.base (IsLocalRing.closedPoint O) ∈ 𝔛reg.smoothOffEdges ∧
        (σ j).1.base (IsLocalRing.closedPoint O) ∈ (𝔛reg.comp (v j)).support ∧
        ∀ w, w ≠ v j → (σ j).1.base (IsLocalRing.closedPoint O) ∉ (𝔛reg.comp w).support)
    (aplus aminus : X0MqComponents 𝔛reg.width → ℕ)
    (hdeg : ∀ (nd : 𝔛reg.node) (i : Fin (𝔛reg.width nd - 1)),
        (∑ j, Finsupp.single (v j) ((pos j : ℤ) - (neg j : ℤ))) (Sum.inr ⟨nd, i⟩) +
          MazurRapoportAppendix.intersectionAlpha (x0MqResolvedTable 𝔛reg.width)
            (fun F => ((aplus F : ℤ) - (aminus F : ℤ))) (Sum.inr ⟨nd, i⟩) = 0) :
    ∃ M : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O)))).Modules,
      Scheme.Modules.IsInvertible M ∧
      Nonempty ((Scheme.Modules.pullback 𝔛reg.toDR).obj M ≅
        ((List.finRange m).foldr
          (fun j N => ((σ j).1.ker ^ (pos j)).invModule ⊗ ((σ j).1.ker ^ (neg j)).module ⊗ N)
          ((∏ F, (𝔛reg.comp F) ^ (aplus F)).invModule ⊗ (∏ F, (𝔛reg.comp F) ^ (aminus F)).module))) :=
  𝔛reg.exists_isInvertible_and_pullback_toDR_iso_divisorialSheaf hp hϖ hrat Fc ch hF σ pos neg v hv aplus aminus hdeg

end S_ModularCurve_DRResolvedModelPackage_exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero
end P2MW
export P2MW.S_ModularCurve_DRResolvedModelPackage_exists_isInvertible_and_pullback_toDR_iso_of_forall_exceptional_degree_eq_zero (solution)
