-- Prove2me | solution 1 for ModularCurve.XHDRModelAtP.exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/d5d43f94-2d04-568b-a104-966477e59552

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_XHHeckeOperator
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_ModulesNormModule
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_heckeDegeneracyPair_chartPin_flat
import Theorems.Thm_ModularCurve_XHDRModelAtP_exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed
import Theorems.Thm_AlgebraicGeometry_geometricallyIntegral_of_smooth_of_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_flat_toBase
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFinitePresentation_toBase
import Theorems.Thm_ModularCurve_finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC
import Theorems.Thm_GaloisRep_isFractionRing_ratLocalizedAt
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegrallyClosed_stalk
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_isIntegral
import Theorems.Thm_ModularCurve_heckeInputsHAlong
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_morphismRestrict_eq_finrank
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
import Theorems.Thm_AlgebraicGeometry_RelPicard_baseChange_relativeGroupLaw_mul_compat
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_normModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_finrank_pullbackMap_of_comp_eq
import Theorems.Thm_ModularCurve_XHDRModelAtP_isFinite_flat_finrank_curveChange_heckeDegeneracy_rat
import Theorems.Thm_ModularCurve_XH_pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_pointEquivPlace_eq_restrictAlong_of_chartPin
import Theorems.Thm_ModularCurve_exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_finrankAlong_heckeBetaHBar
import Theorems.Thm_ringKrullDim_le_of_ringHom_isIntegral
import Theorems.Thm_AlgebraicGeometry_IsOpenImmersion_ringKrullDim_stalk_eq
import Theorems.Thm_AlgebraicGeometry_IsAffineOpen_ringKrullDim_stalk_le
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_finite_polynomial_chartAlgFin_and_chartAlgInf
import Theorems.Thm_ModularCurve_transcendental_of_coe_eq_coeffEmb_jq
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.DRModelPackageLevel.Mfib_chart_nonempty ModularCurve.DRModelPackageLevel.eeta_iso ModularCurve.DRModelPackageLevel.efib_iso ModularCurve.DRModelPackageLevel.smoothLocus_relDim AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar"
p2m_attr_erase "instance" "AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModulePreGlue AlgebraicGeometry.Scheme.Modules.GlueOfCocycle.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensSubtypeForallMinMemAddSubgroupFamilies"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.ProjectiveLine.map_mk ModularCurve.DRModelPackageLevel.mk.injEq ModularCurve.DRModelPackageLevel.mk.sizeOf_spec ModularCurve.DRModelPackageLevel.πw_val ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicCurve.mulAdele_apply"
p2m_attr_erase "simp" "AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply AlgebraicCurve.cechH1.traceAlong_mk AlgebraicCurve.lSpaceOnZero.coe_pullbackAlong_apply AlgebraicCurve.lSpaceOnZero.coe_traceAlong_apply AlgebraicCurve.cechH1.pullbackAlong_mk AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I"
p2m_attr_erase "simp" "AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.Modules.glueComponent_glueMk AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.injEq AlgebraicGeometry.Scheme.Modules.UnitCocycle.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec RegularLocalRingQuotientAscent.dualNumberFst_apply"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"

open scoped MatrixGroups
p2m_open "CategoryTheory.MonoidalCategory GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve"
open scoped MatrixGroups

universe u v w
p2m_open_scoped "TensorProduct Polynomial AlgebraicGeometry.Polynomial"
open AlgebraicCurve.TwoChartIntegralModel in
section
open AlgebraicCurve.TwoChartIntegralModel
namespace DimFibAux

theorem ringKrullDim_tensorProduct_le_one
    {R : Type u} [CommRing R] {B : Type v} [CommRing B] [Algebra R B]
    (φ : R[X] →ₐ[R] B) (hφ : φ.toRingHom.IsIntegral)
    (k : Type w) [Field k] [Algebra R k] :
    ringKrullDim (B ⊗[R] k) ≤ 1 := by
  classical
  let ψ : k[X] →+* B ⊗[R] k :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := k)).toRingHom
      (φ Polynomial.X ⊗ₜ[R] (1 : k))
  have hcomp : ψ.comp (Polynomial.mapRingHom (algebraMap R k)) =
      (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := k)).comp φ.toRingHom := by
    apply Polynomial.ringHom_ext
    · intro a
      have h1 : φ (Polynomial.C a) = algebraMap R B a := by rw [Polynomial.C_eq_algebraMap, AlgHom.commutes]
      have h2 : (Algebra.TensorProduct.includeRight (R := R) (A := B) (B := k)) (algebraMap R k a) =
          algebraMap R (B ⊗[R] k) a := AlgHom.commutes _ a
      simp only [ψ, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, h2,
        Algebra.TensorProduct.includeLeftRingHom_apply, Algebra.TensorProduct.algebraMap_apply]
    · simp only [ψ, RingHom.coe_comp, Function.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        Algebra.TensorProduct.includeLeftRingHom_apply]
  have hψ : ψ.IsIntegral := by
    letI : Algebra R[X] B := φ.toRingHom.toAlgebra
    letI : Algebra k[X] (B ⊗[R] k) := ψ.toAlgebra
    intro x
    change IsIntegral k[X] x
    induction x using TensorProduct.induction_on with
    | zero => exact isIntegral_zero
    | tmul b c =>
      have hb : IsIntegral R[X] b := hφ b
      have h1 : IsIntegral k[X] (b ⊗ₜ[R] (1 : k)) :=
        hb.map_of_comp_eq (Polynomial.mapRingHom (algebraMap R k))
          (Algebra.TensorProduct.includeLeftRingHom (R := R) (A := B) (B := k)) hcomp
      have h2 : b ⊗ₜ[R] c = (b ⊗ₜ[R] (1 : k)) * algebraMap k[X] (B ⊗[R] k) (Polynomial.C c) := by
        change b ⊗ₜ[R] c = (b ⊗ₜ[R] (1 : k)) * ψ (Polynomial.C c)
        simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
          Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [h2]
      exact h1.mul isIntegral_algebraMap
    | add x y hx hy => exact hx.add hy
  calc ringKrullDim (B ⊗[R] k) ≤ ringKrullDim k[X] := ringKrullDim_le_of_ringHom_isIntegral ψ hψ
    _ = 1 := by
      rw [Polynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]; rfl

theorem ringKrullDim_stalk_le_of_isOpenImmersion {X : Scheme.{u}} (S : CommRingCat.{u})
    (g : Spec S ⟶ X) [IsOpenImmersion g] (y : Spec S) :
    ringKrullDim (X.presheaf.stalk (g.base y)) ≤ ringKrullDim S := by
  rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq g y]
  refine (AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le (isAffineOpen_top (Spec S)) y trivial).trans ?_
  exact (ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso S).commRingCatIsoToRingEquiv).le

theorem ringKrullDim_stalk_pullback_comp_le {X : Scheme.{u}} (R B k : Type u) [CommRing R] [CommRing B] [CommRing k]
    [Algebra R B] [Algebra R k] (ι : Spec (CommRingCat.of B) ⟶ X) (f : X ⟶ Spec (CommRingCat.of R))
    (hι : ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R B)))
    (y : ↥(pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R k))))) :
    ringKrullDim ((pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.stalk y) ≤
      ringKrullDim (B ⊗[R] k) := by
  let e : pullback (ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap R k))) ≅ Spec (CommRingCat.of (B ⊗[R] k)) :=
    pullback.congrHom hι rfl ≪≫ pullbackSpecIso R B k
  rw [AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq e.hom y]
  have h := AlgebraicGeometry.IsAffineOpen.ringKrullDim_stalk_le (isAffineOpen_top (Spec (CommRingCat.of (B ⊗[R] k))))
    (e.hom.base y) trivial
  refine h.trans ?_
  exact (ringKrullDim_eq_of_ringEquiv (Scheme.ΓSpecIso (CommRingCat.of (B ⊗[R] k))).commRingCatIsoToRingEquiv).le

theorem ringKrullDim_stalk_pullback_toBase_le
    (R : Type u) [CommRing R] (F : Type u) [Field F] [Algebra R F] (j : F) [Fact (j ≠ 0)]
    (k : Type u) [CommRing k] [Algebra R k] (d : WithBot ℕ∞)
    (hFin : ringKrullDim (↥(chartAlgFin R F j) ⊗[R] k) ≤ d)
    (hInf : ringKrullDim (↥(chartAlgInf R F j) ⊗[R] k) ≤ d)
    (z : ↥(pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k))))) :
    ringKrullDim ((pullback (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.stalk z) ≤ d := by
  classical
  let 𝒰 : (AlgebraicCurve.TwoChartIntegralModel R F j).OpenCover :=
    Scheme.Cover.mkOfCovers Bool
      (fun b => match b with | true => XFin R F j | false => XInf R F j)
      (fun b => match b with | true => ιFin R F j | false => ιInf R F j)
      (fun x => by
        rcases mem_range_ιFin_or_mem_range_ιInf R F j x with ⟨y, hy⟩ | ⟨y, hy⟩
        · exact ⟨true, y, hy⟩
        · exact ⟨false, y, hy⟩)
      (fun b => by cases b <;> dsimp only <;> infer_instance)
  let 𝒱 := Scheme.Pullback.openCoverOfLeft 𝒰 (toBase R F j) (Spec.map (CommRingCat.ofHom (algebraMap R k)))
  obtain ⟨i, y, hy⟩ := 𝒱.exists_eq z
  rw [← hy, ← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq (𝒱.f i) y]
  rcases i with (_ | _)
  · change ringKrullDim ((pullback (ιInf R F j ≫ toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.stalk y) ≤ d
    exact (ringKrullDim_stalk_pullback_comp_le R (↥(chartAlgInf R F j)) k (ιInf R F j) (toBase R F j)
      (ιInf_toBase R F j) y).trans hInf
  · change ringKrullDim ((pullback (ιFin R F j ≫ toBase R F j)
        (Spec.map (CommRingCat.ofHom (algebraMap R k)))).presheaf.stalk y) ≤ d
    exact (ringKrullDim_stalk_pullback_comp_le R (↥(chartAlgFin R F j)) k (ιFin R F j) (toBase R F j)
      (ιFin_toBase R F j) y).trans hFin

end DimFibAux

namespace GenCodim
open ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup

theorem ringKrullDim_stalk_genericFibre_le_one
    (L : Type) [Field L] [CharZero L]
    (K : IntermediateField L (LaurentSeries L))
    (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [UniqueFactorizationMonoid A] [Algebra A L] [IsFractionRing A L]
    [instAK : Algebra A ↥K] [towK : IsScalarTower A L ↥K]
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq) [Fact (j ≠ 0)]
    (hFD : FiniteDimensional ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K)
    (z : ↥(pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L))))) :
    ringKrullDim ((pullback (AlgebraicCurve.TwoChartIntegralModel.toBase A (↥K) j)
      (Spec.map (CommRingCat.ofHom (algebraMap A L)))).presheaf.stalk z) ≤ 1 := by
  classical
  have htj := ModularCurve.transcendental_of_coe_eq_coeffEmb_jq L K A j hj
  haveI := hFD
  haveI hsep : Algebra.IsSeparable ↥(IntermediateField.adjoin L ({j} : Set ↥K)) ↥K :=
    Algebra.IsSeparable.of_integral _ _
  obtain ⟨hfF, hfI⟩ := finite_polynomial_chartAlgFin_and_chartAlgInf A L ↥K j htj hFD hsep
  have hfF' : (polynomialToChartFin A ↥K j).toRingHom.Finite := hfF
  have hfI' : (polynomialToChartInf A ↥K j).toRingHom.Finite := hfI
  exact DimFibAux.ringKrullDim_stalk_pullback_toBase_le A ↥K j L 1
    (DimFibAux.ringKrullDim_tensorProduct_le_one _ (RingHom.IsIntegral.of_finite hfF') L)
    (DimFibAux.ringKrullDim_tensorProduct_le_one _ (RingHom.IsIntegral.of_finite hfI') L) z

theorem isLocalization_away_natCast (p : ℕ) [hp : Fact p.Prime] :
    IsLocalization.Away ((p : R p)) ℚ := by
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨y, k, rfl⟩
    show IsUnit ((((p : R p) ^ k : R p)) : ℚ)
    rw [Subring.coe_pow, Subring.coe_natCast]
    exact isUnit_iff_ne_zero.mpr (pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero))
  · intro q
    obtain ⟨k, d, hd, hdd⟩ := Nat.exists_eq_pow_mul_and_not_dvd q.den_nz p hp.out.one_lt.ne'
    have hd0 : d ≠ 0 := by rintro rfl; rw [mul_zero] at hdd; exact q.den_nz hdd
    have hq : q * (p : ℚ) ^ k = (q.num : ℚ) / (d : ℚ) := by
      have h1 : q = (q.num : ℚ) / (q.den : ℚ) := (Rat.num_div_den q).symm
      conv_lhs => rw [h1]
      rw [hdd]; push_cast
      have hpk : ((p : ℚ)) ^ k ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.out.ne_zero)
      field_simp
    have hmem : q * (p : ℚ) ^ k ∈ GaloisRep.ratLocalizedAt p := by
      rw [hq]
      show ((q.num : ℚ) / (d : ℚ)).den.Coprime p
      have hden : ((q.num : ℚ) / (d : ℚ)).den ∣ d := by
        have := Rat.den_dvd q.num (d : ℤ)
        rw [Rat.divInt_eq_div] at this
        push_cast at this
        exact_mod_cast this
      exact Nat.Coprime.coprime_dvd_left hden ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hd).symm
    refine ⟨⟨⟨_, hmem⟩, ⟨(p : R p) ^ k, k, rfl⟩⟩, ?_⟩
    show q * ((((p : R p) ^ k : R p)) : ℚ) = q * (p : ℚ) ^ k
    rw [Subring.coe_pow, Subring.coe_natCast]
  · intro x y h
    exact ⟨1, by simpa using Subtype.ext h⟩

p2m_attr_erase "instance" "DivisionRing.toRatAlgebra in"

theorem laurentBaseChange_rat (F : IntermediateField ℚ (LaurentSeries ℚ)) : laurentBaseChange ℚ F = F := by
  unfold laurentBaseChange
  have hce : ∀ x : LaurentSeries ℚ, coeffEmb ℚ x = x := fun x => by
    ext k; rw [ModularCurve.coeffEmb_coeff]; rfl
  have : (⇑(coeffEmb ℚ) '' (F : Set (LaurentSeries ℚ))) = (F : Set (LaurentSeries ℚ)) := by
    ext x; simp [hce]
  rw [this]
  exact IntermediateField.adjoin_self ℚ F

theorem tower_R (p : ℕ) (K : IntermediateField ℚ (LaurentSeries ℚ)) :
    @IsScalarTower (R p) ℚ (↥K) Algebra.toSMul (instAlgebraIntermediateFieldLaurent K).toSMul Algebra.toSMul := by
  refine @IsScalarTower.of_algebraMap_eq (R p) ℚ _ _ _ _ _ (instAlgebraIntermediateFieldLaurent K) _ (fun r => ?_)
  apply Subtype.ext
  have h1 : ((algebraMap (R p) ↥K r : ↥K) : LaurentSeries ℚ) = ((r : ℚ) : LaurentSeries ℚ) := by
    rw [show algebraMap (R p) ↥K r = algebraMap ℚ ↥K (r : ℚ) from rfl, eq_ratCast, SubfieldClass.coe_ratCast]
  rw [h1]
  show ((r : ℚ) : LaurentSeries ℚ) = ((@algebraMap ℚ ↥K _ _ (instAlgebraIntermediateFieldLaurent K) ((algebraMap (R p) ℚ) r) : ↥K) : LaurentSeries ℚ)
  rw [show (algebraMap (R p) ℚ) r = (r : ℚ) from rfl, eq_ratCast, SubfieldClass.coe_ratCast]

theorem ringKrullDim_stalk_le_one_of_generic (p : ℕ) [Fact p.Prime]
    (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (x : ↥(X p Γ hj)) (hx : ((toBase p Γ hj).base x).asIdeal = ⊥) :
    ringKrullDim ((X p Γ hj).presheaf.stalk x) ≤ 1 := by
  classical
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI := isLocalization_away_natCast p

  haveI : IsOpenImmersion (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))) := IsOpenImmersion.of_isLocalization (p : R p)
  have hxr : x ∈ Set.range (pullback.fst (toBase p Γ hj) (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ)))).base := by
    rw [Scheme.Pullback.range_fst]
    show (toBase p Γ hj).base x ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap (R p) ℚ))).base
    refine ⟨IsLocalRing.closedPoint ℚ, ?_⟩
    apply PrimeSpectrum.ext
    rw [hx]
    show Ideal.comap (algebraMap (R p) ℚ) (IsLocalRing.closedPoint ℚ).asIdeal = ⊥
    rw [show (IsLocalRing.closedPoint ℚ).asIdeal = ⊥ from IsLocalRing.maximalIdeal_eq_bot]
    exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective (R p) ℚ)
  obtain ⟨z, rfl⟩ := hxr
  rw [← AlgebraicGeometry.IsOpenImmersion.ringKrullDim_stalk_eq (pullback.fst _ _) z]
  have hFD := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange Γ hT ℚ
    (qExpFunctionFieldC ℚ Γ) (laurentBaseChange_rat _).symm (jAt Γ hj) rfl
  exact ringKrullDim_stalk_genericFibre_le_one (L := ℚ) (K := qExpFunctionFieldC ℚ Γ) (A := R p) (towK := tower_R p _)
    (jAt Γ hj) rfl hFD z

end GenCodim

end

noncomputable section

namespace GenAwayBody

private def castBase {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s') (a : SchemeHomOver s f) :
    SchemeHomOver s' f :=
  ⟨a.1, a.2.trans e⟩

private theorem castBase_coe {B Y X : Scheme.{u}} {s s' : Y ⟶ B} {f : X ⟶ B} (e : s = s')
    (a : SchemeHomOver s f) : (castBase e a).1 = a.1 := rfl

private theorem mul_castBase {R : Type u} [CommRing R] {A T : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
    (G : RelativeGroupLaw R f) {s s' : T ⟶ Spec (CommRingCat.of R)} (e : s = s') (a b : SchemeHomOver s f) :
    G.mul s' (castBase e a) (castBase e b) = castBase e (G.mul s a b) := by
  subst e; rfl

private def liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    SchemeHomOver t (D.baseChange R').toBase :=
  ⟨pullback.lift a.1 t a.2, pullback.lift_snd _ _ _⟩

private theorem liftPt_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    (liftPt D R' t a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  pullback.lift_fst _ _ _

private theorem eq_liftPt {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (z : SchemeHomOver t (D.baseChange R').toBase)
    (a : SchemeHomOver (t ≫ specMap R R') D.toBase)
    (hz : z.1 ≫ pullback.fst D.toBase (specMap R R') = a.1) : z = liftPt D R' t a := by
  apply Subtype.ext
  apply pullback.hom_ext
  · exact hz.trans (liftPt_fst D R' t a).symm
  · exact z.2.trans (pullback.lift_snd _ _ _).symm

private theorem liftPt_mul {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a b : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    liftPt D R' t ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) h).mul
        (t ≫ specMap R R') a b) =
      (RepresentsRelSubPic.relativeGroupLaw
        (P := algEquivZeroGroupCut (baseChange R c R') (sectionBaseChange R' ε)) h').mul t
        (liftPt D R' t a) (liftPt D R' t b) := by
  symm
  apply eq_liftPt
  exact AlgebraicGeometry.RelPicard.baseChange_relativeGroupLaw_mul_compat R c ε D h R' h' hP t _ _ a b
    (liftPt_fst D R' t a).symm (liftPt_fst D R' t b).symm

private def liftEquiv {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R') :
    SchemeHomOver s D.toBase ≃ SchemeHomOver t (D.baseChange R').toBase where
  toFun a := liftPt D R' t (castBase hs a)
  invFun z := ⟨z.1 ≫ pullback.fst D.toBase (specMap R R'), by
    rw [Category.assoc, pullback.condition, reassoc_of% z.2, hs]⟩
  left_inv a := Subtype.ext (liftPt_fst D R' t (castBase hs a))
  right_inv z := (eq_liftPt D R' t z _ rfl).symm

private theorem liftEquiv_apply {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R')
    (a : SchemeHomOver s D.toBase) : liftEquiv D R' t hs a = liftPt D R' t (castBase hs a) := rfl

private theorem liftEquiv_apply_fst {R : Type u} [CommRing R] {C : Scheme.{u}} {c : C ⟶ Spec (CommRingCat.of R)}
    (D : RelativePic0Designation R c) (R' : Type u) [CommRing R'] [Algebra R R']
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) {s : T ⟶ Spec (CommRingCat.of R)} (hs : s = t ≫ specMap R R')
    (a : SchemeHomOver s D.toBase) :
    (liftEquiv D R' t hs a).1 ≫ pullback.fst D.toBase (specMap R R') = a.1 :=
  liftPt_fst D R' t (castBase hs a)

private theorem isPullback_fst_curveChange {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    IsPullback (pullback.fst c' t) (curveChange f hf t) f (pullback.fst c t) := by
  refine IsPullback.of_bot ?_ ?_ (IsPullback.of_hasPullback c t)
  · rw [curveChange_snd, hf]
    exact IsPullback.of_hasPullback c' t
  · simp only [curveChange, pullback.lift_fst]

private theorem curveChange_fst {R : Type u} [CommRing R] {C C' T : Scheme.{u}}
    {c : C ⟶ Spec (CommRingCat.of R)} {c' : C' ⟶ Spec (CommRingCat.of R)}
    (f : C' ⟶ C) (hf : f ≫ c = c') (t : T ⟶ Spec (CommRingCat.of R)) :
    curveChange f hf t ≫ pullback.fst c t = pullback.fst c' t ≫ f := by
  simp only [curveChange, pullback.lift_fst]

private theorem isIso_lift_of_comp {X S T T' : Scheme.{u}} (f : X ⟶ S) (u : T ⟶ S) (v : T' ⟶ T) (w : T' ⟶ S)
    (hw : w = v ≫ u) (k : pullback f w ⟶ pullback f u)
    (hk₁ : k ≫ pullback.fst f u = pullback.fst f w) (hk₂ : k ≫ pullback.snd f u = pullback.snd f w ≫ v)
    (hk : k ≫ pullback.snd f u = pullback.snd f w ≫ v) :
    IsIso (pullback.lift k (pullback.snd f w) hk : pullback f w ⟶ pullback (pullback.snd f u) v) := by
  refine ⟨⟨pullback.lift (pullback.fst _ _ ≫ pullback.fst f u) (pullback.snd _ _) ?_, ?_, ?_⟩⟩
  · rw [hw, Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst_assoc, hk₁, Category.id_comp]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, Category.id_comp]
      apply pullback.hom_ext
      · rw [Category.assoc, hk₁, pullback.lift_fst]
      · rw [Category.assoc, hk₂, pullback.lift_snd_assoc, pullback.condition]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.id_comp]

section K

private abbrev cls {X : Scheme.{u}} (M : X.Modules) : Skeleton X.Modules := toSkeleton M

private theorem cls_eq_iff {X : Scheme.{u}} (A B : X.Modules) : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun ⟨e⟩ => Quotient.sound ⟨e⟩⟩

private theorem cls_congr {X : Scheme.{u}} {A B : X.Modules} (e : A ≅ B) : cls A = cls B :=
  (cls_eq_iff A B).2 ⟨e⟩

private noncomputable def isoOfClsEq {X : Scheme.{u}} {A B : X.Modules} (h : cls A = cls B) : A ≅ B :=
  ((cls_eq_iff A B).1 h).some

private theorem cls_tensor {X : Scheme.{u}} (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B :=
  Skeleton.toSkeleton_tensorObj A B

private theorem cls_unit (X : Scheme.{u}) : cls (𝟙_ X.Modules) = 1 := Skeleton.one_eq.symm

private theorem cls_pullback_congr {X Y : Scheme.{u}} (f : X ⟶ Y) {A B : Y.Modules} (h : cls A = cls B) :
    cls ((Scheme.Modules.pullback f).obj A) = cls ((Scheme.Modules.pullback f).obj B) :=
  cls_congr ((Scheme.Modules.pullback f).mapIso (isoOfClsEq h))

private theorem cls_pullback_tensor {X Y : Scheme.{u}} (f : X ⟶ Y) (A B : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj (A ⊗ B)) =
      cls ((Scheme.Modules.pullback f).obj A) * cls ((Scheme.Modules.pullback f).obj B) :=
  (cls_congr (Scheme.Modules.pullbackTensorObjIso f A B)).trans (cls_tensor _ _)

private theorem cls_pullback_unit {X Y : Scheme.{u}} (f : X ⟶ Y) :
    cls ((Scheme.Modules.pullback f).obj (𝟙_ Y.Modules)) = 1 :=
  (cls_congr (Scheme.Modules.pullbackTensorUnitObjIso f)).trans (cls_unit X)

private theorem cls_pullback_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    cls ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) =
      cls ((Scheme.Modules.pullback (f ≫ g)).obj M) :=
  cls_congr ((Scheme.Modules.pullbackComp f g).app M)

private theorem cls_pullback_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (h : f = g) (M : Y.Modules) :
    cls ((Scheme.Modules.pullback f).obj M) = cls ((Scheme.Modules.pullback g).obj M) := by
  subst h; rfl

private theorem cls_pullback_id {X : Scheme.{u}} (M : X.Modules) :
    cls ((Scheme.Modules.pullback (𝟙 X)).obj M) = cls M :=
  cls_congr ((Scheme.Modules.pullbackId X).app M)

private theorem cls_pullback_inv_hom {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : Y.Modules) :
    cls ((Scheme.Modules.pullback (inv e)).obj ((Scheme.Modules.pullback e).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.inv_hom_id e), cls_pullback_id]

private theorem cls_pullback_hom_inv {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] (M : X.Modules) :
    cls ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback (inv e)).obj M)) = cls M := by
  rw [cls_pullback_comp, cls_pullback_congr_hom (IsIso.hom_inv_id e), cls_pullback_id]

private theorem cls_normModule_congr {X Y : Scheme.{u}} (π : X ⟶ Y) (d : ℕ) {L L' : X.Modules} (h : cls L = cls L') :
    cls (Scheme.Modules.normModule π d L) = cls (Scheme.Modules.normModule π d L') :=
  cls_congr (Scheme.Modules.normModuleMapIso π d (isoOfClsEq h))

end K

private theorem poincare_liftPt_iso {R : Type u} [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c) (D : RelativePic0Designation R c)
    (h : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (R' : Type u) [CommRing R'] [Algebra R R']
    (h' : RepresentsRelSubPic (baseChange R c R') (sectionBaseChange R' ε)
      (algEquivZeroCut (baseChange R c R') (sectionBaseChange R' ε)) (D.baseChange R'))
    (hP : Nonempty (h'.poincare.L ≅ (BaseChange.ofR c ε R'
      (h.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩)).L))
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R')) (a : SchemeHomOver (t ≫ specMap R R') D.toBase) :
    Nonempty ((h'.poincare.pullbackAlong (liftPt D R' t a)).L ≅
      (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj (h.poincare.pullbackAlong a).L) := by
  let ψ₀ : SchemeHomOver ((D.baseChange R').toBase ≫ specMap R R') D.toBase :=
    ⟨pullback.fst D.toBase (specMap R R'), pullback.condition⟩
  have E : baseChangeSnd (baseChange R c R') (liftPt D R' t a) ≫
      (BaseChange.κ c R' (D.baseChange R').toBase).hom ≫ baseChangeSnd c ψ₀ =
      (BaseChange.κ c R' t).hom ≫ baseChangeSnd c a := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_fst', BaseChange.κ_hom_fst,
        ← Category.assoc, BaseChange.baseChangeSnd_fst', Category.assoc, BaseChange.baseChangeSnd_fst',
        BaseChange.κ_hom_fst]
    · rw [Category.assoc, Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc ((BaseChange.κ c R' _).hom),
        BaseChange.κ_hom_snd, ← Category.assoc, BaseChange.baseChangeSnd_snd', Category.assoc, liftPt_fst,
        Category.assoc, BaseChange.baseChangeSnd_snd', ← Category.assoc, BaseChange.κ_hom_snd]
  refine ⟨(Scheme.Modules.pullback _).mapIso hP.some ≪≫ ?_⟩
  change (Scheme.Modules.pullback (baseChangeSnd _ (liftPt D R' t a))).obj
      ((Scheme.Modules.pullback (BaseChange.κ c R' (D.baseChange R').toBase).hom).obj
        ((Scheme.Modules.pullback (baseChangeSnd c ψ₀)).obj h.poincare.L)) ≅
    (Scheme.Modules.pullback (BaseChange.κ c R' t).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd c a)).obj h.poincare.L)
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app _ ≪≫
    (Scheme.Modules.pullbackCongr (by rw [Category.assoc]; exact E)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ _).app _).symm

end GenAwayBody

end

namespace L3bAsm
open ModularCurve ModularCurve.XHDRLevel CongruenceSubgroup

theorem coeffEmb_qExpandH (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n] (x : LaurentSeries ℚ) :
    ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ n x) = ModularCurve.qExpand L n (ModularCurve.coeffEmb L x) := by
  ext k
  rw [ModularCurve.coeffEmb_coeff]
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [ModularCurve.qExpand_coeff_mul, ModularCurve.qExpand_coeff_mul, ModularCurve.coeffEmb_coeff]
  · rw [ModularCurve.qExpand_coeff_of_not_dvd n _ hk, ModularCurve.qExpand_coeff_of_not_dvd n _ hk, map_zero]

end L3bAsm

open L3bAsm GenAwayBody in
set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    [IsProper (toBase p (ΓM M H) hj)]

    (D : RelativePic0Designation (R p) (toBase p (ΓM M H) hj))
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) D)
    (hsm : Smooth D.toBase) (hsep : IsSeparated D.toBase) (hqc : QuasiCompact D.toBase)
    (hsurj : Surjective D.toBase) (hgc : GeometricallyConnected D.toBase)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase p (ΓM M H) hj) 𝔛.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔛.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase p (ΓM M H) hj) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (t ≫ (sectionBaseChange ℚ 𝔛.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔛.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶ pullback (toBase p (ΓM M H) hj) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.fst (toBase p (ΓM M H) hj) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase p (ΓM M H) hj) (specMap (R p) ℚ) = pullback.snd (toBase p (ΓM M H) hj) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔛.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔛.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔛.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1)
    (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JH M H ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JH M H,
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JH M H),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(xHFunctionFieldBar M H)),
        (Dv : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ p) :
    haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
    ∃ φ : SchemeHomOver D.toBase D.toBase,
      (∀ {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s D.toBase),
        NeronModelInfra.schemeHomOverComp
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s x y) φ =
          (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul s
            (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JH M H, (pts (heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x)).1 = (pts x).1 ≫ φ.1 := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩

  have hIn := ModularCurve.heckeInputsHAlong (AlgebraicClosure ℚ) M H ℓ
  have hβdef : HeckeBetaHDefined M H ℓ := hIn.betaHDefined

  obtain ⟨πα, πβ, hfinα, hfinβ, hlfpα, hlfpβ, ια, ιβ, U, hsurjα, hsurjβ, hια, hιβ, hchα, hchβ, hpreα, hpreβ,
      hUcodim, hUflα, hUflβ, hUrkα, hUrkβ⟩ :=
    ModularCurve.XHDRModelAtP.exists_heckeDegeneracyPair_chartPin_flat p M H hpM hj 𝔛 ℓ hβdef
  haveI := hfinα; haveI := hfinβ; haveI := hlfpα; haveI := hlfpβ; haveI := hUflα; haveI := hUflβ
  haveI : Surjective πα.1 := ⟨hsurjα⟩
  haveI : Surjective πβ.1 := ⟨hsurjβ⟩

  haveI := 𝔛.isIntegral; haveI := 𝔛.lfp; haveI := 𝔛.flat
  haveI : Smooth D.toBase := hsm
  haveI : GeometricallyConnected D.toBase := hgc
  haveI : Flat D.toBase := inferInstance
  haveI : LocallyOfFiniteType D.toBase := inferInstance
  haveI : IsDiscreteValuationRing (R p) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt p Fact.out
  haveI : IsLocallyNoetherian (X p (ΓM M H) hj) := LocallyOfFiniteType.isLocallyNoetherian (toBase p (ΓM M H) hj)
  haveI : IsIntegral (X p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.isIntegral (R p) _ _

  have hT0' : ModularGroup.T ∈ CongruenceSubgroup.Gamma0 (M * ℓ) := by
    rw [CongruenceSubgroup.Gamma0_mem]; simp [ModularGroup.T]
  have hTroof : ModularGroup.T ∈ CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ) :=
    Subgroup.mem_inf.mpr ⟨translation_mem_GammaH M H, hT0'⟩
  obtain ⟨hFTf, hFTi⟩ := ModularCurve.finiteType_chartAlgFin_and_chartAlgInf_twoChartIntegralModel_qExpFunctionFieldC p
    (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hTroof (jAt (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) rfl
  haveI := hFTf; haveI := hFTi
  haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
  haveI : LocallyOfFinitePresentation (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.locallyOfFinitePresentation_toBase (R p) _ _
  haveI : Flat (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) :=
    AlgebraicCurve.TwoChartIntegralModel.flat_toBase (R p) _ _ (fun a b h => by
      change algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) (a : ℚ) =
        algebraMap ℚ ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) (b : ℚ) at h
      exact Subtype.ext ((algebraMap ℚ _).injective h))
  haveI : IsLocallyNoetherian (X p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) :=
    LocallyOfFiniteType.isLocallyNoetherian (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj)
  haveI : GeometricallyIntegral D.toBase := AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected D.toBase
  haveI : IsIntegral ↑(pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) D.toBase) := inferInstance
  haveI : IsIntegral ↑(pullback (toBase p (ΓM M H) hj) D.toBase) := inferInstance
  have hnormD : ∀ V : (pullback (toBase p (ΓM M H) hj) D.toBase).Opens, IsAffineOpen V →
      IsIntegrallyClosed Γ(pullback (toBase p (ΓM M H) hj) D.toBase, V) := fun V hV =>
    AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.fst (toBase p (ΓM M H) hj) D.toBase) 𝔛.normal V hV
  haveI : GeometricallyConnected (pullback.fst D.toBase D.toBase ≫ D.toBase) := GeometricallyConnected.comp _ _
  haveI : GeometricallyIntegral (pullback.fst D.toBase D.toBase ≫ D.toBase) :=
    AlgebraicGeometry.geometricallyIntegral_of_smooth_of_geometricallyConnected _
  haveI : IsIntegral ↑(pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (pullback.fst D.toBase D.toBase ≫ D.toBase)) := inferInstance
  haveI : IsIntegral ↑(pullback (toBase p (ΓM M H) hj) (pullback.fst D.toBase D.toBase ≫ D.toBase)) := inferInstance
  have hnormD₂ : ∀ V : (pullback (toBase p (ΓM M H) hj) (pullback.fst D.toBase D.toBase ≫ D.toBase)).Opens, IsAffineOpen V →
      IsIntegrallyClosed Γ(pullback (toBase p (ΓM M H) hj) (pullback.fst D.toBase D.toBase ≫ D.toBase), V) := fun V hV =>
    AlgebraicGeometry.isIntegrallyClosed_sections_of_smooth_of_forall_isIntegrallyClosed_sections
      (pullback.fst (toBase p (ΓM M H) hj) (pullback.fst D.toBase D.toBase ≫ D.toBase)) 𝔛.normal V hV

  obtain ⟨Nm, hNm⟩ := AlgebraicGeometry.Scheme.Modules.exists_norm_isInvertible_tensor_pullback_normModule_of_isFinite_of_isIntegrallyClosed.{0}
  have hCnorm := AlgebraicCurve.TwoChartIntegralModel.isIntegrallyClosed_stalk (R p) ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)

  haveI : LocallyOfFinitePresentation (πα.1 ∣_ U) := inferInstance
  have hrk : ∀ y : U, (πα.1 ∣_ U).finrank y = (if ℓ ∣ M then ℓ else ℓ + 1) := fun y => by
    rw [AlgebraicGeometry.Scheme.Hom.finrank_morphismRestrict_eq_finrank πα.1 U y.1 y.2]
    exact hUrkα y.1 y.2
  have hVgen : ∀ x : ↥(X p (ΓM M H) hj), ((toBase p (ΓM M H) hj).base x).asIdeal = ⊥ → x ∈ U := fun x hx =>
    hUcodim x (GenCodim.ringKrullDim_stalk_le_one_of_generic p (ΓM M H) (translation_mem_GammaH M H) hj x hx)
  obtain ⟨Tℓ, ⟨hTiso⟩, hThom, hT0⟩ :=
    AlgebraicGeometry.RelPicard.RepresentsRelSubPic.exists_hom_classifies_norm_pullback_poincare_of_twoGluedCurves_of_mem_of_ringKrullDim_le_one
      (R p) (toBase p (ΓM M H) hj) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) hCnorm 𝔛.εinf
      (fun k _ _ f hf => ModularCurve.XHDRModelAtP.exists_twoGluedSmoothCurves_isReduced_pullback_of_ker_ne_bot p M H hpM hj 𝔛 k f hf)
      πβ πα D hD hnormD hnormD₂ Nm hNm U (if ℓ ∣ M then ℓ else ℓ + 1) hrk hUcodim hVgen
  refine ⟨Tℓ, hThom, ?_⟩

  have hgen : genPt p = specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ := by
    change Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first | rfl | (congr 2; exact IsScalarTower.algebraMap_eq _ _ _)

  have hUt : ∀ {T : Scheme.{0}} (t : T ⟶ base p) (ht : ∀ y : T, (t.base y).asIdeal = ⊥),
      Set.range (pullback.fst (toBase p (ΓM M H) hj) t).base ⊆ (U : Set (X p (ΓM M H) hj)) := by
    intro T t ht
    rintro _ ⟨y, rfl⟩
    apply hUcodim
    apply GenCodim.ringKrullDim_stalk_le_one_of_generic p (ΓM M H) (translation_mem_GammaH M H) hj
    have := congrArg (fun f => (f.base y).asIdeal) (pullback.condition (f := toBase p (ΓM M H) hj) (g := t))
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at this
    rw [this]
    exact ht _
  have hgenPt_gen : ∀ y : Spec (CommRingCat.of (AlgebraicClosure ℚ)), ((genPt p).base y).asIdeal = ⊥ := by
    intro y
    haveI : IsFractionRing (R p) ℚ := GaloisRep.isFractionRing_ratLocalizedAt p
    show Ideal.comap (algebraMap (R p) (AlgebraicClosure ℚ)) y.asIdeal = ⊥
    have hy : y.asIdeal = ⊥ := by
      have := y.isPrime; exact (Ideal.eq_bot_of_prime y.asIdeal)
    rw [hy]
    exact Ideal.comap_bot_of_injective _ ((algebraMap ℚ (AlgebraicClosure ℚ)).injective.comp (IsFractionRing.injective (R p) ℚ))
  have hUt₀ := hUt (genPt p) hgenPt_gen

  haveI : IsProper (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := inferInstance
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := 𝔛.smooth_generic
  haveI : GeometricallyIntegral (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) := 𝔛.geomIntegral_generic

  have h4b := ModularCurve.XHDRModelAtP.isFinite_flat_finrank_curveChange_heckeDegeneracy_rat p M H hpM hj 𝔛 ℓ πα πβ U hUcodim hUrkα hUrkβ
  rcases h4b with ⟨hfa, hfb, hla, hlb, hfla, hflb, hrka, hrkb⟩
  haveI := hfa; haveI := hfb; haveI := hla; haveI := hlb; haveI := hfla; haveI := hflb
  have hαc : curveChange πα.1 πα.2 (specMap (R p) ℚ) ≫ baseChange (R p) (toBase p (ΓM M H) hj) ℚ =
      baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ := curveChange_snd πα.1 πα.2 _
  have hβc : curveChange πβ.1 πβ.2 (specMap (R p) ℚ) ≫ baseChange (R p) (toBase p (ΓM M H) hj) ℚ =
      baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ := curveChange_snd πβ.1 πβ.2 _

  let φη : SchemeHomOver (D.baseChange ℚ).toBase (D.baseChange ℚ).toBase :=
    ⟨pullback.map D.toBase (specMap (R p) ℚ) D.toBase (specMap (R p) ℚ) Tℓ.1 (𝟙 _) (𝟙 _)
      (by rw [Tℓ.2, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp]),
     by simp only [pullback.lift_snd, Category.comp_id]⟩
  have hφfst : φη.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ) = pullback.fst _ _ ≫ Tℓ.1 := pullback.lift_fst _ _ _
  have hcomp : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (a : SchemeHomOver (s ≫ specMap (R p) ℚ) D.toBase),
      NeronModelInfra.schemeHomOverComp (liftPt D ℚ s a) φη = liftPt D ℚ s (NeronModelInfra.schemeHomOverComp a Tℓ) := by
    intro T s a
    apply eq_liftPt
    change ((liftPt D ℚ s a).1 ≫ φη.1) ≫ _ = a.1 ≫ Tℓ.1
    rw [Category.assoc, hφfst, ← Category.assoc, liftPt_fst]
  have hlift : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (z : SchemeHomOver s (D.baseChange ℚ).toBase),
      ∃ a : SchemeHomOver (s ≫ specMap (R p) ℚ) D.toBase, z = liftPt D ℚ s a := fun s z =>
    ⟨⟨z.1 ≫ pullback.fst _ _, by rw [Category.assoc, pullback.condition, reassoc_of% z.2]⟩, eq_liftPt D ℚ s z _ rfl⟩
  have hφadd : ∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ℚ)) (x y : SchemeHomOver s (D.baseChange ℚ).toBase),
      NeronModelInfra.schemeHomOverComp
          ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDQ).mul s x y) φη =
        (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDQ).mul s
          (NeronModelInfra.schemeHomOverComp x φη) (NeronModelInfra.schemeHomOverComp y φη) := by
    intro T s x y
    obtain ⟨a, rfl⟩ := hlift s x
    obtain ⟨b, rfl⟩ := hlift s y
    rw [← liftPt_mul _ _ D hD ℚ hDQ hPQ, hcomp, hcomp, hcomp, hThom, liftPt_mul _ _ D hD ℚ hDQ hPQ]

  let kQ' : pullback (toBase p (ΓM M H) hj) (genPt p) ⟶
      pullback (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    pullback.lift kQ (pullback.snd (toBase p (ΓM M H) hj) (genPt p)) (by exact hkQ₂)
  have hkQ'₁ : kQ' ≫ pullback.fst _ _ = kQ := pullback.lift_fst _ _ _
  have hkQ'₂ : kQ' ≫ pullback.snd _ _ = pullback.snd (toBase p (ΓM M H) hj) (genPt p) := pullback.lift_snd _ _ _
  haveI : IsIso kQ' := isIso_lift_of_comp _ _ _ _ hgen kQ hkQ₁ hkQ₂ _
  let eη := 𝔛.eeta ≫ kQ'
  have heη : eη ≫ pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) = 𝔛.Meta.toBase := by
    simp only [eη, Category.assoc, hkQ'₂]; exact 𝔛.heeta

  let kQ₂ : pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (genPt p) ⟶ pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (specMap (R p) ℚ) :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ specMap ℚ (AlgebraicClosure ℚ))
      (by rw [pullback.condition, Category.assoc, ← hgen])
  have hkQ₂₁ : kQ₂ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hkQ₂₂ : kQ₂ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ specMap ℚ (AlgebraicClosure ℚ) := pullback.lift_snd _ _ _
  let kQ₂' : pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (genPt p) ⟶
      pullback (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) :=
    pullback.lift kQ₂ (pullback.snd (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (genPt p)) hkQ₂₂
  haveI : IsIso kQ₂' := isIso_lift_of_comp _ _ _ _ hgen kQ₂ hkQ₂₁ hkQ₂₂ _

  haveI : IsFinite (curveChange πα.1 πα.2 D.toBase) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange πα.1 πα.2 D.toBase) inferInstance
  haveI : Surjective (curveChange πα.1 πα.2 D.toBase) :=
    MorphismProperty.of_isPullback (P := @Surjective) (isPullback_fst_curveChange πα.1 πα.2 D.toBase) inferInstance
  have hread : ∀ (a : SchemeHomOver (genPt p) D.toBase),
      Nonempty ((hD.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a Tℓ)).L ≅
        Scheme.Modules.rigidify (rigSection (toBase p (ΓM M H) hj) (genPt p) 𝔛.εinf) (pullback.snd (toBase p (ΓM M H) hj) (genPt p))
          (Scheme.Modules.normModule (curveChange πα.1 πα.2 (genPt p)) (if ℓ ∣ M then ℓ else ℓ + 1)
            ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 (genPt p))).obj (hD.poincare.pullbackAlong a).L))) :=
    fun a => AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
      hD πα πβ U (if ℓ ∣ M then ℓ else ℓ + 1) hUflα hUrkα
      (Nm (curveChange πα.1 πα.2 D.toBase) ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hD.poincare.L))
      ((hNm _ hnormD).1 _ (hD.poincare.isInvertible.pullback _))
      (fun V d' hf hl hr => (hNm _ hnormD).2.2.2.2.2 V d' hf hl hr _ (hD.poincare.isInvertible.pullback _))
      Tℓ ⟨hTiso⟩ (genPt p) a
      hUt₀
  have hφpt : ∀ z : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (D.baseChange ℚ).toBase,
      Nonempty ((hDQ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp z φη)).L ≅
        Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))) (sectionBaseChange ℚ 𝔛.εinf))
          (pullback.snd (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))
          (Scheme.Modules.normModule
            (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))))) (if ℓ ∣ M then ℓ else ℓ + 1)
            ((Scheme.Modules.pullback
              (curveChange (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hβc (Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))))).obj
              (hDQ.poincare.pullbackAlong z).L))) := by

    have hUt' : Set.range (pullback.fst (toBase p (ΓM M H) hj) (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)).base ⊆
        (U : Set (X p (ΓM M H) hj)) := hUt _ (fun y => by rw [← hgen]; exact hgenPt_gen y)

    intro z
    obtain ⟨a, rfl⟩ := hlift _ z
    have e3 := AlgebraicGeometry.RelPicard.RepresentsRelSubPic.nonempty_poincare_pullbackAlong_comp_iso_rigidify_normModule_of_range_subset
      hD πα πβ U (if ℓ ∣ M then ℓ else ℓ + 1) hUflα hUrkα
      (Nm (curveChange πα.1 πα.2 D.toBase) ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 D.toBase)).obj hD.poincare.L))
      ((hNm _ hnormD).1 _ (hD.poincare.isInvertible.pullback _))
      (fun V d' hf hl hr => (hNm _ hnormD).2.2.2.2.2 V d' hf hl hr _ (hD.poincare.isInvertible.pullback _))
      Tℓ ⟨hTiso⟩ (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ) a hUt'
    rcases e3 with ⟨e3⟩
    rcases poincare_liftPt_iso (toBase p (ΓM M H) hj) 𝔛.εinf D hD ℚ hDQ hPQ (specMap ℚ (AlgebraicClosure ℚ))
      (NeronModelInfra.schemeHomOverComp a Tℓ) with ⟨e1⟩
    rcases poincare_liftPt_iso (toBase p (ΓM M H) hj) 𝔛.εinf D hD ℚ hDQ hPQ (specMap ℚ (AlgebraicClosure ℚ)) a with ⟨e2⟩
    rw [hcomp]

    have sqα : (BaseChange.κ (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom ≫
        curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ) =
        curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [curveChange_fst, reassoc_of% (BaseChange.κ_hom_fst (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))),
          BaseChange.κ_hom_fst,
          reassoc_of% (curveChange_fst (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ))),
          curveChange_fst]
      · simp only [Category.assoc]
        rw [curveChange_snd, BaseChange.κ_hom_snd, BaseChange.κ_hom_snd, curveChange_snd]
    have sqβ : (BaseChange.κ (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom ≫
        curveChange πβ.1 πβ.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ) =
        curveChange (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hβc (specMap ℚ (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom := by
      apply pullback.hom_ext
      · simp only [Category.assoc]
        rw [curveChange_fst, reassoc_of% (BaseChange.κ_hom_fst (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))),
          BaseChange.κ_hom_fst,
          reassoc_of% (curveChange_fst (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hβc (specMap ℚ (AlgebraicClosure ℚ))),
          curveChange_fst]
      · simp only [Category.assoc]
        rw [curveChange_snd, BaseChange.κ_hom_snd, BaseChange.κ_hom_snd, curveChange_snd]

    haveI : IsFinite (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @IsFinite) (isPullback_fst_curveChange _ hαc _) inferInstance
    haveI : Flat (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @Flat) (isPullback_fst_curveChange _ hαc _) inferInstance
    haveI : LocallyOfFinitePresentation (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ))) :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) (isPullback_fst_curveChange _ hαc _) inferInstance
    have hπαt : curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ) =
        (BaseChange.κ (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).inv ≫
          curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)) ≫
          (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom := by
      rw [← sqα, Iso.inv_hom_id_assoc]
    haveI : IsFinite (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)) := by
      rw [hπαt]; infer_instance
    haveI : Flat (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)) := by
      rw [hπαt]; infer_instance
    haveI : LocallyOfFinitePresentation (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)) := by
      rw [hπαt]; infer_instance
    have hd : ∀ y, (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)).finrank y =
        (if ℓ ∣ M then ℓ else ℓ + 1) := by
      intro y
      rw [hπαt, Scheme.Hom.finrank_comp_left_of_isIso]
      have sq : IsPullback (𝟙 _)
          (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)) ≫
            (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom)
          (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)))
          (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).inv :=
        IsPullback.of_horiz_isIso ⟨by simp only [Category.id_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]⟩
      rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ sq]
      exact (Scheme.Hom.finrank_pullbackMap_of_comp_eq _ _ _ _ hαc _).trans (hrka _)
    rcases AlgebraicGeometry.Scheme.Modules.nonempty_pullback_normModule_iso
      (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ)) (if ℓ ∣ M then ℓ else ℓ + 1) hd
      (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom
      (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)))
      (BaseChange.κ (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom
      (IsPullback.of_horiz_isIso ⟨sqα⟩)
      (((hD.poincare.pullbackAlong a).isInvertible).pullback
        (curveChange πβ.1 πβ.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ))) with ⟨e4⟩

    have hi : cls ((Scheme.Modules.pullback (BaseChange.κ (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ))).hom).obj
        (Scheme.Modules.normModule (curveChange πα.1 πα.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ))
          (if ℓ ∣ M then ℓ else ℓ + 1)
          ((Scheme.Modules.pullback (curveChange πβ.1 πβ.2 (specMap ℚ (AlgebraicClosure ℚ) ≫ specMap (R p) ℚ))).obj
            (hD.poincare.pullbackAlong a).L))) =
        cls (Scheme.Modules.normModule
          (curveChange (curveChange πα.1 πα.2 (specMap (R p) ℚ)) hαc (specMap ℚ (AlgebraicClosure ℚ)))
          (if ℓ ∣ M then ℓ else ℓ + 1)
          ((Scheme.Modules.pullback
            (curveChange (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hβc (specMap ℚ (AlgebraicClosure ℚ)))).obj
            (hDQ.poincare.pullbackAlong (liftPt D ℚ (specMap ℚ (AlgebraicClosure ℚ)) a)).L)) := by
      rw [cls_congr e4]
      apply cls_normModule_congr
      rw [cls_pullback_comp, cls_pullback_congr_hom sqβ, ← cls_pullback_comp,
        cls_pullback_congr (curveChange (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hβc (specMap ℚ (AlgebraicClosure ℚ)))
          (cls_congr e2)]
    refine (cls_eq_iff _ _).1 ?_
    rw [cls_congr e1, cls_pullback_congr _ (cls_congr e3), Scheme.Modules.rigidify_def, Scheme.Modules.rigidify_def,
      cls_pullback_tensor, cls_tensor, hi]
    congr 1
    rw [cls_pullback_comp, cls_pullback_congr_hom (BaseChange.κ_hom_snd (toBase p (ΓM M H) hj) ℚ (specMap ℚ (AlgebraicClosure ℚ)))]
    apply cls_pullback_congr
    refine cls_congr (Scheme.Modules.dualMapIso (isoOfClsEq ?_))
    rw [cls_pullback_congr_hom (BaseChange.rigSection_κ_hom (toBase p (ΓM M H) hj) 𝔛.εinf ℚ (specMap ℚ (AlgebraicClosure ℚ))).symm,
      ← cls_pullback_comp,
      cls_pullback_congr (rigSection (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ))
        (sectionBaseChange ℚ 𝔛.εinf)) hi]

  have hfd' := ModularCurve.finiteDimensional_adjoin_of_coe_eq_coeffEmb_jq_of_eq_laurentBaseChange
    (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hTroof ℚ
    (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) (GenCodim.laurentBaseChange_rat _).symm
    (jAt (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) rfl
  have hMeta' := ModularCurve.exists_curveModel_iso_genericFibre_galoisCompat_chartPin_twoChartIntegralModel
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) p
      (jAt (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ?htj ?hfd
      (fun x hx => ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC _ x hx)
  case htj =>

    rintro ⟨f, hf0, hf⟩
    refine ModularCurve.transcendental_jqModC ℚ ⟨f, hf0, ?_⟩
    have h1 := congrArg (SubringClass.subtype (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))) hf
    rw [map_zero, Polynomial.aeval_def, Polynomial.hom_eval₂] at h1
    rw [Polynomial.aeval_def]
    convert h1 using 2 <;> first | rfl | exact Subsingleton.elim _ _
  case hfd => convert hfd' <;> exact Subsingleton.elim _ _
  obtain ⟨Meta', eeta', hisoη', heeta', -, hne', hpin'⟩ := hMeta'
  haveI := hisoη'
  let eη' := eeta' ≫ kQ₂'
  have heη' : eη' ≫ pullback.snd (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) =
      Meta'.toBase := by
    simp only [eη', kQ₂', Category.assoc, pullback.lift_snd]; exact heeta'

  let pts' := pts.trans (liftEquiv D ℚ (specMap ℚ (AlgebraicClosure ℚ)) hgen)
  have e1 : ∀ y, (pts' y).1 ≫ pullback.fst D.toBase (specMap (R p) ℚ) = (pts y).1 := fun y =>
    liftEquiv_apply_fst D ℚ (specMap ℚ (AlgebraicClosure ℚ)) hgen (pts y)
  have e2 : ∀ y, (pts' y).1 ≫ pullback.snd D.toBase (specMap (R p) ℚ) = specMap ℚ (AlgebraicClosure ℚ) := fun y =>
    (pts' y).2
  have hadd' : ∀ x y : JH M H, pts' (x + y) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDQ).mul _ (pts' x) (pts' y) := by
    intro x y
    show liftEquiv D ℚ _ hgen (pts (x + y)) =
      (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hDQ).mul _
        (liftEquiv D ℚ _ hgen (pts x)) (liftEquiv D ℚ _ hgen (pts y))
    rw [hpts_add, liftEquiv_apply, liftEquiv_apply, liftEquiv_apply, ← mul_castBase,
      liftPt_mul _ _ D hD ℚ hDQ hPQ]
  have hnorm' : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) _ =
        Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫ (sectionBaseChange ℚ 𝔛.εinf).1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := xHFunctionFieldBar M H),
        (Dv : Divisor (AlgebraicClosure ℚ) (xHFunctionFieldBar M H)) =
          Finsupp.single (𝔛.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔛.Meta.pointEquivPlace s) 1 ∧
        (pts' (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) _ ≫ ajQ.1 := by
    intro x s hs
    have hs' : s.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) = genPt p ≫ 𝔛.εinf.1 := by
      have := congrArg (· ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) hs
      simp only [eη, Category.assoc, sectionBaseChange_coe_fst] at this
      rw [reassoc_of% hkQ'₁, hkQ₁] at this
      rw [this, hgen, Category.assoc]
    obtain ⟨Dv, hDv, hpts⟩ := hpts_aj x s hs'
    refine ⟨Dv, hDv, ?_⟩
    apply pullback.hom_ext
    · rw [e1, hpts, hajbar]
      simp only [eη, Category.assoc]
      rw [reassoc_of% hkQ'₁]
    · rw [e2]
      symm
      simp only [eη, Category.assoc]
      have h2 : ajQ.1 ≫ pullback.snd D.toBase (specMap (R p) ℚ) = baseChange (R p) (toBase p (ΓM M H) hj) ℚ := ajQ.2
      have h3 : pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (specMap ℚ (AlgebraicClosure ℚ)) ≫
          baseChange (R p) (toBase p (ΓM M H) hj) ℚ = pullback.snd _ _ ≫ specMap ℚ (AlgebraicClosure ℚ) := pullback.condition
      rw [h2, h3, reassoc_of% hkQ'₂, reassoc_of% 𝔛.heeta, reassoc_of% x.2]

  obtain ⟨h0, hαI, hβI, hPD, hfin, hFI, hN⟩ := hIn
  haveI := hPD
  have hfinβ : FiniteAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) := by
    have hv := ModularCurve.finrankAlong_heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ
    have hpos : 0 < AlgebraicCurve.finrankAlong (AlgebraicClosure ℚ) (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) := by
      rw [hv]; split_ifs <;> have := (Fact.out : ℓ.Prime).pos <;> omega
    unfold AlgebraicCurve.FiniteAlong
    unfold AlgebraicCurve.finrankAlong at hpos
    letI := (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ).toRingHom.toAlgebra
    exact Module.finite_of_finrank_pos hpos
  have hop : ∀ x : JH M H, heckeOperatorHAlong (AlgebraicClosure ℚ) M H ℓ x =
      Pic0.correspondence (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ)
        hβI hαI hFI hfin hN x := by
    intro x
    rw [heckeOperatorHAlong_eq h0 hαI hβI hFI hfin hN]
    rfl

  have hyx_of : ∀ (π : SchemeHomOver (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (toBase p (ΓM M H) hj))
      (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta'.C // q ≫ Meta'.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ) _ ≫ curveChange π.1 π.2 (specMap (R p) ℚ) =
        x.1 ≫ eη ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) _ →
      x.1 ≫ 𝔛.eeta ≫ pullback.fst (toBase p (ΓM M H) hj) (genPt p) =
        y.1 ≫ eeta' ≫ pullback.fst _ _ ≫ π.1 := by
    intro π y x hyx
    have := congrArg (· ≫ pullback.fst (toBase p (ΓM M H) hj) (specMap (R p) ℚ)) hyx
    simp only [eη, eη', kQ₂', Category.assoc, curveChange_fst, pullback.lift_fst_assoc] at this
    rw [reassoc_of% hkQ'₁, hkQ₁, reassoc_of% hkQ₂₁] at this
    exact this.symm
  have hplaceα : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta'.C // q ≫ Meta'.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ) _ ≫ curveChange πα.1 πα.2 (specMap (R p) ℚ) =
        x.1 ≫ eη ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) _ →
      𝔛.Meta.pointEquivPlace x = Place.restrictAlong
        (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hαI (Meta'.pointEquivPlace y) := by
    intro y x hyx
    refine AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin (R p) (AlgebraicClosure ℚ)
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) (jAt (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj)
      _ _ 𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty (fun a => rfl) Meta' eeta' heeta' hne' (fun b => rfl)
      πα.1 πα.2 ια hchα (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) ?_ hαI hfin y x (hyx_of πα y x hyx)
    intro a
    apply Subtype.ext
    exact ((coe_heckeAlphaHBar M H ℓ _).trans (𝔛.Meta_pin a)).trans
      (((hpin' (ια a)).trans (congrArg (fun t : LaurentSeries ℚ => coeffEmb (AlgebraicClosure ℚ) t) (hια a)))).symm
  have hplaceβ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Meta'.C // q ≫ Meta'.toBase = 𝟙 _})
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y.1 ≫ eη' ≫ pullback.fst (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ) _ ≫ curveChange πβ.1 πβ.2 (specMap (R p) ℚ) =
        x.1 ≫ eη ≫ pullback.fst (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) _ →
      𝔛.Meta.pointEquivPlace x = Place.restrictAlong
        (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβI (Meta'.pointEquivPlace y) := by
    intro y x hyx
    refine AlgebraicCurve.TwoChartIntegralModel.pointEquivPlace_eq_restrictAlong_of_chartPin (R p) (AlgebraicClosure ℚ)
      ↥(qExpFunctionFieldC ℚ (ΓM M H)) (jAt (ΓM M H) hj)
      ↥(qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ))) (jAt (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj)
      _ _ 𝔛.Meta 𝔛.eeta 𝔛.heeta 𝔛.Meta_chart_nonempty (fun a => rfl) Meta' eeta' heeta' hne' (fun b => rfl)
      πβ.1 πβ.2 ιβ hchβ (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) ?_ hβI hfinβ y x (hyx_of πβ y x hyx)
    intro a
    apply Subtype.ext
    refine ((coe_heckeBetaHBar M H ℓ h0 _).trans (congrArg (qExpand (AlgebraicClosure ℚ) ℓ) (𝔛.Meta_pin a))).trans ?_
    refine (((hpin' (ιβ a)).trans (congrArg (fun t : LaurentSeries ℚ => coeffEmb (AlgebraicClosure ℚ) t) (hιβ a))).trans
      (L3bAsm.coeffEmb_qExpandH (AlgebraicClosure ℚ) ℓ _)).symm

  intro x
  have key := ModularCurve.XH.pic0Correspondence_pts_eq_comp_of_poincare_pullbackAlong_iso_laurentBaseChange ℚ M H
    (baseChange (R p) (toBase p (ΓM M H) hj) ℚ) (sectionBaseChange ℚ 𝔛.εinf) (D.baseChange ℚ) hDQ ajQ hajQε hajQ
    𝔛.Meta eη heη (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)))
    (pullback (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) (specMap (R p) ℚ))
    (baseChange (R p) (toBase p (CohCarrier.GammaH M H ⊓ CongruenceSubgroup.Gamma0 (M * ℓ)) hj) ℚ)
    (curveChange πα.1 πα.2 (specMap (R p) ℚ)) (curveChange πβ.1 πβ.2 (specMap (R p) ℚ)) hαc hβc
    (if ℓ ∣ M then ℓ else ℓ + 1) hrka φη hφpt hφadd Meta' eη' heη'
    (heckeAlphaHBar (AlgebraicClosure ℚ) M H ℓ) hαI (heckeBetaHBar (AlgebraicClosure ℚ) M H ℓ) hβI
    hplaceα hplaceβ (hPD := hPD) hFI hfin hN pts' hadd' hnorm' x
  rw [hop]
  calc (pts _).1 = (pts' _).1 ≫ pullback.fst D.toBase (specMap (R p) ℚ) := (e1 _).symm
    _ = ((pts' x).1 ≫ φη.1) ≫ pullback.fst D.toBase (specMap (R p) ℚ) :=
          congrArg (· ≫ pullback.fst D.toBase (specMap (R p) ℚ)) key
    _ = (pts x).1 ≫ Tℓ.1 := by rw [Category.assoc, hφfst, ← Category.assoc, e1]

end S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne
end P2MW
export P2MW.S_ModularCurve_XHDRModelAtP_exists_hom_mul_and_pts_heckeOperatorHAlong_eq_comp_of_ne (solution)
