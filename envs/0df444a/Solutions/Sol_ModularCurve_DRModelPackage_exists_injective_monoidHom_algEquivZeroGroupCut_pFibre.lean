-- Prove2me | solution 1 for ModularCurve.DRModelPackage.exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/e9c23094-4aec-5016-9494-04d9c0a61e02

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackage
import Definitions.Def_ModularCurve_DRModelLegTwoInput
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicGeometry_TwoGluedProjectiveLines_exists_nodeRatioHom
import Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
import Theorems.Thm_AlgebraicCurve_CurveModel_finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc
import Theorems.Thm_AlgebraicCurve_TwoChartIntegralModel_locallyOfFiniteType_toBase
import Theorems.Thm_ModularCurve_DRModelPackage_not_smooth_pullback_snd_toBase_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackage_exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
p2m_attr_erase "instance" "AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk"
p2m_attr_erase "simp" "ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq"
p2m_attr_erase "simp" "DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicCurve.GluedPic0.toPic0Pair_mk AlgebraicCurve.GluedPic0.toPic0Pair_nodeUnit RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub"
p2m_attr_erase "simp" "ModularCurve.qSeriesBar_neg"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve
open scoped CategoryTheory.MonObj
p2m_open "CategoryTheory.MonoidalCategory AlgebraicCurve"

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [Fact p.Prime] (𝔛 : DRModelPackage p) (I : 𝔛.LegTwoInput)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] :
    letI := (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).commGroupObj
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
    ∃ (s : ℕ) (δ : (relSubPicPresheaf (DRModel.toBase p) 𝔛.εinf
          (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).toSubPicCondition).obj
          (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))) →*
        (Fin s → Kˣ) ⧸ (Pi.constMonoidHom (Fin s) Kˣ).range),
      Function.Injective δ := by
  classical

  haveI hred : IsReduced (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := I.hgred K (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))

  haveI : LocallyOfFiniteType (DRModel.toBase p) := by
    have hfin : Algebra.FiniteType ℤ
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
      letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartFin ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)).toRingHom.toAlgebra
      haveI : Module.Finite (Polynomial ℤ)
          ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
        𝔛.chartFin_finite
      haveI : IsScalarTower ℤ (Polynomial ℤ)
          ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgFin ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
        IsScalarTower.of_algebraMap_eq fun r => by
          rw [RingHom.algebraMap_toAlgebra]
          exact (AlgHom.commutes _ r).symm
      exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ (Polynomial ℤ))
        (Module.Finite.finiteType _)
    have hinf : Algebra.FiniteType ℤ
        ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) := by
      letI := (AlgebraicCurve.TwoChartIntegralModel.polynomialToChartInf ℤ ↥(modularFunctionFieldFull p)
        (IgusaScheme.jFull p)).toRingHom.toAlgebra
      haveI : Module.Finite (Polynomial ℤ)
          ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
        𝔛.chartInf_finite
      haveI : IsScalarTower ℤ (Polynomial ℤ)
          ↥(AlgebraicCurve.TwoChartIntegralModel.chartAlgInf ℤ ↥(modularFunctionFieldFull p) (IgusaScheme.jFull p)) :=
        IsScalarTower.of_algebraMap_eq fun r => by
          rw [RingHom.algebraMap_toAlgebra]
          exact (AlgHom.commutes _ r).symm
      exact Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType ℤ (Polynomial ℤ))
        (Module.Finite.finiteType _)
    haveI := hfin
    haveI := hinf
    exact AlgebraicCurve.TwoChartIntegralModel.locallyOfFiniteType_toBase ℤ ↥(modularFunctionFieldFull p)
      (IgusaScheme.jFull p)
  haveI : LocallyOfFiniteType (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := inferInstance

  have extract : ∀ N : RigidifiedLineBundle (DRModel.toBase p) 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))),
      (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf).P (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) N → IsAlgEquivZero (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) N.L := by
    intro N hN
    have h1 := hN K (𝟙 _)

    let e : (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) ⟶ pullback (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) (𝟙 (Spec (CommRingCat.of K))) :=
      pullback.lift (𝟙 _) (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) (by simp)
    have he : e ≫ fibreAt (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) (𝟙 _) = (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := pullback.lift_snd _ _ _
    have h2 := IsAlgEquivZero.pullback e he h1
    refine IsAlgEquivZero.of_iso ?_ h2
    have hef : e ≫ pullback.fst (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) (𝟙 (Spec (CommRingCat.of K))) = 𝟙 _ := pullback.lift_fst _ _ _
    exact (Scheme.Modules.pullbackComp e (pullback.fst (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) (𝟙 (Spec (CommRingCat.of K))))).app N.L ≪≫
      (Scheme.Modules.pullbackCongr hef).app N.L ≪≫ (Scheme.Modules.pullbackId _).app N.L

  have hns : ¬ Smooth (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) := ModularCurve.DRModelPackage.not_smooth_pullback_snd_toBase_of_charP p 𝔛 K
  obtain ⟨M₁, M₂, i₁, i₂, hci₁, hci₂, n, a, b, 𝒲₀, hi₁, hi₂, hcover, ha, hnode, hinter, htrans, hU0₁, hU0₂,
    hU1₁, hU1₂, -, -, -, -⟩ := I.hbad K (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) hns
  haveI := hci₁
  haveI := hci₂

  let cov : ∀ {M : CurveModel K (RatFunc K)} (i : M.C ⟶ (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))) [IsClosedImmersion i],
      M.C.TwoAffineOpenCover := fun {M} i _ =>
    { U0 := i ⁻¹ᵁ 𝒲₀.U0
      U1 := i ⁻¹ᵁ 𝒲₀.U1
      isAffineOpen_U0 := 𝒲₀.isAffineOpen_U0.preimage i
      isAffineOpen_U1 := 𝒲₀.isAffineOpen_U1.preimage i
      sup_eq_top := by
        have : i ⁻¹ᵁ 𝒲₀.U0 ⊔ i ⁻¹ᵁ 𝒲₀.U1 = i ⁻¹ᵁ (𝒲₀.U0 ⊔ 𝒲₀.U1) := rfl
        rw [this, 𝒲₀.sup_eq_top]
        rfl
      isAffineOpen_inf := by
        have : i ⁻¹ᵁ 𝒲₀.U0 ⊓ i ⁻¹ᵁ 𝒲₀.U1 = i ⁻¹ᵁ (𝒲₀.U0 ⊓ 𝒲₀.U1) := rfl
        rw [this]
        exact 𝒲₀.isAffineOpen_inf.preimage i }
  have h10 : ∀ (M : CurveModel K (RatFunc K)) (𝒲 : M.C.TwoAffineOpenCover),
      Module.finrank K (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H1 = 0 ∧
      Module.finrank K (𝒲.sectionsOf M.toBase (SheafOfModules.unit M.C.ringCatSheaf : M.C.Modules)).H0 = 1 :=
    fun M 𝒲 => AlgebraicCurve.CurveModel.finrank_H1_sectionsOf_unit_eq_zero_and_finrank_H0_eq_one_of_ratFunc K M 𝒲

  have triv : ∀ N : RigidifiedLineBundle (DRModel.toBase p) 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))), (algEquivZeroCut (DRModel.toBase p) 𝔛.εinf).P (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) N →
      Nonempty ((Scheme.Modules.pullback i₁).obj N.L ≅
        (Scheme.Modules.pullback i₁).obj (SheafOfModules.unit (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))).ringCatSheaf)) ∧
      Nonempty ((Scheme.Modules.pullback i₂).obj N.L ≅
        (Scheme.Modules.pullback i₂).obj (SheafOfModules.unit (pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))).ringCatSheaf)) := by
    intro N hN
    exact ⟨(AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
        K (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) N.L N.isInvertible (extract N hN) M₁ i₁ hi₁ (cov i₁) (h10 M₁)).1,
      (AlgebraicGeometry.RelPicard.IsAlgEquivZero.nonempty_pullback_iso_pullback_unit_and_eulerChar_eq_one_of_curveModel_ratFunc
        K (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) N.L N.isInvertible (extract N hN) M₂ i₂ hi₂ (cov i₂) (h10 M₂)).1⟩

  obtain ⟨δ, hinv, hone, hmul, hker⟩ :=
    AlgebraicGeometry.TwoGluedProjectiveLines.exists_nodeRatioHom K (pullback.snd (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))) M₁ M₂ i₁ i₂ hi₁ hi₂ hcover a b ha
      hnode hinter htrans

  let δ₀ : RigidifiedLineBundle.Classes (DRModel.toBase p) 𝔛.εinf (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))) → (Fin n → Kˣ) ⧸ (Pi.constMonoidHom (Fin n) Kˣ).range :=
    Quotient.lift (fun N => δ N.L) (fun N N' h => hinv N.L N'.L h)
  letI := (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).commGroupObj (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))))
  let δbar : (relSubPicPresheaf (DRModel.toBase p) 𝔛.εinf (algEquivZeroGroupCut (DRModel.toBase p) 𝔛.εinf).toSubPicCondition).obj
      (Opposite.op (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℤ K))))) →* (Fin n → Kˣ) ⧸ (Pi.constMonoidHom (Fin n) Kˣ).range :=
    { toFun := fun ξ => δ₀ ξ.1
      map_one' := by
        show δ (RigidifiedLineBundle.unit (Spec.map (CommRingCat.ofHom (algebraMap ℤ K)))).L = 1
        exact hone
      map_mul' := by
        rintro ⟨q, hq⟩ ⟨r, hr⟩
        induction q using Quotient.ind with
        | _ M =>
        induction r using Quotient.ind with
        | _ N =>
        show δ (M.L ⊗ N.L) = δ M.L * δ N.L
        exact hmul M.L N.L M.isInvertible N.isInvertible (triv M hq).1 (triv M hq).2 (triv N hr).1 (triv N hr).2 }
  refine ⟨n, δbar, (injective_iff_map_eq_one δbar).mpr ?_⟩
  rintro ⟨q, hq⟩ hξ
  induction q using Quotient.ind with
  | _ M =>
  obtain ⟨e⟩ := hker M.L M.isInvertible (triv M hq).1 (triv M hq).2 hξ
  exact Subtype.ext (Quotient.sound ⟨e⟩)

end S_ModularCurve_DRModelPackage_exists_injective_monoidHom_algEquivZeroGroupCut_pFibre
end P2MW
export P2MW.S_ModularCurve_DRModelPackage_exists_injective_monoidHom_algEquivZeroGroupCut_pFibre (solution)
