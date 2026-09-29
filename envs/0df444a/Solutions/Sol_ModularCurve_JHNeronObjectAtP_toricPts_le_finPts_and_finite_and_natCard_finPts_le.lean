-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.toricPts_le_finPts_and_finite_and_natCard_finPts_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/5d57b5e6-586a-5212-a710-c4f6242d5359

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
import Theorems.Thm_ValuationSubring_addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder
import Theorems.Thm_AlgebraicGeometry_finite_torsion_of_isProper_of_smooth
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import Theorems.Thm_ValuationSubring_henselianLocalRing_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_finite_and_natCard_sections_le_of_finrank_specialFibre_le
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_isFinite_schemeKerStr_special_and_finrank_eq_mul_sq
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_natCard_finPts_eq_natCard_sections_schemeKer
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_schemeKerStr_baseChange_props
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_finPts_and_finite_and_natCard_finPts_le
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ"
p2m_attr_erase "instance" "PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "ModularCurve.JZeroNeronAtPData.mk.sizeOf_spec ModularCurve.JZeroNeronAtPData.mk.injEq AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply"
p2m_attr_erase "simp" "AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty"
p2m_attr_erase "simp" "AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec"
p2m_attr_erase "simp" "DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP ModularCurve.JHNeronObjectAtP

noncomputable section

namespace BLPCount

section ToricLeFinite

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem convPow_eq_one (t m : ℕ) (χ : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)) :
    χ ^ m = 1 := by

  have hmul : ∀ (φ ψ : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)) (g : Fin t → ZMod m),
      (φ * ψ).ofConv (AddMonoidAlgebra.single g 1) =
        φ.ofConv (AddMonoidAlgebra.single g 1) * ψ.ofConv (AddMonoidAlgebra.single g 1) := by
    intro φ ψ g
    change (φ * ψ) (AddMonoidAlgebra.single g 1) = _
    rw [AlgHom.convMul_apply]
    erw [AddMonoidAlgebra.comul_single]
    simp
  have hpow : ∀ (k : ℕ) (g : Fin t → ZMod m),
      (χ ^ k).ofConv (AddMonoidAlgebra.single g 1) = χ.ofConv (AddMonoidAlgebra.single g 1) ^ k := by
    intro k g
    induction k with
    | zero =>
        rw [pow_zero, pow_zero]
        change (1 : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)) (AddMonoidAlgebra.single g 1) = 1
        rw [AlgHom.convOne_apply]
        erw [AddMonoidAlgebra.counit_single]
        simp
    | succ k ih => rw [pow_succ, hmul, ih, pow_succ]
  apply WithConv.ext
  refine AddMonoidAlgebra.algHom_ext (fun g => ?_) (Subsingleton.elim _ _)
  change (χ ^ m).ofConv (AddMonoidAlgebra.single g 1) =
    (1 : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv (AddMonoidAlgebra.single g 1)
  rw [hpow]
  change _ = (1 : WithConv (muCoord ↥A t m →ₐ[↥A] AlgebraicClosure ℚ)) (AddMonoidAlgebra.single g 1)
  rw [AlgHom.convOne_apply]
  erw [AddMonoidAlgebra.counit_single]
  simp only [CommSemiring.counit_apply, map_one]

  rw [← map_pow]
  change χ.ofConv (AddMonoidAlgebra.single g 1 ^ m) = 1
  rw [AddMonoidAlgebra.single_pow, one_pow]
  have hg : m • g = 0 := by
    ext i
    simp
  rw [hg]
  exact map_one χ.ofConv

theorem toricPts_le_finPts (O : JHNeronObjectAtP p M H hpM A hA Λ) (m : ℕ) :
    O.toricPts m ≤ O.finPts m := by
  by_cases hm : 0 < m
  swap
  · rw [JHNeronObjectAtP.toricPts, dif_neg hm]
    exact bot_le
  obtain ⟨hhom, -, hmem, -⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard
      p M H hpM A hA Λ O m hm
  intro x hx
  obtain ⟨χ, rfl⟩ := (hmem x).1 hx
  refine AddSubgroup.subset_closure ⟨?_, ?_⟩
  ·
    have h1 : O.toricPoint m hm
        (1 : WithConv (muCoord ↥A O.toricRank m →ₐ[↥A] AlgebraicClosure ℚ)).ofConv = 0 := by
      have := hhom 1 1
      rw [mul_one] at this
      simpa using this
    have hk : ∀ k : ℕ, O.toricPoint m hm ((WithConv.toConv χ) ^ k).ofConv = k • O.toricPoint m hm χ := by
      intro k
      induction k with
      | zero => rw [pow_zero, h1, zero_nsmul]
      | succ k ih => rw [pow_succ, hhom, ih, succ_nsmul]
    rw [AlgebraicCurve.Pic0.mem_torsion, natCast_zsmul, ← hk, convPow_eq_one]
    exact h1
  ·
    have hfin : ∀ g : Fin O.toricRank → ZMod m, IsOfFinAddOrder g := fun g => by

      refine (isOfFinAddOrder_iff_nsmul_eq_zero).2 ⟨m, hm, ?_⟩
      ext i
      haveI : NeZero m := ⟨hm.ne'⟩
      simp
    obtain ⟨-, χA, hχA⟩ := ValuationSubring.addMonoidAlgebra_algHom_apply_mem_of_isOfFinAddOrder A hfin χ
    refine ⟨⟨Spec.map (CommRingCat.ofHom χA.toRingHom) ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA, ?_⟩, ?_⟩
    ·
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc (O.toricLift m hm).1,
        (O.toricLift m hm).2, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
      have : χA.toRingHom.comp (algebraMap (↥A) (muCoord (↥A) O.toricRank m)) = RingHom.id _ := by
        rw [AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap]; rfl
      rw [this, CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
    ·
      rw [JHNeronObjectAtP.toricPoint, Equiv.apply_symm_apply]
      change (muPt A O.toricRank m χ).1 ≫ (O.toricLift m hm).1 ≫ pullback.fst O.g Λ.σA = _
      have hχ : χ.toRingHom = A.subtype.comp χA.toRingHom :=
        RingHom.ext fun x => (hχA x).symm
      change Spec.map (CommRingCat.ofHom χ.toRingHom) ≫ _ = _
      rw [hχ, CommRingCat.ofHom_comp, Spec.map_comp]
      simp only [Category.assoc]

end ToricLeFinite

section GenericFinite

variable {p : ℕ}

theorem toFibrePt_coe {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (x : SchemeHomOver ι f) :
    (toFibrePt x).1 = pullback.lift x.1 (𝟙 _) (by rw [Category.id_comp]; exact x.2) := rfl

def fibrePtEquiv {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    (ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)) (f : X ⟶ Spec (CommRingCat.of R)) :
    SchemeHomOver ι f ≃ SchemeHomOver (𝟙 _) (RelativeGroupLaw.baseChangeStr ι f) where
  toFun := toFibrePt
  invFun := ofFibrePt
  left_inv x := by
    apply Subtype.ext
    change (pullback.lift x.1 (𝟙 _) _) ≫ pullback.fst f ι = x.1
    rw [pullback.lift_fst]
  right_inv y := by
    apply Subtype.ext
    change pullback.lift (y.1 ≫ pullback.fst f ι) (𝟙 _) _ = y.1
    apply pullback.hom_ext
    · rw [pullback.lift_fst]
    · rw [pullback.lift_snd]; exact y.2.symm

theorem toFibrePt_mul {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x y : SchemeHomOver ι f) :
    toFibrePt (L.mul ι x y) = (L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y) := by
  rw [RelativeGroupLaw.baseChange_mul]
  change RelativeGroupLaw.baseChangePointOfBase ι (overId (L.mul ι x y)) =
    RelativeGroupLaw.baseChangePointOfBase ι (L.mul (𝟙 _ ≫ ι)
      (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (overId x)))
      (RelativeGroupLaw.baseChangePointToBase ι (RelativeGroupLaw.baseChangePointOfBase ι (overId y))))
  rw [RelativeGroupLaw.baseChangePointToBase_ofBase, RelativeGroupLaw.baseChangePointToBase_ofBase]
  congr 1

theorem finite_torsion_of_pts {X : Scheme.{0}} {f : X ⟶ base p} (L : RelativeGroupLaw (baseRing p) f)
    [Smooth f] [IsProper (pullback.snd f (genPt p))]
    {Γ : Type*} [AddCommGroup Γ] (pts : Γ ≃ SchemeHomOver (genPt p) f)
    (hadd : ∀ x y, pts (x + y) = L.mul _ (pts x) (pts y)) (N : ℕ) (hN : N ≠ 0) :
    Finite {x : Γ // N • x = 0} := by
  let K := AlgebraicClosure ℚ
  let J : Scheme.{0} := pullback f (genPt p)
  let c : J ⟶ Spec (CommRingCat.of K) := pullback.snd f (genPt p)
  let Lb : RelativeGroupLaw K c := L.baseChange (genPt p)

  let P1 : SchemeHomOver (pullback.fst c c ≫ c) c := ⟨pullback.fst c c, rfl⟩
  let P2 : SchemeHomOver (pullback.fst c c ≫ c) c := ⟨pullback.snd c c, pullback.condition.symm⟩
  let mul : pullback c c ⟶ J := (Lb.mul _ P1 P2).1
  let pts' : Γ ≃ SchemeHomOver (𝟙 _) c := pts.trans (fibrePtEquiv (genPt p) f)
  have hmulpt : ∀ u v : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) c,
      (Lb.mul _ u v).1 = pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ mul := by
    intro u v
    have hψ : pullback.lift u.1 v.1 (u.2.trans v.2.symm) ≫ (pullback.fst c c ≫ c) = 𝟙 _ := by
      rw [← Category.assoc, pullback.lift_fst]; exact u.2
    have h1 : schemeHomOverComp _ hψ P1 = u := Subtype.ext (pullback.lift_fst _ _ _)
    have h2 : schemeHomOverComp _ hψ P2 = v := Subtype.ext (pullback.lift_snd _ _ _)
    have := Lb.mul_natural _ _ _ hψ P1 P2
    rw [h1, h2] at this
    rw [← this]
    rfl
  have hadd' : ∀ x y : Γ, (pts' (x + y)).1 =
      pullback.lift (pts' x).1 (pts' y).1 ((pts' x).2.trans (pts' y).2.symm) ≫ mul := by
    intro x y
    rw [← hmulpt]
    change (toFibrePt (pts (x + y))).1 = _
    rw [hadd, toFibrePt_mul]
    rfl
  have hK : (N : K) ≠ 0 := Nat.cast_ne_zero.2 hN
  exact AlgebraicGeometry.finite_torsion_of_isProper_of_smooth K J c inferInstance inferInstance mul Γ pts' hadd' N hK

theorem isProper_pullback_snd_genPt {X : Scheme.{0}} (f : X ⟶ base p)
    [IsProper (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))))] :
    IsProper (pullback.snd f (genPt p)) := by
  let ιQ : Spec (CommRingCat.of ℚ) ⟶ base p := Spec.map (CommRingCat.ofHom (algebraMap (baseRing p) ℚ))
  let j : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Spec (CommRingCat.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ)))
  have hgen : j ≫ ιQ = genPt p := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    first
      | rfl
      | (congr 2; exact (IsScalarTower.algebraMap_eq _ _ _).symm)
      | (congr 2; ext x; simp [IsScalarTower.algebraMap_apply])
  have h : IsProper (pullback.snd f (j ≫ ιQ)) := by
    rw [← pullbackLeftPullbackSndIso_inv_snd_snd f ιQ j]
    infer_instance
  rw [hgen] at h
  exact h

end GenericFinite

section FiniteTorsion

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

omit [Fact p.Prime] [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)] in

theorem finite_torsion_level (Λ : JHNeronObjectAtP.LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (N : ℕ) (hN : N ≠ 0) :
    Finite ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) N) := by
  haveI : Smooth Λ.f := hΛ.smooth
  haveI : IsProper Λ.f := hΛ.proper
  haveI : Finite {x : JH (M / p) (infSubgroup p M H hpM) // N • x = 0} :=
    finite_torsion_of_pts Λ.L Λ.pts hΛpts_add N hN
  refine Finite.of_injective (fun x : ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) N) =>
    (⟨x.1, by rw [← natCast_zsmul]; exact AlgebraicCurve.Pic0.mem_torsion.1 x.2⟩ : {x : JH (M / p) (infSubgroup p M H hpM) // N • x = 0}))
    fun x y h => Subtype.ext (by simpa using congrArg (fun z : {x : JH (M / p) (infSubgroup p M H hpM) // N • x = 0} => z.1) h)

theorem finite_finPts (O : JHNeronObjectAtP p M H hpM A hA Λ) (N : ℕ) (hN : N ≠ 0) :
    Finite ↥(O.finPts N) := by
  haveI : Smooth O.g := O.smooth
  haveI := O.proper_generic
  haveI : IsProper (pullback.snd O.g (genPt p)) := isProper_pullback_snd_genPt O.g
  haveI : Finite {x : JH M H // N • x = 0} := finite_torsion_of_pts O.L O.pts O.pts_add N hN
  have hle : O.finPts N ≤ Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar M H) N :=
    (AddSubgroup.closure_le _).2 fun x hx => hx.1
  refine Finite.of_injective (fun x : ↥(O.finPts N) =>
    (⟨x.1, by rw [← natCast_zsmul]; exact AlgebraicCurve.Pic0.mem_torsion.1 (hle x.2)⟩ : {x : JH M H // N • x = 0}))
    fun x y h => Subtype.ext (by simpa using congrArg (fun z : {x : JH M H // N • x = 0} => z.1) h)

end FiniteTorsion

section Count

theorem moduleFinite_sections_of_isFinite {R : Type} [CommRing R] {Y : Scheme.{0}} (q : Y ⟶ Spec (.of R)) [IsFinite q] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom q ⊤
    Module.Finite R Γ(Y, ⊤) := by
  have hq : IsAffine Y ∧ RingHom.Finite (q.appTop).hom := (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).1 inferInstance
  have h1 : RingHom.Finite ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop).hom := by
    rw [CommRingCat.hom_comp]
    exact RingHom.Finite.comp hq.2 (RingHom.Finite.of_surjective _ (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv.symm.surjective)
  have h2 : (Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ ⊤ le_top = (Scheme.ΓSpecIso (.of R)).inv ≫ q.appTop := by
    congr 1
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  change RingHom.Finite ((Scheme.ΓSpecIso (.of R)).inv ≫ q.appLE ⊤ ⊤ le_top).hom
  rw [h2]
  exact h1

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : JHNeronObjectAtP.LevelData p M H hpM A}

theorem natCard_finPts_le (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (m : ℕ) (hm : 0 < m) :
    Nat.card ↥(O.finPts m) ≤
      Nat.card ↥(O.toricPts m) *
        Nat.card ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) m) ^ 2 := by

  rw [ModularCurve.JHNeronObjectAtP.natCard_finPts_eq_natCard_sections_schemeKer p M H hpM A hA Λ O m]

  obtain ⟨hlft, hsep, hqc, -, hlqf, ⟨π, hπ⟩, -⟩ :=
    ModularCurve.JHNeronObjectAtP.schemeKerStr_baseChange_props p M H hpM A hA Λ O m hm

  obtain ⟨hΛfin, hΛord⟩ :=
    ModularCurve.JHNeronObjectAtP.LevelData.isFinite_schemeKerStr_special_and_finrank_eq_natCard_torsion
      p M H hpM A Λ hΛ hΛpts_add m hm

  obtain ⟨hOfin, hOord⟩ :=
    ModularCurve.JHNeronObjectAtP.isFinite_schemeKerStr_special_and_finrank_eq_mul_sq p M H hpM A hA Λ hΛ.proper O m hm hΛfin

  haveI : HenselianLocalRing ↥A := ValuationSubring.henselianLocalRing_of_isAlgClosed A
  haveI := hlft; haveI := hsep; haveI := hqc; haveI := hlqf; haveI := hOfin
  have hB := AlgebraicGeometry.finite_and_natCard_sections_le_of_finrank_specialFibre_le (AlgebraicClosure ℚ)
    ((O.L.baseChange Λ.σA).schemeKerStr m) ((O.L.baseChange (resPt A ≫ Λ.σA)).schemeKerStr m) π hπ
    (m ^ O.toricRank * Nat.card ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) m) ^ 2)
    ⟨moduleFinite_sections_of_isFinite _, by rw [hOord, hΛord]⟩

  obtain ⟨-, -, -, hcard⟩ :=
    ModularCurve.JHNeronObjectAtP.toricPoint_convMul_and_injective_and_mem_toricPts_iff_and_natCard p M H hpM A hA Λ O m hm
  rw [hcard]
  exact hB.2

end Count

end BLPCount

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (n : ℕ) :
    O.toricPts (p ^ n) ≤ O.finPts (p ^ n) ∧
    Finite ↥(O.finPts (p ^ n)) ∧
    Finite ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (p ^ n)) ∧
    Nat.card ↥(O.finPts (p ^ n)) ≤
      Nat.card ↥(O.toricPts (p ^ n)) *
        Nat.card ↥(Pic0.torsion (AlgebraicClosure ℚ) (xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (p ^ n)) ^ 2 := by
  have hpn : 0 < p ^ n := pow_pos (Fact.out : p.Prime).pos n
  exact ⟨BLPCount.toricPts_le_finPts O (p ^ n),
    BLPCount.finite_finPts O (p ^ n) hpn.ne',
    BLPCount.finite_torsion_level Λ hΛ hΛpts_add (p ^ n) hpn.ne',
    BLPCount.natCard_finPts_le O hΛ hΛpts_add (p ^ n) hpn⟩

end

end S_ModularCurve_JHNeronObjectAtP_toricPts_le_finPts_and_finite_and_natCard_finPts_le
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_toricPts_le_finPts_and_finite_and_natCard_finPts_le (solution)
