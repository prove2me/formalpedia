-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/31098753-f6a8-51c4-9ed4-aa8d3db48311

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawTranslate
import Definitions.Def_GoodReductionJacobian_NsmulEigenSubdatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_SheafOfModules_MonoidalV2
import Definitions.Def_AlgebraicGeometry_ModulesTensorPowV2
import Definitions.Def_AlgebraicGeometry_ModulesSectionsTensorV2
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor

import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_hopfAlgebra_torsion_finrank_eq_pow_and_nsmulAlgHom_eq
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_flat_etale_schemeKerStr_of_isUnit
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset
import Theorems.Thm_Algebra_isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_isReduced_of_etale
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
p2m_attr_erase "instance" "GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions"
p2m_attr_erase "instance" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime"
p2m_attr_erase "simp" "NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra~schemeHomOverComp GoodReductionJacobian"

universe u

namespace C1Body

section RepTheory

open Classical

variable {K : Type*} [Field K] {G : Type*} [CommGroup G] [Fintype G]
  {V : Type*} [AddCommGroup V] [Module K V]
  (ρ : G → (V →ₗ[K] V)) (hρ1 : ρ 1 = LinearMap.id) (hρmul : ∀ x y, ρ (x * y) = (ρ x).comp (ρ y))

def eig (φ : G →* Kˣ) : Submodule K V where
  carrier := {v | ∀ x, ρ x v = ((φ x : Kˣ) : K) • v}
  zero_mem' := fun x => by simp
  add_mem' := fun {v w} hv hw x => by
    change ρ x (v + w) = _ • (v + w)
    rw [map_add, hv x, hw x, smul_add]
  smul_mem' := fun c v hv x => by
    change ρ x (c • v) = _ • (c • v)
    rw [LinearMap.map_smul, hv x, smul_comm]

theorem mem_eig (φ : G →* Kˣ) (v : V) : v ∈ eig ρ φ ↔ ∀ x, ρ x v = ((φ x : Kˣ) : K) • v := Iff.rfl

theorem sum_eq_zero_of_mul_eq {S c : K} (h : c * S = S) (hc : c ≠ 1) : S = 0 := by
  have h2 : (c - 1) * S = 0 := by rw [sub_mul, one_mul, h, sub_self]
  rcases mul_eq_zero.1 h2 with h3 | h3
  · exact absurd (sub_eq_zero.1 h3) hc
  · exact h3

theorem sum_char_eq_zero (φ : G →* Kˣ) (hφ : φ ≠ 1) : ∑ x : G, ((φ x : Kˣ) : K) = 0 := by
  obtain ⟨y, hy⟩ : ∃ y, φ y ≠ 1 := by
    by_contra h; push_neg at h; exact hφ (MonoidHom.ext h)
  refine sum_eq_zero_of_mul_eq ?_ (fun h => hy (Units.ext h))
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun x => y * x) (Group.mulLeft_bijective y) _ _ fun x => ?_
  rw [map_mul, Units.val_mul]

variable [Fintype (G →* Kˣ)]

theorem sum_dual_eq_zero [HasEnoughRootsOfUnity K (Monoid.exponent G)] (x : G) (hx : x ≠ 1) :
    ∑ φ : G →* Kˣ, ((φ x : Kˣ) : K) = 0 := by
  obtain ⟨ψ, hψ⟩ := CommGroup.exists_apply_ne_one_of_hasEnoughRootsOfUnity G K hx
  refine sum_eq_zero_of_mul_eq ?_ (fun h => hψ (Units.ext h))
  rw [Finset.mul_sum]
  refine Fintype.sum_bijective (fun φ => ψ * φ) (Group.mulLeft_bijective ψ) _ _ fun φ => ?_
  rw [MonoidHom.mul_apply, Units.val_mul]

theorem card_dual [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Fintype.card (G →* Kˣ) = Fintype.card G := by
  have := CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity G K
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

theorem sum_dual_inv_apply [HasEnoughRootsOfUnity K (Monoid.exponent G)] [DecidableEq G] (x : G) :
    ∑ φ : G →* Kˣ, (((φ x)⁻¹ : Kˣ) : K) = if x = 1 then (Fintype.card G : K) else 0 := by
  split_ifs with hx
  · subst hx; simp [card_dual]
  · have : ∑ φ : G →* Kˣ, (((φ x)⁻¹ : Kˣ) : K) = ∑ φ : G →* Kˣ, ((φ x⁻¹ : Kˣ) : K) :=
      Finset.sum_congr rfl fun φ _ => by rw [map_inv]
    rw [this]
    exact sum_dual_eq_zero x⁻¹ (fun h => hx (inv_eq_one.1 h))

variable (hcard : (Fintype.card G : K) ≠ 0)

noncomputable def proj (φ : G →* Kˣ) : V →ₗ[K] V :=
  (Fintype.card G : K)⁻¹ • ∑ x : G, (((φ x)⁻¹ : Kˣ) : K) • ρ x

theorem proj_apply (φ : G →* Kˣ) (v : V) :
    proj ρ φ v = (Fintype.card G : K)⁻¹ • ∑ x : G, (((φ x)⁻¹ : Kˣ) : K) • ρ x v := by
  simp only [proj, LinearMap.smul_apply, LinearMap.sum_apply]

include hρmul in
theorem proj_mem (φ : G →* Kˣ) (v : V) : proj ρ φ v ∈ eig ρ φ := by
  intro y
  rw [proj_apply, LinearMap.map_smul, smul_comm (((φ y : Kˣ) : K))]
  congr 1
  rw [map_sum, Finset.smul_sum]

  have ha : ∀ x, ρ y ((((φ x)⁻¹ : Kˣ) : K) • ρ x v) = (((φ x)⁻¹ : Kˣ) : K) • ρ (y * x) v := fun x => by
    rw [LinearMap.map_smul, hρmul, LinearMap.comp_apply]
  rw [Finset.sum_congr rfl (fun x _ => ha x)]
  refine Fintype.sum_bijective (fun x => y * x) (Group.mulLeft_bijective y) _ _ fun x => ?_

  rw [smul_smul, ← Units.val_mul]
  congr 2
  rw [map_mul, mul_inv, ← mul_assoc, mul_inv_cancel, one_mul]

include hρ1 hcard in
theorem sum_proj [HasEnoughRootsOfUnity K (Monoid.exponent G)] (v : V) : ∑ φ : G →* Kˣ, proj ρ φ v = v := by
  classical
  simp only [proj_apply]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have : ∀ x : G, ∑ φ : G →* Kˣ, (((φ x)⁻¹ : Kˣ) : K) • ρ x v = if x = 1 then (Fintype.card G : K) • ρ x v else 0 := by
    intro x
    rw [← Finset.sum_smul, sum_dual_inv_apply]
    split_ifs <;> simp
  simp only [this, Finset.sum_ite_eq', Finset.mem_univ, if_true, hρ1, LinearMap.id_apply, smul_smul,
    inv_mul_cancel₀ hcard, one_smul]

include hcard in
theorem proj_of_mem [HasEnoughRootsOfUnity K (Monoid.exponent G)]
    (φ ψ : G →* Kˣ) (v : V) (hv : v ∈ eig ρ ψ) :
    proj ρ φ v = if φ = ψ then v else 0 := by
  classical
  rw [proj_apply]
  by_cases h : φ = ψ
  · subst h
    have : ∀ x : G, (((φ x)⁻¹ : Kˣ) : K) • ρ x v = v := by
      intro x; rw [hv x, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
    simp only [this, Finset.sum_const, Finset.card_univ, if_true]
    rw [← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  · have : ∀ x : G, (((φ x)⁻¹ : Kˣ) : K) • ρ x v = (((φ⁻¹ * ψ) x : Kˣ) : K) • v := by
      intro x; rw [hv x, smul_smul, MonoidHom.mul_apply, MonoidHom.inv_apply, Units.val_mul]
    simp only [this, ← Finset.sum_smul, smul_smul]
    have hne : φ⁻¹ * ψ ≠ 1 := fun h' => h (inv_mul_eq_one.1 h')
    rw [sum_char_eq_zero (φ⁻¹ * ψ) hne, mul_zero, zero_smul, if_neg h]

include hρ1 hρmul hcard in

theorem bijective_sum_eig [HasEnoughRootsOfUnity K (Monoid.exponent G)] :
    Function.Bijective (fun v : (φ : G →* Kˣ) → eig ρ φ => ∑ φ, (v φ).1) := by
  classical
  have key : ∀ (v : (φ : G →* Kˣ) → eig ρ φ) (ψ : G →* Kˣ), proj ρ ψ (∑ φ, (v φ).1) = (v ψ).1 := by
    intro v ψ
    rw [map_sum]
    have : ∀ φ, proj ρ ψ (v φ).1 = if ψ = φ then (v φ).1 else 0 := fun φ => proj_of_mem ρ hcard ψ φ _ (v φ).2
    simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  constructor
  · intro v w hvw
    funext ψ
    apply Subtype.ext
    rw [← key v ψ, ← key w ψ]
    exact congrArg (proj ρ ψ) hvw
  · intro v
    exact ⟨fun φ => ⟨proj ρ φ v, proj_mem ρ hρmul φ v⟩, sum_proj ρ hρ1 hcard v⟩

end RepTheory

end C1Body

namespace C1Body

section Points

p2m_open "AlgebraicGeometry AlgebraicGeometry.OModulePresheaf GoodReductionJacobian.RelativeGroupLaw"

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f) (hc : L.IsCommutative)

noncomputable def commGroupPt : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :=
  { L.pointGroup (𝟙 _) with mul_comm := fun x y => hc (𝟙 _) x y }

theorem pow_eq_nsmul (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) (k : ℕ) :
    letI := commGroupPt L hc; x ^ k = L.nsmul (𝟙 _) k x := by
  letI := commGroupPt L hc
  induction k with
  | zero => rfl
  | succ k ih => rw [pow_succ, ih]; rfl

theorem mem_torsionSubset_iff_pow (n : ℕ) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    letI := commGroupPt L hc; x ∈ L.torsionSubset (𝟙 _) n ↔ x ^ n = 1 := by
  letI := commGroupPt L hc
  rw [pow_eq_nsmul L hc]; exact Iff.rfl

noncomputable def torsionSubgroup (n : ℕ) : letI := commGroupPt L hc; Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :=
  letI := commGroupPt L hc
  { carrier := L.torsionSubset (𝟙 _) n
    one_mem' := by rw [mem_torsionSubset_iff_pow L hc]; exact one_pow n
    mul_mem' := fun {x y} hx hy => by
      rw [mem_torsionSubset_iff_pow L hc] at hx hy ⊢
      rw [mul_pow, hx, hy, _root_.one_mul]
    inv_mem' := fun {x} hx => by
      rw [mem_torsionSubset_iff_pow L hc] at hx ⊢
      rw [inv_pow, hx, inv_one] }

theorem mem_torsionSubgroup_iff (n : ℕ) (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    letI := commGroupPt L hc; x ∈ torsionSubgroup L hc n ↔ x ∈ L.torsionSubset (𝟙 _) n := Iff.rfl

noncomputable def cst (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) : SchemeHomOver f f :=
  ⟨f ≫ x.1, by rw [Category.assoc, x.2, Category.comp_id]⟩

theorem translate_eq (x : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate x = (L.mul f RelativeGroupLaw.idPoint (cst x)).1 := rfl

theorem comp_translate (φ : A ⟶ A) (hφ : φ ≫ f = f) (y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    φ ≫ L.translate y = (L.mul f ⟨φ, hφ⟩ (cst y)).1 := by
  rw [translate_eq]
  have h1 : φ ≫ (L.mul f RelativeGroupLaw.idPoint (cst y)).1 =
      (schemeHomOverComp φ hφ (L.mul f RelativeGroupLaw.idPoint (cst y))).1 := rfl
  rw [h1, L.mul_natural f f φ hφ]
  have e1 : schemeHomOverComp φ hφ RelativeGroupLaw.idPoint = (⟨φ, hφ⟩ : SchemeHomOver f f) :=
    Subtype.ext (Category.comp_id φ)
  have e2 : schemeHomOverComp φ hφ (cst y) = cst y :=
    Subtype.ext (by show φ ≫ f ≫ y.1 = f ≫ y.1; rw [← Category.assoc, hφ])
  rw [e1, e2]

theorem cst_mul (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    cst (L.mul (𝟙 _) x y) = L.mul f (cst x) (cst y) := by
  have h : cst (L.mul (𝟙 _) x y) = schemeHomOverComp f (Category.comp_id f) (L.mul (𝟙 _) x y) := Subtype.ext rfl
  rw [h, L.mul_natural (𝟙 _) f f (Category.comp_id f)]
  rfl

include hc in
theorem translate_mul (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) :
    L.translate (L.mul (𝟙 _) x y) = L.translate x ≫ L.translate y := by
  rw [comp_translate L (L.translate x) (L.translate_over x) y]
  have : (⟨L.translate x, L.translate_over x⟩ : SchemeHomOver f f) = L.mul f RelativeGroupLaw.idPoint (cst x) :=
    Subtype.ext rfl
  rw [this, L.mul_assoc, ← cst_mul]
  rfl

theorem appLE_id_eq (W : A.Opens) (e : W ≤ (𝟙 A) ⁻¹ᵁ W) : (𝟙 A : A ⟶ A).appLE W W e = 𝟙 _ := by
  have : (homOfLE e).op = 𝟙 (Opposite.op W) := Subsingleton.elim _ _
  rw [Scheme.Hom.appLE, this]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  simp

variable (n : ℕ)
  (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n)

theorem deckApp_one (U : A.Opens) (h1 : L.one (𝟙 _) ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of R))) n) :
    L.deckApp n (L.one (𝟙 _)) (hG _ h1) U = 𝟙 _ := by
  rw [deckApp_def, appLE_congr_hom (L.translate_one)]
  · exact appLE_id_eq _ _
  · change (L.schemeNsmul n) ⁻¹ᵁ U ≤ (L.schemeNsmul n) ⁻¹ᵁ U; exact le_rfl

include hc in
theorem deckApp_mul (U : A.Opens) (x y : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f)
    (hx : x ∈ L.torsionSubset (𝟙 _) n) (hy : y ∈ L.torsionSubset (𝟙 _) n) (hxy : L.mul (𝟙 _) x y ∈ L.torsionSubset (𝟙 _) n) :
    L.deckApp n (L.mul (𝟙 _) x y) (hG _ hxy) U = L.deckApp n y (hG _ hy) U ≫ L.deckApp n x (hG _ hx) U := by
  rw [deckApp_def, deckApp_def, deckApp_def, Scheme.Hom.appLE_comp_appLE]
  exact appLE_congr_hom (translate_mul L hc x y) _ _ _ _

noncomputable def rho (U : A.Opens) (x : letI := commGroupPt L hc; ↥(torsionSubgroup L hc n)) :
    (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U →ₗ[R]
      (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U where
  toFun s := (L.deckApp n x.1 (hG x.1 x.2) U).hom s
  map_add' s t := map_add _ _ _
  map_smul' r s := by
    change (L.deckApp n x.1 (hG x.1 x.2) U).hom (L.nsmulConst n U r * (show Γ(A, _) from s)) =
      L.nsmulConst n U r * (L.deckApp n x.1 (hG x.1 x.2) U).hom s
    rw [map_mul, deckApp_nsmulConst]

theorem rho_apply (U : A.Opens) (x : letI := commGroupPt L hc; ↥(torsionSubgroup L hc n))
    (s : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U) :
    rho L hc n hG U x s = (L.deckApp n x.1 (hG x.1 x.2) U).hom s := rfl

theorem rho_one (U : A.Opens) : letI := commGroupPt L hc; rho L hc n hG U 1 = LinearMap.id := by
  letI := commGroupPt L hc
  refine LinearMap.ext fun s => ?_
  rw [rho_apply]
  have h1 : ((1 : ↥(torsionSubgroup L hc n)) : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) f) = L.one (𝟙 _) := rfl
  have := deckApp_one L n hG U (h1 ▸ (1 : ↥(torsionSubgroup L hc n)).2)
  rw [show L.deckApp n (1 : ↥(torsionSubgroup L hc n)).1 (hG _ (1 : ↥(torsionSubgroup L hc n)).2) U = 𝟙 _ from this]
  rfl

theorem rho_mul (U : A.Opens) (x y : letI := commGroupPt L hc; ↥(torsionSubgroup L hc n)) :
    letI := commGroupPt L hc; rho L hc n hG U (x * y) = (rho L hc n hG U x).comp (rho L hc n hG U y) := by
  letI := commGroupPt L hc
  refine LinearMap.ext fun s => ?_
  rw [LinearMap.comp_apply, rho_apply, rho_apply, rho_apply]
  have hxy : (x * y).1 = L.mul (𝟙 _) x.1 y.1 := rfl
  have := deckApp_mul L hc n hG U x.1 y.1 x.2 y.2 (hxy ▸ (x * y).2)
  rw [show L.deckApp n (x * y).1 (hG _ (x * y).2) U = L.deckApp n y.1 (hG _ y.2) U ≫ L.deckApp n x.1 (hG _ x.2) U
    from this]
  rfl

end Points

end C1Body

namespace C1Body

section Count

open AlgebraicGeometry GoodReductionJacobian.RelativeGroupLaw

variable (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0)

include hc hA hn in
theorem natCard_torsionSubset :
    Nat.card ↥(L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n) = n ^ (2 * g) := by
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  obtain ⟨H, instR, instH, hfin, hcoc, hdim, -, e, he_mul, he_nat⟩ :=
    GoodReductionJacobian.AbelianSchemePropertyBundle.exists_hopfAlgebra_torsion_finrank_eq_pow_and_nsmulAlgHom_eq
      K f L hc hA g n hn0
  haveI := hfin

  obtain ⟨hfinK, -, hEt, -⟩ := L.isFinite_flat_etale_schemeKerStr_of_isUnit hA hc g n (isUnit_iff_ne_zero.2 hn)
  haveI := hfinK
  haveI := hEt
  haveI : IsReduced (L.schemeKer n) := AlgebraicGeometry.isReduced_of_etale (L.schemeKerStr n)
  haveI : IsAffineHom (L.schemeKerStr n) := inferInstance
  obtain ⟨i, -, -⟩ := L.exists_iso_spec_schemeKer_of_forall_equiv_torsionSubset n H e he_nat
  haveI : IsReduced (Spec (CommRingCat.of H)) := isReduced_of_isOpenImmersion i.hom
  haveI hred : _root_.IsReduced H := (affine_isReduced_iff (CommRingCat.of H)).1 inferInstance
  have hcardH : Nat.card (H →ₐ[K] K) = n ^ (2 * g) := by
    rw [← hdim]; exact (Algebra.isReduced_iff_natCard_algHom_eq_finrank_of_isAlgClosed K K H).1 hred
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 (Spec (CommRingCat.of K)) := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]; exact Spec.map_id _
  have h1 : Nat.card ↥(L.torsionSubset (Spec.map (CommRingCat.ofHom (algebraMap K K))) n) =
      Nat.card (WithConv (H →ₐ[K] K)) := Nat.card_congr (e K).symm
  rw [hid] at h1
  rw [h1, ← hcardH]
  exact Nat.card_congr (⟨WithConv.ofConv, WithConv.toConv, fun _ => rfl, fun _ => rfl⟩ : WithConv (H →ₐ[K] K) ≃ (H →ₐ[K] K))

end Count

end C1Body

open C1Body AlgebraicGeometry _root_.AlgebraicGeometry.OModulePresheaf GoodReductionJacobian.RelativeGroupLaw in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f]
    (n : ℕ) (hn : (n : K) ≠ 0)
    (hG : ∀ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n, L.translate x ≫ L.schemeNsmul n = L.schemeNsmul n) :
    {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K | L.IsNsmulCharacter n χ}.Finite ∧
    {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K | L.IsNsmulCharacter n χ}.ncard = n ^ (2 * g) ∧
    (∀ χ ψ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K,
      L.IsNsmulCharacter n χ → L.IsNsmulCharacter n ψ → L.IsNsmulCharacter n (χ * ψ)) ∧
    (∀ χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K, L.IsNsmulCharacter n χ → χ ^ n = 1) ∧
    ∀ (X : Finset (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)),
      (∀ χ, χ ∈ X ↔ L.IsNsmulCharacter n χ) →
      ∀ U : A.Opens, Function.Bijective
        (fun s : (χ : ↥X) → (L.eigenSubdatum n hG (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)).obj U =>
          ∑ χ : ↥X, (L.eigenInclusion n hG (χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K)).app U (s χ)) := by
  classical
  have hn0 : n ≠ 0 := by rintro rfl; exact hn (by simp)
  letI grp : CommGroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) := commGroupPt L hc
  let Gs : Subgroup (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f) := torsionSubgroup L hc n
  have hGs : ∀ x, x ∈ Gs ↔ x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n := fun x => Iff.rfl

  have hcardG : Nat.card ↥Gs = n ^ (2 * g) := by
    change Nat.card ↥(L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n) = n ^ (2 * g)
    exact natCard_torsionSubset K f L hc hA g n hn
  haveI : Finite ↥Gs := Nat.finite_of_card_ne_zero (by rw [hcardG]; positivity)
  letI : Fintype ↥Gs := Fintype.ofFinite _
  have hcardK : (Fintype.card ↥Gs : K) ≠ 0 := by
    rw [← Nat.card_eq_fintype_card, hcardG, Nat.cast_pow]; exact pow_ne_zero _ hn

  haveI : NeZero (n : K) := ⟨hn⟩
  haveI : NeZero n := ⟨hn0⟩
  have hexp : Monoid.exponent ↥Gs ∣ n := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (mem_torsionSubset_iff_pow L hc n x.1).1 x.2
  haveI hroots : HasEnoughRootsOfUnity K (Monoid.exponent ↥Gs) := HasEnoughRootsOfUnity.of_dvd K hexp
  haveI : Finite (↥Gs →* Kˣ) := by
    obtain ⟨e⟩ := CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity ↥Gs K
    exact Finite.of_equiv _ e.toEquiv.symm
  letI : Fintype (↥Gs →* Kˣ) := Fintype.ofFinite _

  let toF : (↥Gs →* Kˣ) → (SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K) := fun φ x =>
    if hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n then ((φ ⟨x, hx⟩ : Kˣ) : K) else 1
  have toF_mem : ∀ φ x (hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n), toF φ x = ((φ ⟨x, hx⟩ : Kˣ) : K) :=
    fun φ x hx => dif_pos hx
  have toF_not : ∀ φ x, x ∉ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n → toF φ x = 1 :=
    fun φ x hx => dif_neg hx
  have one_mem : L.one (𝟙 (Spec (CommRingCat.of K))) ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n := Gs.one_mem
  have toF_char : ∀ φ, L.IsNsmulCharacter n (toF φ) := by
    intro φ
    refine ⟨fun x hx => toF_not φ x hx, ?_, ?_⟩
    · rw [toF_mem φ _ one_mem]
      have : (⟨L.one (𝟙 (Spec (CommRingCat.of K))), one_mem⟩ : ↥Gs) = 1 := Subtype.ext rfl
      rw [this, map_one, Units.val_one]
    · intro x hx y hy
      have hxy : L.mul (𝟙 _) x y ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n := Gs.mul_mem hx hy
      rw [toF_mem φ _ hxy, toF_mem φ x hx, toF_mem φ y hy]
      have : (⟨L.mul (𝟙 _) x y, hxy⟩ : ↥Gs) = ⟨x, hx⟩ * ⟨y, hy⟩ := Subtype.ext rfl
      rw [this, map_mul, Units.val_mul]
  have toF_inj : Function.Injective toF := by
    intro φ ψ h
    ext x
    have := congrFun h x.1
    rwa [toF_mem φ x.1 x.2, toF_mem ψ x.1 x.2] at this
  have toF_surj : ∀ χ, L.IsNsmulCharacter n χ → ∃ φ, toF φ = χ := by
    rintro χ ⟨hoff, hone, hmul⟩
    have hunit : ∀ x : ↥Gs, χ x.1 * χ (x⁻¹).1 = 1 := fun x => by
      rw [← hmul _ x.2 _ (x⁻¹).2]
      have : L.mul (𝟙 _) x.1 (x⁻¹).1 = (x * x⁻¹).1 := rfl
      rw [this, _root_.mul_inv_cancel]; exact hone
    let φ : ↥Gs →* Kˣ :=
      { toFun := fun x => Units.mkOfMulEqOne (χ x.1) (χ (x⁻¹).1) (hunit x)
        map_one' := Units.ext hone
        map_mul' := fun x y => Units.ext (hmul _ x.2 _ y.2) }
    refine ⟨φ, funext fun x => ?_⟩
    by_cases hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n
    · rw [toF_mem φ x hx]; rfl
    · rw [toF_not φ x hx, hoff x hx]
  have hset : {χ : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K | L.IsNsmulCharacter n χ} = Set.range toF := by
    ext χ
    exact ⟨fun h => by obtain ⟨φ, rfl⟩ := toF_surj χ h; exact ⟨φ, rfl⟩, fun ⟨φ, h⟩ => h ▸ toF_char φ⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hset]; exact Set.finite_range toF
  · rw [hset, ← Nat.card_coe_set_eq, Nat.card_congr (Equiv.ofInjective toF toF_inj).symm,
      CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity ↥Gs K, hcardG]
  · intro χ ψ hχ hψ
    obtain ⟨φ, rfl⟩ := toF_surj χ hχ
    obtain ⟨φ', rfl⟩ := toF_surj ψ hψ
    have : toF φ * toF φ' = toF (φ * φ') := funext fun x => by
      rw [Pi.mul_apply]
      by_cases hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n
      · rw [toF_mem _ x hx, toF_mem _ x hx, toF_mem _ x hx, MonoidHom.mul_apply, Units.val_mul]
      · rw [toF_not _ x hx, toF_not _ x hx, toF_not _ x hx, _root_.mul_one]
    rw [this]; exact toF_char _
  · intro χ hχ
    obtain ⟨φ, rfl⟩ := toF_surj χ hχ
    funext x
    rw [Pi.pow_apply, Pi.one_apply]
    by_cases hx : x ∈ L.torsionSubset (𝟙 (Spec (CommRingCat.of K))) n
    · rw [toF_mem φ x hx, ← Units.val_pow_eq_pow_val, ← map_pow]
      have : (⟨x, hx⟩ : ↥Gs) ^ n = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]; exact (mem_torsionSubset_iff_pow L hc n x).1 hx)
      rw [this, map_one, Units.val_one]
    · rw [toF_not φ x hx, one_pow]
  · intro X hX U
    let ρ := rho L hc n hG U
    have hbij := bijective_sum_eig ρ (rho_one L hc n hG U) (rho_mul L hc n hG U) hcardK

    have heig : ∀ φ (v : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U),
        v ∈ eig ρ φ ↔ v ∈ L.eigenSubmodule n hG (toF φ) U := by
      intro φ v
      rw [mem_eig, RelativeGroupLaw.mem_eigenSubmodule_iff, RelativeGroupLaw.isEigensection_iff]
      constructor
      · intro h x hx
        have h1 := h ⟨x, hx⟩
        rw [rho_apply] at h1
        rw [toF_mem φ x hx, h1]; rfl
      · intro h x
        rw [rho_apply]
        have h1 := h x.1 x.2
        rw [toF_mem φ x.1 x.2] at h1
        exact h1
    have hXφ : ∀ φ, toF φ ∈ X := fun φ => (hX _).2 (toF_char φ)
    let eX : (↥Gs →* Kˣ) ≃ ↥X := Equiv.ofBijective (fun φ => ⟨toF φ, hXφ φ⟩)
      ⟨fun φ ψ h => toF_inj (congrArg Subtype.val h), fun χ => by
        obtain ⟨φ, hφ⟩ := toF_surj χ.1 ((hX _).1 χ.2); exact ⟨φ, Subtype.ext hφ⟩⟩
    have eX_val : ∀ φ, ((eX φ : ↥X) : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K) = toF φ := fun φ => rfl
    have eX_symm_val : ∀ χ : ↥X, toF (eX.symm χ) = χ.1 := fun χ => by
      have := congrArg Subtype.val (eX.apply_symm_apply χ); exact this
    have key : ∀ (a b : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f → K) (hab : a = b)
        (v : (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U),
        v ∈ L.eigenSubmodule n hG a U → v ∈ L.eigenSubmodule n hG b U := by
      intro a b hab v hv; subst hab; exact hv
    constructor
    · intro s s' hss'
      dsimp only at hss'
      simp only [RelativeGroupLaw.eigenInclusion_app] at hss'
      let gv : ↥X → (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U := fun χ => (s χ).1
      let gv' : ↥X → (OModulePresheaf.pushforwardUnit f (L.schemeNsmul n)).obj U := fun χ => (s' χ).1
      have hgg : ∑ χ, gv χ = ∑ χ, gv' χ := hss'
      let u : (φ : ↥Gs →* Kˣ) → eig ρ φ := fun φ => ⟨gv (eX φ), (heig φ _).2 (s (eX φ)).2⟩
      let u' : (φ : ↥Gs →* Kˣ) → eig ρ φ := fun φ => ⟨gv' (eX φ), (heig φ _).2 (s' (eX φ)).2⟩
      have hu : (∑ φ, (u φ).1) = ∑ φ, (u' φ).1 := by
        change (∑ φ, gv (eX φ)) = ∑ φ, gv' (eX φ)
        rw [Equiv.sum_comp eX gv, Equiv.sum_comp eX gv']
        exact hgg
      have huu := hbij.1 hu
      have hg : ∀ χ, gv χ = gv' χ := fun χ => by
        have := congrArg Subtype.val (congrFun huu (eX.symm χ))
        change gv (eX (eX.symm χ)) = gv' (eX (eX.symm χ)) at this
        rwa [Equiv.apply_symm_apply] at this
      funext χ
      exact Subtype.ext (hg χ)
    · intro w
      obtain ⟨u, hu⟩ := hbij.2 w
      refine ⟨fun χ => ⟨(u (eX.symm χ)).1, key _ _ (eX_symm_val χ) _ ((heig _ _).1 (u (eX.symm χ)).2)⟩, ?_⟩
      dsimp only
      simp only [RelativeGroupLaw.eigenInclusion_app]
      rw [← hu]
      exact Equiv.sum_comp eX.symm (fun φ => (u φ).1)

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_finite_isNsmulCharacter_and_ncard_eq_pow_and_bijective_sum_eigenInclusion (solution)
