-- Prove2me | solution 1 for ModularCurve.FullLevel.telescope_frame_of_semistableCovering_of_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/bb9dfa1c-d037-5ff0-8768-74e4acbd84f2

import Mathlib
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringTelescope
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringGuards
import Definitions.Def_ModularCurve_FullLevelSemistableCoveringNaturality
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_JZeroTateModule
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ValuationSubring_exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne
import Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv
import Theorems.Thm_ValuationSubring_tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JH_finite_and_free_and_finrank_tateModule_eq_two_mul_genusFF
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_telescope_frame_of_semistableCovering_of_eq_two
p2m_attr_erase "instance" "ExtCitation.instGroupExtArithLocalGroups ExtCitation.instFintypeExtArithIndex ExtCitation.instGroupPrimeLocalGaloisGroup groupCohomology.finiteDimensional_selmerAdm_of_adm JacobiSumStickelberger.instModuleZModModP ExtCitation.LocalLevel.compactGw ExtCitation.LocalLevel.isInvariant_gal ExtCitation.LocalLevel.algRwOO ExtCitation.LocalLevel.finiteIndex_fixingSubgroup_s17 ExtCitation.LocalLevel.smulCommOO ExtCitation.LocalLevel.continuousSMulDiscrete_gal ExtCitation.LocalLevel.charP_kbar ExtCitation.LocalLevel.algZModKbar ExtCitation.LocalLevel.smulCommRw ExtCitation.LocalLevel.isInvariantOO ExtCitation.LocalLevel.csdRw ExtCitation.LocalLevel.compactSpace_gal ExtCitation.LocalLevel.isInvariantRw ExtCitation.LocalLevel.actOO ExtCitation.LocalLevel.algOO ExtCitation.LocalLevel.finiteIndex_op_s17 ExtCitation.LocalLevel.csdOO ExtCitation.LocalLevel.smulOO instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies"
p2m_attr_erase "instance" "PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra"
p2m_attr_erase "instance" "TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "ExtCitation.pPrime_coe ExtCitation.extArithLoc_inr ExtCitation.extArithLoc_inl groupCohomology.selmerAdm_top groupCohomology.selmerAdm_bot groupCohomology.mem_orthogonal_iff Representation.twist_one groupCohomology.orthogonal_bot Stickelberger.mem_exponentSet ExtCitation.archimedeanLoc_archimedeanGen complexConjAlgEquiv_apply galRestrictionDatum_apply Ideal.coe_mapNonZero algAutToRingAut_apply JacobiSumStickelberger.mem_nsmulRange JacobiSumStickelberger.ModP.mapEnd_proj JacobiSumStickelberger.clEnd_clProj JacobiSumStickelberger.ModP.proj_apply JacobiSumStickelberger.ModP.mapHom_proj ExtCitation.LocalLevel.coe_smul_OO AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd"
p2m_attr_erase "simp" "NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app"
p2m_attr_erase "simp" "PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec"
p2m_attr_erase "simp" "CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq"

set_option autoImplicit false

open AlgebraicCurve IsLocalRing
open scoped TensorProduct Pointwise

attribute [local instance] ModularCurve.instDecidableEqResidueFieldSemistable
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable

noncomputable section

namespace R1AF8TeleFrame

section Base

variable (q : ℕ) [Fact q.Prime] (P : ValuationSubring (AlgebraicClosure ℚ))

theorem natCast_mem_P : ((q : ℕ) : AlgebraicClosure ℚ) ∈ P := _root_.natCast_mem P q

theorem natCast_mem_maximalIdeal (hP : P.LiesOverPrime q) :
    (⟨(q : AlgebraicClosure ℚ), natCast_mem_P q P⟩ : P) ∈ maximalIdeal P :=
  ValuationSubring.coe_mem_nonunits_iff.mp hP

theorem residue_natCast_eq_zero (hP : P.LiesOverPrime q) : ((q : ℕ) : ResidueField P) = 0 := by
  have h := (residue_eq_zero_iff (R := P) _).mpr (natCast_mem_maximalIdeal q P hP)
  have hq : (⟨(q : AlgebraicClosure ℚ), natCast_mem_P q P⟩ : P) = (q : P) := Subtype.ext (by simp)
  rw [hq, map_natCast] at h
  exact h

theorem charP_residueField (hP : P.LiesOverPrime q) : CharP (ResidueField P) q :=
  (CharP.charP_iff_prime_eq_zero (Fact.out : q.Prime)).mpr (residue_natCast_eq_zero q P hP)

theorem isUnit_natCast_of_ne (hP : P.LiesOverPrime q) (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam) :
    IsUnit ((lam : ℕ) : ResidueField P) := by
  haveI := charP_residueField q P hP
  rw [isUnit_iff_ne_zero, Ne, CharP.cast_eq_zero_iff (ResidueField P) q lam]
  intro h
  exact hqlam ((Nat.prime_dvd_prime_iff_eq (Fact.out : q.Prime) (Fact.out : lam.Prime)).mp h)

variable (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)

include hπ in
theorem pi_ne_zero : π ≠ 0 := by
  rintro rfl
  have hq0 : (q : AlgebraicClosure ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : q.Prime).ne_zero
  have hne : q ^ 2 - 1 ≠ 0 := by
    have h2 := (Fact.out : q.Prime).two_le
    have : 2 ^ 2 ≤ q ^ 2 := Nat.pow_le_pow_left h2 2
    omega
  rw [zero_pow hne] at hπ
  exact hq0 hπ.symm

include hπ in
theorem pi_mk_ne_zero : (⟨π, hπP⟩ : P) ≠ 0 := fun h =>
  pi_ne_zero q π hπ (congrArg Subtype.val h)

include hπ in
theorem pi_mem_maximalIdeal (hP : P.LiesOverPrime q) : (⟨π, hπP⟩ : P) ∈ maximalIdeal P := by
  have hpow : (⟨π, hπP⟩ : P) ^ (q ^ 2 - 1) = ⟨(q : AlgebraicClosure ℚ), natCast_mem_P q P⟩ :=
    Subtype.ext (by simp [hπ])
  have hmem : (⟨π, hπP⟩ : P) ^ (q ^ 2 - 1) ∈ maximalIdeal P := hpow ▸ natCast_mem_maximalIdeal q P hP
  exact (Ideal.IsMaximal.isPrime (maximalIdeal.isMaximal P)).mem_of_pow_mem _ hmem

end Base

section Inertia

variable (P : ValuationSubring (AlgebraicClosure ℚ))

theorem mem_iff_apply_mem_of_mem_inertiaSubgroupIn {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (a : AlgebraicClosure ℚ) : a ∈ P ↔ τ a ∈ P := by
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hτ
  constructor
  · intro ha
    exact (t • (⟨a, ha⟩ : P)).2
  · intro ha
    have h := (t⁻¹ • (⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a, ha⟩ : P)).2
    have hval : ((t⁻¹ • (⟨(t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a, ha⟩ : P) : P) :
        AlgebraicClosure ℚ) = a := by
      show ((t⁻¹ : P.decompositionSubgroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          ((t : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) a) = a
      simp
    rw [hval] at h
    exact h

theorem residue_apply_eq_of_mem_inertiaSubgroupIn {τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ}
    (hτ : τ ∈ P.inertiaSubgroupIn ℚ) (a : P) (h : τ (a : AlgebraicClosure ℚ) ∈ P) :
    residue P ⟨τ (a : AlgebraicClosure ℚ), h⟩ = residue P a := by
  obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hτ
  have hker : MulSemiringAction.toRingAut (P.decompositionSubgroup ℚ) (ResidueField P) t = 1 :=
    (MonoidHom.mem_ker).mp ht
  have key : residue P (t • a) = residue P a := by
    rw [ResidueField.residue_smul]
    have := RingEquiv.congr_fun hker (residue P a)
    simpa using this
  have hsmul : (t • a : P) = ⟨((P.decompositionSubgroup ℚ).subtype t) (a : AlgebraicClosure ℚ), h⟩ :=
    Subtype.ext rfl
  rw [hsmul] at key
  exact key

end Inertia

section Nodes

open ModularCurve ModularCurve.FullLevel ModularCurve.FullLevel.SemistableCovering

variable {q : ℕ} [Fact q.Prime] {M' : ℕ} [NeZero M'] {A : ValuationSubring (AlgebraicClosure ℚ)}
variable {W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) M'))}
variable (𝒞 : SemistableCovering q M' A W)

abbrev SumSigma : Type := Σ j : CuspidalType.ProjLine q ⊕ ↥W, Place (ResidueField A) (𝒞.sumFbar j)

abbrev TeleSigma : Type := Σ i : Fin 𝒞.teleN, Place (ResidueField A) (𝒞.teleFbar i)

def toSum (x : TeleSigma 𝒞) : SumSigma 𝒞 := ⟨𝒞.eIdx.symm x.1, x.2⟩

theorem toSum_injective : Function.Injective (toSum 𝒞) := by
  rintro ⟨i, y⟩ ⟨i', y'⟩ h
  have h1 : 𝒞.eIdx.symm i = 𝒞.eIdx.symm i' := congrArg Sigma.fst h
  have h2 : HEq y y' := (Sigma.mk.inj_iff.mp h).2
  have hi : i = i' := 𝒞.eIdx.symm.injective h1
  subst hi
  exact Sigma.ext rfl h2

def sumEnds : (CuspidalType.ProjLine q × ↥W) ⊕ (CuspidalType.ProjLine q × ↥W) → SumSigma 𝒞 :=
  Sum.elim (fun p => ⟨Sum.inl p.1, 𝒞.sumNode (Sum.inl p.1) p⟩) (fun p => ⟨Sum.inr p.2, 𝒞.sumNode (Sum.inr p.2) p⟩)

theorem toSum_src (e : Fin 𝒞.teleM) :
    toSum 𝒞 ⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ = sumEnds 𝒞 (Sum.inl (𝒞.eEdge.symm e)) := by
  show (⟨𝒞.eIdx.symm (𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1)),
      𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inl (𝒞.eEdge.symm e).1))) (𝒞.eEdge.symm e)⟩ : SumSigma 𝒞) =
    ⟨Sum.inl (𝒞.eEdge.symm e).1, 𝒞.sumNode (Sum.inl (𝒞.eEdge.symm e).1) (𝒞.eEdge.symm e)⟩
  rw [Equiv.symm_apply_apply]

theorem toSum_tgt (e : Fin 𝒞.teleM) :
    toSum 𝒞 ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ = sumEnds 𝒞 (Sum.inr (𝒞.eEdge.symm e)) := by
  show (⟨𝒞.eIdx.symm (𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2)),
      𝒞.sumNode (𝒞.eIdx.symm (𝒞.eIdx (Sum.inr (𝒞.eEdge.symm e).2))) (𝒞.eEdge.symm e)⟩ : SumSigma 𝒞) =
    ⟨Sum.inr (𝒞.eEdge.symm e).2, 𝒞.sumNode (Sum.inr (𝒞.eEdge.symm e).2) (𝒞.eEdge.symm e)⟩
  rw [Equiv.symm_apply_apply]

theorem toSum_elim (E : Fin 𝒞.teleM ⊕ Fin 𝒞.teleM) :
    toSum 𝒞 (Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : TeleSigma 𝒞)) (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E) =
      sumEnds 𝒞 (E.map 𝒞.eEdge.symm 𝒞.eEdge.symm) := by
  rcases E with e | e
  · exact toSum_src 𝒞 e
  · exact toSum_tgt 𝒞 e

theorem exists_sumEnds_eq (j : CuspidalType.ProjLine q ⊕ ↥W) (x : Place (ResidueField A) (𝒞.sumFbar j))
    (hx : x ∈ (𝒞.sumChart j).nodes) : ∃ E, sumEnds 𝒞 E = ⟨j, x⟩ := by
  cases j with
  | inl ℓ =>
    obtain ⟨s, hs, -⟩ := 𝒞.existsUnique_xs_eq ℓ x hx
    refine ⟨Sum.inl (ℓ, s), ?_⟩
    show (⟨Sum.inl ℓ, 𝒞.xs ℓ s⟩ : SumSigma 𝒞) = ⟨Sum.inl ℓ, x⟩
    rw [hs]
  | inr s =>
    obtain ⟨ℓ, hℓ, -⟩ := 𝒞.existsUnique_xt_eq s x hx
    refine ⟨Sum.inr (ℓ, s), ?_⟩
    show (⟨Sum.inr s, 𝒞.xt ℓ s⟩ : SumSigma 𝒞) = ⟨Sum.inr s, x⟩
    rw [hℓ]

theorem sumEnds_unique (j : CuspidalType.ProjLine q ⊕ ↥W) (x : Place (ResidueField A) (𝒞.sumFbar j))
    (hx : x ∈ (𝒞.sumChart j).nodes)
    (E E' : (CuspidalType.ProjLine q × ↥W) ⊕ (CuspidalType.ProjLine q × ↥W))
    (hE : sumEnds 𝒞 E = ⟨j, x⟩) (hE' : sumEnds 𝒞 E' = ⟨j, x⟩) : E = E' := by
  rcases E with ⟨ℓ, s⟩ | ⟨ℓ, s⟩ <;> rcases E' with ⟨ℓ', s'⟩ | ⟨ℓ', s'⟩
  ·
    change (⟨Sum.inl ℓ, 𝒞.xs ℓ s⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE
    change (⟨Sum.inl ℓ', 𝒞.xs ℓ' s'⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE'
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hE
    obtain ⟨h1', h2'⟩ := Sigma.mk.inj_iff.mp hE'
    subst h1
    have hℓ : ℓ' = ℓ := Sum.inl_injective h1'
    subst hℓ
    have hx1 : 𝒞.xs ℓ' s = x := eq_of_heq h2
    have hx2 : 𝒞.xs ℓ' s' = x := eq_of_heq h2'
    obtain ⟨s₀, -, huniq⟩ := 𝒞.existsUnique_xs_eq ℓ' x hx
    have : s = s' := (huniq s hx1).trans (huniq s' hx2).symm
    subst this
    rfl
  · change (⟨Sum.inl ℓ, 𝒞.xs ℓ s⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE
    change (⟨Sum.inr s', 𝒞.xt ℓ' s'⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE'
    have h1 : (Sum.inl ℓ : CuspidalType.ProjLine q ⊕ ↥W) = j := congrArg Sigma.fst hE
    have h1' : (Sum.inr s' : CuspidalType.ProjLine q ⊕ ↥W) = j := congrArg Sigma.fst hE'
    exact absurd (h1.trans h1'.symm) Sum.inl_ne_inr
  · change (⟨Sum.inr s, 𝒞.xt ℓ s⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE
    change (⟨Sum.inl ℓ', 𝒞.xs ℓ' s'⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE'
    have h1 : (Sum.inr s : CuspidalType.ProjLine q ⊕ ↥W) = j := congrArg Sigma.fst hE
    have h1' : (Sum.inl ℓ' : CuspidalType.ProjLine q ⊕ ↥W) = j := congrArg Sigma.fst hE'
    exact absurd (h1'.trans h1.symm) Sum.inl_ne_inr
  ·
    change (⟨Sum.inr s, 𝒞.xt ℓ s⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE
    change (⟨Sum.inr s', 𝒞.xt ℓ' s'⟩ : SumSigma 𝒞) = ⟨j, x⟩ at hE'
    obtain ⟨h1, h2⟩ := Sigma.mk.inj_iff.mp hE
    obtain ⟨h1', h2'⟩ := Sigma.mk.inj_iff.mp hE'
    subst h1
    have hs : s' = s := Sum.inr_injective h1'
    subst hs
    have hx1 : 𝒞.xt ℓ s' = x := eq_of_heq h2
    have hx2 : 𝒞.xt ℓ' s' = x := eq_of_heq h2'
    obtain ⟨ℓ₀, -, huniq⟩ := 𝒞.existsUnique_xt_eq s' x hx
    have : ℓ = ℓ' := (huniq ℓ hx1).trans (huniq ℓ' hx2).symm
    subst this
    rfl

theorem tele_nodes :
    (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃ e,
        (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField A) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
        (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (ResidueField A) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
      (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∀ E E' : Fin 𝒞.teleM ⊕ Fin 𝒞.teleM,
        Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField A) (𝒞.teleFbar j)))
          (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E = ⟨i, x⟩ →
        Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (ResidueField A) (𝒞.teleFbar j)))
          (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E' = ⟨i, x⟩ → E = E') := by
  refine ⟨fun i x hx => ?_, fun i x hx E E' hE hE' => ?_⟩
  ·
    obtain ⟨E, hE⟩ := exists_sumEnds_eq 𝒞 (𝒞.eIdx.symm i) x hx
    rcases E with p | p
    · refine ⟨𝒞.eEdge p, Or.inl ?_⟩
      apply toSum_injective 𝒞
      rw [toSum_src, Equiv.symm_apply_apply]
      exact hE
    · refine ⟨𝒞.eEdge p, Or.inr ?_⟩
      apply toSum_injective 𝒞
      rw [toSum_tgt, Equiv.symm_apply_apply]
      exact hE
  ·
    have hE1 := congrArg (toSum 𝒞) hE
    have hE1' := congrArg (toSum 𝒞) hE'
    rw [toSum_elim] at hE1 hE1'
    have huniq := sumEnds_unique 𝒞 (𝒞.eIdx.symm i) x hx _ _ hE1 hE1'
    have hinj : Function.Injective (Sum.map 𝒞.eEdge.symm 𝒞.eEdge.symm :
        Fin 𝒞.teleM ⊕ Fin 𝒞.teleM → (CuspidalType.ProjLine q × ↥W) ⊕ (CuspidalType.ProjLine q × ↥W)) :=
      Sum.map_injective.mpr ⟨𝒞.eEdge.symm.injective, 𝒞.eEdge.symm.injective⟩
    exact hinj huniq

end Nodes

theorem isRational_of_isCurveOver {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (v : Place K F) : v.IsRational := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  exact (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := v.ResidueField)).2

abbrev F0 (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] : IntermediateField ℚ (LaurentSeries ℚ) :=
  ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')

theorem baseAut_arithmeticGalois_apply (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M']
    (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : AlgebraicClosure ℚ) :
    SemilinearAut.baseAut (ModularCurve.arithmeticGalois (L := AlgebraicClosure ℚ) (F0 q M') τ) a = τ a := by
  rw [ModularCurve.baseAut_arithmeticGalois]
  rfl

end R1AF8TeleFrame

end

set_option maxHeartbeats 6400000 in
open R1AF8TeleFrame ModularCurve ModularCurve.FullLevel in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q = 2) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (lam : ℕ) [Fact lam.Prime] (hqlam : q ≠ lam)
    (hLA : ModularCurve.FullLevel.LevelAutInputs q M') (hGL : ModularCurve.FullLevel.GL2Laws q M')
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (W : Finset (AlgebraicCurve.Place (IsLocalRing.ResidueField P)
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M')))
    (hW : ∀ w, w ∈ W ↔ w ∈ ModularCurve.ssPlaces q M' (IsLocalRing.ResidueField P))
    (π : AlgebraicClosure ℚ) (hπ : π ^ (q ^ 2 - 1) = (q : AlgebraicClosure ℚ)) (hπP : π ∈ P)
    (ι : GaloisField q 2 →+* IsLocalRing.ResidueField P)
    [IsDomain (DrinfeldCurve.CoordRing q (IsLocalRing.ResidueField P))]
    (hle : ModularCurve.modularFunctionFieldBar M' ≤ ModularCurve.FullLevel.fieldBar q M')
    (R₀ : AlgebraicCurve.ConstantReduction P ↥(ModularCurve.modularFunctionFieldBar M')
      (modularFunctionFieldC (IsLocalRing.ResidueField P) M'))

    (hR₀ : ∀ (y : LaurentSeries ↥P) (hy : ModularCurve.coeffMap P.subtype y ∈ ModularCurve.modularFunctionFieldBar M'),
      ∃ h : (⟨ModularCurve.coeffMap P.subtype y, hy⟩ : ↥(ModularCurve.modularFunctionFieldBar M')) ∈ R₀.integers,
        ((R₀.residue ⟨_, h⟩ : modularFunctionFieldC (IsLocalRing.ResidueField P) M') :
            LaurentSeries (IsLocalRing.ResidueField P)) =
          ModularCurve.coeffMap (IsLocalRing.residue ↥P) y) :
    letI : Algebra (GaloisField q 2) (IsLocalRing.ResidueField P) := ι.toAlgebra
    let S : Set (SemilinearAut (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M')) :=
      {s | ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
        s = ModularCurve.arithmeticGalois (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ}
    ∀ 𝒞 : ModularCurve.FullLevel.SemistableCovering q M' P W,
      𝒞.EquivClauses →
      (∀ (ζ : ModularCurve.FullLevel.Idx q) (s : ↥W), ∃ η : ℕ, (η = 1 ∨ η = q) ∧ 𝒞.DrinfeldClause π ι η ζ s) →
      (∀ ζ : ModularCurve.FullLevel.Idx q, 𝒞.IgusaUnipotentClause ζ) → 𝒞.LevelPinClauses hle R₀ → 𝒞.InertiaClause π →
      𝒞.WidthClause ⟨π, hπP⟩ → 𝒞.GenusClause → 𝒞.DiscFibreClause → 𝒞.CurveClause → 𝒞.NaturalityClauses →
      ((⟨π, hπP⟩ : P) ∈ IsLocalRing.maximalIdeal P ∧ (⟨π, hπP⟩ : P) ≠ 0) ∧
      (∀ x : AlgebraicClosure ℚ, x ≠ 0 → ∀ y : P, y ∈ IsLocalRing.maximalIdeal P →
        ∃ n : ℕ, P.valuation ((y : AlgebraicClosure ℚ) ^ n) ≤ P.valuation x) ∧
      (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, Q.IsRational) ∧
      (∀ s ∈ S,
        (∀ a : AlgebraicClosure ℚ, a ∈ P ↔ SemilinearAut.baseAut s a ∈ P) ∧
        SemilinearAut.baseAut s ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) ∧
        (∀ (a : P) (h : SemilinearAut.baseAut s (a : AlgebraicClosure ℚ) ∈ P),
          IsLocalRing.residue P ⟨SemilinearAut.baseAut s (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) ∧
        (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, s • Q ∈ (𝒞.teleChart i).dom) ∧
        (∀ e, ∀ Q ∈ (𝒞.teleAn e).dom, s • Q ∈ (𝒞.teleAn e).dom) ∧
        (∀ e, s • (𝒞.teleAn e).param = (𝒞.teleAn e).param) ∧ (∀ e, s • (𝒞.teleAn' e).param = (𝒞.teleAn' e).param) ∧
        (∀ i, ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), ∀ hf : f ∈ (𝒞.teleChart i).integers,
          ∃ hf' : s • f ∈ (𝒞.teleChart i).integers,
          (𝒞.teleChart i).residue ⟨s • f, hf'⟩ = (𝒞.teleChart i).residue ⟨f, hf⟩) ∧
        (∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap (s • Q) = (𝒞.teleChart i).placeMap Q)) ∧
      (∀ σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ, (∀ a : AlgebraicClosure ℚ, a ∈ P ↔ σ a ∈ P) →
        σ ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) →
        (∀ (a : P) (h : σ (a : AlgebraicClosure ℚ) ∈ P),
          IsLocalRing.residue P ⟨σ (a : AlgebraicClosure ℚ), h⟩ = IsLocalRing.residue P a) →
        ∃ s ∈ S, SemilinearAut.baseAut s = σ) ∧
      IsUnit ((lam : ℕ) : IsLocalRing.ResidueField P) ∧
      (∃ s ∈ S, ∃ r : AlgebraicClosure ℚ, r ^ lam = ((⟨π, hπP⟩ : P) : AlgebraicClosure ℚ) ∧
        SemilinearAut.baseAut s r ≠ r) ∧
      ((∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∃ e,
          (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)) = ⟨i, x⟩ ∨
          (⟨𝒞.teleTgt e, 𝒞.teleXt e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)) = ⟨i, x⟩) ∧
        (∀ i, ∀ x ∈ (𝒞.teleChart i).nodes, ∀ E E' : Fin 𝒞.teleM ⊕ Fin 𝒞.teleM,
          Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)))
            (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E = ⟨i, x⟩ →
          Sum.elim (fun e => (⟨𝒞.teleSrc e, 𝒞.teleXs e⟩ : Σ j, Place (IsLocalRing.ResidueField P) (𝒞.teleFbar j)))
            (fun e => ⟨𝒞.teleTgt e, 𝒞.teleXt e⟩) E' = ⟨i, x⟩ → E = E')) ∧
      FiniteDimensional ℚ_[lam] (ModularCurve.RationalTateModule lam (Pic0 (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M'))) ∧
      IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') ∧ Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') := by
  intro S 𝒞 _hEq _hDr _hIg _hPin hIn _hWd _hGen _hDisc _hCurve _hNat

  have hCF := ModularCurve.isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
    (AlgebraicClosure ℚ) (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')
  haveI hCurveF : IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') := hCF.1
  have hEssF : Algebra.EssFiniteType (AlgebraicClosure ℚ) ↥(ModularCurve.FullLevel.fieldBar q M') := hCF.2
  have hπ0 : π ≠ 0 := pi_ne_zero q π hπ

  have htame := (ValuationSubring.tameCharacter_eq_one_iff_apply_eq_and_conj_mem_and_exists_apply_eq_of_pow_sq_sub_one_eq
    q P hP π hπ).1

  have hS : ∀ s, s ∈ S ↔ ∃ τ ∈ P.inertiaSubgroupIn ℚ, P.tameCharacter π τ = 1 ∧
      s = ModularCurve.arithmeticGalois
        (ModularCurve.xHFunctionField (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')) τ := fun s => Iff.rfl
  refine ⟨⟨pi_mem_maximalIdeal q P π hπ hπP hP, pi_mk_ne_zero q P π hπ hπP⟩,
    ValuationSubring.exists_valuation_pow_le_of_mem_maximalIdeal_algebraicClosure_rat P,
    fun i Q _ => isRational_of_isCurveOver Q, ?_, ?_, isUnit_natCast_of_ne q P hP lam hqlam, ?_,
    R1AF8TeleFrame.tele_nodes 𝒞, ?_, hCurveF, hEssF⟩
  ·
    intro s hs
    obtain ⟨τ, hτI, hτ1, hsτ⟩ := (hS s).mp hs
    have hτπ : τ π = π := (htame τ).mp hτ1
    have hbase : ∀ a : AlgebraicClosure ℚ, SemilinearAut.baseAut s a = τ a := by
      intro a
      rw [hsτ]
      exact baseAut_arithmeticGalois_apply q M' τ a

    have hIn' := hIn τ hτI hτ1
    dsimp only at hIn'
    rw [← hsτ] at hIn'
    obtain ⟨hIg, hSS, hAn⟩ := hIn'

    have hdom : ∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, s • Q ∈ (𝒞.teleChart i).dom :=
      (𝒞.forall_teleChart_iff (fun F _ _ C => ∀ Q ∈ C.dom, s • Q ∈ C.dom)).2
        ⟨fun ℓ Q hQ => ((hIg ℓ).2.2 Q).mp hQ, fun s' Q hQ => ((hSS s').2.2 Q).mp hQ⟩
    have hres : ∀ i, ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'), ∀ hf : f ∈ (𝒞.teleChart i).integers,
        ∃ hf' : s • f ∈ (𝒞.teleChart i).integers,
          (𝒞.teleChart i).residue ⟨s • f, hf'⟩ = (𝒞.teleChart i).residue ⟨f, hf⟩ := by
      refine (𝒞.forall_teleChart_iff (fun F _ _ C => ∀ f : ↥(ModularCurve.FullLevel.fieldBar q M'),
        ∀ hf : f ∈ C.integers, ∃ hf' : s • f ∈ C.integers,
          C.residue ⟨s • f, hf'⟩ = C.residue ⟨f, hf⟩)).2 ⟨fun ℓ f hf => ?_, fun s' f hf => ?_⟩
      · obtain ⟨hst, hlaw⟩ := (hIg ℓ).1
        exact ⟨(hst f).mp hf, hlaw f hf⟩
      · obtain ⟨hst, hlaw⟩ := (hSS s').1
        exact ⟨(hst f).mp hf, hlaw f hf⟩
    have hpm : ∀ i, ∀ Q ∈ (𝒞.teleChart i).dom, (𝒞.teleChart i).placeMap (s • Q) = (𝒞.teleChart i).placeMap Q :=
      (𝒞.forall_teleChart_iff (fun F _ _ C => ∀ Q ∈ C.dom, C.placeMap (s • Q) = C.placeMap Q)).2
        ⟨fun ℓ Q _ => (hIg ℓ).2.1 Q, fun s' Q _ => (hSS s').2.1 Q⟩
    refine ⟨fun a => ?_, ?_, fun a h => ?_, hdom, fun e Q hQ => ?_, fun e => ?_, fun e => ?_, hres, hpm⟩
    · rw [hbase]; exact mem_iff_apply_mem_of_mem_inertiaSubgroupIn P hτI a
    · rw [hbase]; exact hτπ
    · have h' : τ (a : AlgebraicClosure ℚ) ∈ P := by rw [← hbase]; exact h
      have := residue_apply_eq_of_mem_inertiaSubgroupIn P hτI a h'
      convert this using 3
      exact hbase a
    · exact ((hAn (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2).1 Q).mp hQ
    · exact (hAn (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2).2.1
    · exact (hAn (𝒞.eEdge.symm e).1 (𝒞.eEdge.symm e).2).2.2
  ·
    intro σ hσP hσπ hσres
    obtain ⟨τ, hτI, hτ1, hτσ⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_coe_eq_of_ringEquiv P π hπ0 σ hσP hσπ hσres
    refine ⟨ModularCurve.arithmeticGalois (F0 q M') τ, (hS _).mpr ⟨τ, hτI, hτ1, rfl⟩, ?_⟩
    exact RingEquiv.ext fun a => hτσ a
  ·
    obtain ⟨τ, hτI, hτ1, r, hr, hne⟩ :=
      ValuationSubring.exists_mem_inertiaSubgroupIn_tameCharacter_eq_one_and_pow_eq_and_apply_ne q P hP π hπ lam hqlam
    exact ⟨ModularCurve.arithmeticGalois (F0 q M') τ, (hS _).mpr ⟨τ, hτI, hτ1, rfl⟩, r, hr, hne⟩
  ·
    haveI : Module.Finite ℤ_[lam] (TateModule lam (ModularCurve.JH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M'))) :=
      (ModularCurve.JH.finite_and_free_and_finrank_tateModule_eq_two_mul_genusFF
        (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M') lam).1
    show Module.Finite ℚ_[lam] (ℚ_[lam] ⊗[ℤ_[lam]]
      TateModule lam (ModularCurve.JH (q ^ 2 * M') (ModularCurve.FullLevel.levelH q M')))
    infer_instance

end S_ModularCurve_FullLevel_telescope_frame_of_semistableCovering_of_eq_two
end P2MW
export P2MW.S_ModularCurve_FullLevel_telescope_frame_of_semistableCovering_of_eq_two (solution)
