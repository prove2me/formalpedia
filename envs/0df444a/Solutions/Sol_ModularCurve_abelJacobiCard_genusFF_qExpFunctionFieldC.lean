-- Prove2me | solution 1 for ModularCurve.abelJacobiCard_genusFF_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/9239932e-069d-5500-97ec-b9a6624a5669

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_ModularCurve_QExpFrobeniusModL
import Theorems.Thm_AlgebraicCurve_Pic0_abelJacobiCard_genusFF_of_frobenius
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_abelJacobiCard_genusFF_qExpFunctionFieldC
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal"
p2m_attr_erase "instance" "PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower"
p2m_attr_erase "instance" "CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime instTopologicallyFGOfFiniteType ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj"
p2m_attr_erase "simp" "PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
p2m_attr_erase "simp" "AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.coe_toResidueValuationSubring AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

namespace P2mTorsStruct

section FixedScalars

open Polynomial

theorem exists_algebraMap_eq_of_pow_eq {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]
    [Algebra (ZMod p) K] {c : K} (hc : c ^ p = c) : ∃ a : ZMod p, algebraMap (ZMod p) K a = c := by
  classical
  have hp : p.Prime := Fact.out
  set f : K[X] := X ^ p - X with hf
  have hf0 : f ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero K hp.one_lt
  set T : Finset K := Finset.univ.image (algebraMap (ZMod p) K) with hT
  have hTcard : T.card = p := by
    rw [hT, Finset.card_image_of_injective _ (algebraMap (ZMod p) K).injective, Finset.card_univ,
      ZMod.card]
  have hroot : ∀ y : K, y ^ p = y → y ∈ f.roots.toFinset := fun y hy => by
    rw [Multiset.mem_toFinset, mem_roots hf0, IsRoot, hf, eval_sub, eval_pow, eval_X, hy, sub_self]
  have hTroots : T ⊆ f.roots.toFinset := by
    intro y hy
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hy
    exact hroot _ (by rw [← map_pow, ZMod.pow_card])
  have hcard_le : f.roots.toFinset.card ≤ T.card := by
    rw [hTcard]
    exact (Multiset.toFinset_card_le _).trans ((card_roots' f).trans
      (FiniteField.X_pow_card_sub_X_natDegree_eq K hp.one_lt).le)
  have hTeq : T = f.roots.toFinset := Finset.eq_of_subset_of_card_le hTroots hcard_le
  have hc' := hroot c hc
  rw [← hTeq] at hc'
  obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hc'
  exact ⟨a, ha⟩

end FixedScalars

section Descent

open MvPolynomial

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {p : ℕ} [Fact p.Prime]

theorem frobenius_aeval {R : Type*} [CommRing R] [Algebra R F] [CharP R p] [CharP F p]
    {ι : Type*} (v : ι → F) (P : MvPolynomial ι R) :
    frobenius F p (aeval v P) = aeval (fun i => v i ^ p) (map (frobenius R p) P) := by
  rw [aeval_def, aeval_def, eval₂_map, eval₂_comp_left]
  have h1 : (frobenius F p).comp (algebraMap R F) = (algebraMap R F).comp (frobenius R p) := by
    ext c
    simp only [RingHom.comp_apply, frobenius_def, map_pow]
  rw [h1]
  exact congrArg (fun g => eval₂ _ g P) (funext fun i => frobenius_def (p := p) (v i))

variable (φ : F →ₐ[K] F)

omit [Fact p.Prime] in

theorem aeval_pow_eq_zero_of_aeval_eq_zero {ι : Type*} {v : ι → F} (hv : ∀ i, φ (v i) = v i ^ p)
    {Q : MvPolynomial ι K} (hQ : aeval v Q = 0) : aeval (fun i => v i ^ p) Q = 0 := by
  have h := comp_aeval_apply φ (f := v) Q
  rw [hQ, map_zero] at h
  rw [show (fun i => v i ^ p) = fun i => φ (v i) from funext fun i => (hv i).symm]
  exact h.symm

theorem exists_relation_zmod_of_relation [CharP K p] [CharP F p] [PerfectRing K p]
    [Algebra (ZMod p) K] [Algebra (ZMod p) F] [IsScalarTower (ZMod p) K F]
    {ι : Type*} {z : ι → F} (hz : ∀ i, φ (z i) = z i ^ p)
    {P : MvPolynomial ι K} (hP0 : P ≠ 0) (hP : aeval z P = 0) :
    ∃ P₀ : MvPolynomial ι (ZMod p), P₀ ≠ 0 ∧ P₀.support ⊆ P.support ∧ aeval z P₀ = 0 := by
  classical
  set w : ι → F := fun i => z i ^ p with hw
  have hwφ : ∀ i, φ (w i) = w i ^ p := fun i => by simp only [hw, map_pow, hz]

  have hex : ∃ n, ∃ Q : MvPolynomial ι K, Q ≠ 0 ∧ Q.support ⊆ P.support ∧ aeval w Q = 0 ∧
      Q.support.card = n :=
    ⟨_, P, hP0, subset_rfl, aeval_pow_eq_zero_of_aeval_eq_zero φ hz hP, rfl⟩
  obtain ⟨Q, hQ0, hQsupp, hQw, hQcard⟩ := Nat.find_spec hex
  have hmin : ∀ Q' : MvPolynomial ι K, Q'.support ⊆ P.support → aeval w Q' = 0 →
      Q'.support.card < Q.support.card → Q' = 0 := by
    intro Q' h1 h2 h3
    by_contra h0
    exact Nat.find_min hex (hQcard ▸ h3) ⟨Q', h0, h1, h2, rfl⟩

  obtain ⟨m, hm⟩ := ne_zero_iff.mp hQ0
  set c : K := Q.coeff m with hc
  have hmsupp : m ∈ Q.support := mem_support_iff.mpr hm
  set Q₁ : MvPolynomial ι K := c⁻¹ • Q with hQ₁
  have hQ₁supp : Q₁.support = Q.support := support_smul_eq (inv_ne_zero hm) Q
  have hQ₁m : Q₁.coeff m = 1 := by
    rw [hQ₁, coeff_smul, smul_eq_mul, ← hc, inv_mul_cancel₀ hm]
  have hQ₁w : aeval w Q₁ = 0 := by rw [hQ₁, map_smul, hQw, smul_zero]

  set D : MvPolynomial ι K := Q₁ - map (frobenius K p) Q₁ with hD
  have hDw : aeval (fun i => w i ^ p) D = 0 := by
    rw [hD, map_sub, aeval_pow_eq_zero_of_aeval_eq_zero φ hwφ hQ₁w, ← frobenius_aeval, hQ₁w,
      map_zero, sub_zero]
  have hDsupp : D.support ⊆ Q.support.erase m := by
    intro m' hm'
    rw [Finset.mem_erase]
    refine ⟨?_, ?_⟩
    · rintro rfl
      rw [mem_support_iff, hD, coeff_sub, coeff_map, hQ₁m, map_one, sub_self] at hm'
      exact hm' rfl
    · have hsub := support_sub (p := Q₁) (q := map (frobenius K p) Q₁)
      rcases Finset.mem_union.mp (hsub hm') with h | h
      · rwa [← hQ₁supp]
      · rw [← hQ₁supp]
        exact support_map_subset _ _ h

  set D₁ : MvPolynomial ι K := map ((frobeniusEquiv K p).symm : K →+* K) D with hD₁
  have hD₁D : map (frobenius K p) D₁ = D := by
    rw [hD₁, map_map]
    have : (frobenius K p).comp ((frobeniusEquiv K p).symm : K →+* K) = RingHom.id K := by
      ext a
      exact frobenius_apply_frobeniusEquiv_symm K p a
    rw [this, map_id]
  have hD₁w : aeval w D₁ = 0 := by
    apply frobenius_inj F p
    rw [frobenius_aeval, hD₁D, hDw, map_zero]
  have hD₁supp : D₁.support = D.support :=
    support_map_of_injective _ (frobeniusEquiv K p).symm.injective
  have hD₁zero : D₁ = 0 := by
    apply hmin D₁
    · rw [hD₁supp]
      exact hDsupp.trans ((Finset.erase_subset _ _).trans hQsupp)
    · exact hD₁w
    · rw [hD₁supp]
      exact (Finset.card_le_card hDsupp).trans_lt (Finset.card_erase_lt_of_mem hmsupp)
  have hD0 : D = 0 := by rw [← hD₁D, hD₁zero, map_zero]

  have hfix : ∀ m', (Q₁.coeff m') ^ p = Q₁.coeff m' := by
    intro m'
    have h := congrArg (coeff m') hD0
    rw [hD, coeff_sub, coeff_map, coeff_zero, sub_eq_zero, frobenius_def] at h
    exact h.symm
  have hrange : Q₁ ∈ Set.range (map (algebraMap (ZMod p) K)) := by
    rw [mem_range_map_iff_coeffs_subset]
    intro c' hc'
    obtain ⟨m', -, rfl⟩ := mem_coeffs_iff.mp hc'
    exact exists_algebraMap_eq_of_pow_eq (hfix m')
  obtain ⟨P₀, hP₀⟩ := hrange
  have hP₀supp : P₀.support = Q₁.support := by
    rw [← hP₀]
    exact (support_map_of_injective P₀ (algebraMap (ZMod p) K).injective).symm
  refine ⟨P₀, ?_, ?_, ?_⟩
  · rintro rfl
    rw [map_zero] at hP₀
    have h := hQ₁m
    rw [← hP₀, coeff_zero] at h
    exact zero_ne_one h
  · rw [hP₀supp, hQ₁supp]
    exact hQsupp
  ·
    have h1 : aeval w P₀ = 0 := by
      rw [← aeval_map_algebraMap K w P₀, hP₀]
      exact hQ₁w
    apply frobenius_inj F p
    rw [map_zero, frobenius_aeval, ZMod.frobenius_zmod, map_id]
    exact h1

theorem algebraicIndependent_of_algebraicIndependent_zmod [CharP K p] [CharP F p]
    [PerfectRing K p] [Algebra (ZMod p) K] [Algebra (ZMod p) F] [IsScalarTower (ZMod p) K F]
    {ι : Type*} {z : ι → F} (hz : ∀ i, φ (z i) = z i ^ p)
    (h : AlgebraicIndependent (ZMod p) z) : AlgebraicIndependent K z := by
  rw [algebraicIndependent_iff]
  intro P hP
  by_contra hP0
  obtain ⟨P₀, hP₀0, -, hP₀z⟩ := exists_relation_zmod_of_relation φ hz hP0 hP
  exact hP₀0 (h.eq_zero_of_aeval_eq_zero P₀ hP₀z)

end Descent

section Form

open IntermediateField

variable {K F : Type*} [Field K] [Field F] [Algebra K F] {p : ℕ} [Fact p.Prime]
  [CharP F p] [Algebra (ZMod p) F] (φ : F →ₐ[K] F)

omit [CharP F p] in

theorem apply_algebraMap_zmod (a : ZMod p) : φ (algebraMap (ZMod p) F a) = algebraMap (ZMod p) F a := by
  have h : (φ : F →+* F).comp (algebraMap (ZMod p) F) = algebraMap (ZMod p) F := Subsingleton.elim _ _
  exact RingHom.congr_fun h a

omit [CharP F p] in

theorem not_algebraicIndependent_of_val {ι : Type*} (E : IntermediateField (ZMod p) F)
    (z' : ι → E) (h : ¬ AlgebraicIndependent (ZMod p) (fun i => (z' i : F))) :
    ¬ AlgebraicIndependent (ZMod p) z' := fun h' =>
  h (h'.map' (f := E.val) (fun _ _ hab => Subtype.ext hab))

variable [CharP K p] [PerfectRing K p] [Algebra (ZMod p) K] [IsScalarTower (ZMod p) K F]

theorem exists_primeField_form (S : Set F) (hS : ∀ s ∈ S, φ s = s ^ p)
    (hgenS : IntermediateField.adjoin K S = ⊤)
    (hF : ∃ x : F, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F) :
    ∃ E : IntermediateField (ZMod p) F,
      (∃ s : Finset E, IntermediateField.adjoin (ZMod p) (s : Set E) = ⊤) ∧
      IntermediateField.adjoin K (Set.range (algebraMap E F)) = ⊤ ∧
      (∀ y : E, φ (algebraMap E F y) = algebraMap E F (y ^ Nat.card (ZMod p))) ∧
      AlgebraicCurve.IsCurveOver (ZMod p) E := by
  classical
  obtain ⟨x, hx, hxfin⟩ := hF
  haveI := hxfin
  set Kx : IntermediateField K F := IntermediateField.adjoin K ({x} : Set F) with hKx

  haveI : Algebra.EssFiniteType K Kx :=
    essFiniteType_iff.mpr (fg_adjoin_of_finite (Set.finite_singleton x))
  haveI : Algebra.EssFiniteType Kx F := inferInstance
  haveI : Algebra.EssFiniteType K F := Algebra.EssFiniteType.comp K Kx F
  obtain ⟨G, hG⟩ := IntermediateField.fg_top K F
  have hmem : ∀ g : F, ∃ Tg : Finset F, (Tg : Set F) ⊆ S ∧
      g ∈ IntermediateField.adjoin K (Tg : Set F) :=
    fun g => exists_finset_of_mem_adjoin (by rw [hgenS]; exact mem_top)
  choose Tg hTgS hTg using hmem
  set T : Finset F := G.biUnion Tg with hTdef
  have hTS : (T : Set F) ⊆ S := by
    intro y hy
    obtain ⟨g, -, hyg⟩ := Finset.mem_biUnion.mp (Finset.mem_coe.mp hy)
    exact hTgS g hyg
  have hTφ : ∀ y ∈ (T : Set F), φ y = y ^ p := fun y hy => hS y (hTS hy)
  have hTtopK : IntermediateField.adjoin K (T : Set F) = ⊤ := by
    apply top_le_iff.mp
    rw [← hG]
    apply adjoin_le_iff.mpr
    intro g hg
    have h1 : IntermediateField.adjoin K (Tg g : Set F) ≤ IntermediateField.adjoin K (T : Set F) :=
      adjoin.mono K _ _ (fun y hy => Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨g, hg, hy⟩))
    exact h1 (hTg g)

  have htex : ∃ t ∈ T, Transcendental K t := by
    by_contra hcon
    have hint : ∀ y ∈ (T : Set F), IsIntegral K y := fun y hy => by
      have : IsAlgebraic K y := by
        by_contra h
        exact hcon ⟨y, hy, h⟩
      exact this.isIntegral
    haveI : Algebra.IsAlgebraic K (IntermediateField.adjoin K (T : Set F)) := isAlgebraic_adjoin hint
    have hxmem : x ∈ IntermediateField.adjoin K (T : Set F) := by rw [hTtopK]; exact mem_top
    have h1 : IsAlgebraic K (⟨x, hxmem⟩ : IntermediateField.adjoin K (T : Set F)) :=
      Algebra.IsAlgebraic.isAlgebraic _
    exact hx (IntermediateField.isAlgebraic_iff.mp h1)
  obtain ⟨t, htT, htK⟩ := htex
  have ht0 : Transcendental (ZMod p) t := Transcendental.of_tower_top (ZMod p) htK

  set E : IntermediateField (ZMod p) F := IntermediateField.adjoin (ZMod p) (T : Set F) with hEdef
  have hTE : (T : Set F) ⊆ E := subset_adjoin _ _
  set t' : E := ⟨t, hTE htT⟩ with ht'def
  have ht'0 : Transcendental (ZMod p) t' := fun h => ht0 (IntermediateField.isAlgebraic_iff.mp h)

  have hEφ : ∀ y : E, φ (y : F) = (y : F) ^ p := by
    intro y
    have hy : (y : F) ∈ IntermediateField.adjoin (ZMod p) (T : Set F) := y.2
    refine adjoin_induction (F := ZMod p) (p := fun w _ => φ w = w ^ p) ?_ ?_ ?_ ?_ ?_ hy
    · exact hTφ
    · intro a
      rw [apply_algebraMap_zmod, ← map_pow, ZMod.pow_card]
    · intro a b _ _ ha hb
      rw [map_add, ha, hb, add_pow_char]
    · intro a _ ha
      rw [map_inv₀, ha, inv_pow]
    · intro a b _ _ ha hb
      rw [map_mul, ha, hb, mul_pow]

  set ιt : Type _ := (({t'} : Set E) : Type _) with hιt
  set xt : ιt → F := fun i => ((i : E) : F) with hxtdef
  set xt' : ιt → E := fun i => (i : E) with hxt'def
  have hxt_apply : ∀ i : ιt, xt i = t := fun i => by
    have h := i.2
    rw [Set.mem_singleton_iff] at h
    show ((i : E) : F) = t
    rw [h]
  have hxt'_apply : ∀ i : ιt, xt' i = t' := fun i => by
    have h := i.2
    rw [Set.mem_singleton_iff] at h
    exact h
  have hxtind : AlgebraicIndependent K xt :=
    (algebraicIndependent_singleton_iff (⟨t', Set.mem_singleton t'⟩ : ιt)).mpr
      (by rw [hxt_apply]; exact htK)
  have hxt'ind : AlgebraicIndependent (ZMod p) xt' :=
    (algebraicIndependent_singleton_iff (⟨t', Set.mem_singleton t'⟩ : ιt)).mpr
      (by rw [hxt'_apply]; exact ht'0)

  set ιx : Type _ := (({x} : Set F) : Type _) with hιx
  have hxind : AlgebraicIndependent K (Subtype.val : ιx → F) :=
    (algebraicIndependent_singleton_iff (⟨x, Set.mem_singleton x⟩ : ιx)).mpr hx
  have halgKx : Algebra.IsAlgebraic
      (IntermediateField.adjoin K (Set.range (Subtype.val : ιx → F))) F := by
    rw [Subtype.range_coe]
    exact Algebra.IsAlgebraic.of_finite Kx F
  have halgKx' : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range (Subtype.val : ιx → F))) F := by
    open scoped IntermediateField.algebraAdjoinAdjoin in
    exact (IsFractionRing.comap_isAlgebraic_iff
      (A := Algebra.adjoin K (Set.range (Subtype.val : ιx → F)))
      (K := IntermediateField.adjoin K (Set.range (Subtype.val : ιx → F))) (C := F)).mpr halgKx
  have hbx : IsTranscendenceBasis K (Subtype.val : ιx → F) :=
    hxind.isTranscendenceBasis_iff_isAlgebraic.mpr halgKx'
  have htr1 : Algebra.trdeg K F = 1 := by
    rw [← hbx.cardinalMk_eq_trdeg]
    exact Cardinal.mk_singleton x
  have hbt : IsTranscendenceBasis K xt :=
    hxtind.isTranscendenceBasis_of_trdeg_le_of_finite (by rw [htr1]; exact (Cardinal.mk_singleton t').ge)
  haveI halgKt : Algebra.IsAlgebraic (Algebra.adjoin K (Set.range xt)) F := hbt.isAlgebraic

  set K₁ : IntermediateField (ZMod p) E := IntermediateField.adjoin (ZMod p) (Set.range xt') with hK₁
  set T'' : Set E := ((↑) : E → F) ⁻¹' (T : Set F) with hT''
  have hgenalg : ∀ y ∈ T'', IsAlgebraic K₁ y := by
    intro y hy

    set zK : Option ιt → F := fun o => o.elim (y : F) xt with hzK
    have hzKφ : ∀ o, φ (zK o) = zK o ^ p := by
      rintro (_ | i)
      · exact hEφ y
      · exact hEφ _
    have hnotK : ¬ AlgebraicIndependent K zK := by
      rw [hzK, hxtind.option_iff_transcendental]
      exact fun htr => htr (Algebra.IsAlgebraic.isAlgebraic _)

    have hnot0 : ¬ AlgebraicIndependent (ZMod p) zK := fun h0 =>
      hnotK (algebraicIndependent_of_algebraicIndependent_zmod φ hzKφ h0)

    set zE : Option ιt → E := fun o => o.elim y xt' with hzE
    have hzEval : (fun o => (zE o : F)) = zK := by
      funext o
      rcases o with _ | i <;> rfl
    have hnotE : ¬ AlgebraicIndependent (ZMod p) zE :=
      not_algebraicIndependent_of_val E zE (by rw [hzEval]; exact hnot0)
    rw [hzE, hxt'ind.option_iff_transcendental] at hnotE
    have halg : IsAlgebraic (Algebra.adjoin (ZMod p) (Set.range xt')) y := by
      by_contra h
      exact hnotE h
    open scoped IntermediateField.algebraAdjoinAdjoin in
    exact (IsFractionRing.isAlgebraic_iff (Algebra.adjoin (ZMod p) (Set.range xt')) K₁ E).mp halg

  have hvalT'' : ((↑) : E → F) '' T'' = (T : Set F) :=
    Set.image_preimage_eq_of_subset (by
      intro y hy
      exact ⟨⟨y, hTE hy⟩, rfl⟩)
  have hT''top : IntermediateField.adjoin (ZMod p) T'' = (⊤ : IntermediateField (ZMod p) E) := by
    apply lift_injective
    rw [lift_adjoin, lift_top, hvalT'']
  have hK₁top : IntermediateField.adjoin K₁ T'' = (⊤ : IntermediateField K₁ E) := by
    apply restrictScalars_injective (ZMod p)
    rw [restrictScalars_top, adjoin_adjoin_left]
    apply top_le_iff.mp
    rw [← hT''top]
    exact adjoin.mono _ _ _ Set.subset_union_right
  haveI : Finite T'' :=
    ((T.finite_toSet).preimage Subtype.val_injective.injOn).to_subtype
  haveI hK₁fin : FiniteDimensional K₁ (IntermediateField.adjoin K₁ T'') :=
    finiteDimensional_adjoin (fun y hy => (hgenalg y hy).isIntegral)
  set eK₁ : (IntermediateField.adjoin K₁ T'') ≃ₐ[K₁] E :=
    (equivOfEq hK₁top).trans topEquiv with heK₁
  have hfinE : FiniteDimensional K₁ E := LinearEquiv.finiteDimensional eK₁.toLinearEquiv
  have hfinE' : FiniteDimensional (IntermediateField.adjoin (ZMod p) ({t'} : Set E)) E := by
    have hr : Set.range xt' = ({t'} : Set E) := by
      rw [hxt'def]
      exact Subtype.range_coe
    rw [← hr]
    exact hfinE

  refine ⟨E, ?_, ?_, ?_, ?_⟩
  · refine ⟨T.preimage ((↑) : E → F) Subtype.val_injective.injOn, ?_⟩
    rw [Finset.coe_preimage]
    exact hT''top
  · apply top_le_iff.mp
    rw [← hTtopK]
    apply adjoin_le_iff.mpr
    intro y hy
    exact subset_adjoin _ _ ⟨⟨y, hTE hy⟩, rfl⟩
  · intro y
    rw [Nat.card_zmod]
    exact hEφ y
  · exact AlgebraicCurve.isCurveOver_of_transcendental_of_perfectField ht'0 hfinE'

end Form

end P2mTorsStruct

end

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
open P2mTorsStruct in
theorem solution
    (K : Type*) [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))
    (hF : ∃ x : ModularCurve.qExpFunctionFieldC K Γ, Transcendental K x ∧
      FiniteDimensional (IntermediateField.adjoin K ({x} : Set (ModularCurve.qExpFunctionFieldC K Γ)))
        (ModularCurve.qExpFunctionFieldC K Γ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : (ℓ : K) ≠ 0) :
    AlgebraicCurve.AbelJacobiCard K (ModularCurve.qExpFunctionFieldC K Γ) ℓ
      (AlgebraicCurve.genusFF K (ModularCurve.qExpFunctionFieldC K Γ)) := by
  classical

  letI algZK : Algebra (ZMod p) K := ZMod.algebra K p
  letI algZF : Algebra (ZMod p) (ModularCurve.qExpFunctionFieldC K Γ) :=
    ((algebraMap K (ModularCurve.qExpFunctionFieldC K Γ)).comp (algebraMap (ZMod p) K)).toAlgebra
  letI : SMul (ZMod p) (ModularCurve.qExpFunctionFieldC K Γ) := algZF.toSMul
  letI : Module (ZMod p) (ModularCurve.qExpFunctionFieldC K Γ) := algZF.toModule
  haveI : IsScalarTower (ZMod p) K (ModularCurve.qExpFunctionFieldC K Γ) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : CharP (ModularCurve.qExpFunctionFieldC K Γ) p :=
    charP_of_injective_algebraMap (algebraMap K (ModularCurve.qExpFunctionFieldC K Γ)).injective p

  set φ := ModularCurve.qExpFrobeniusModL K Γ p with hφ
  set S : Set (ModularCurve.qExpFunctionFieldC K Γ) :=
    ((↑) : ModularCurve.qExpFunctionFieldC K Γ → LaurentSeries K) ⁻¹' ModularCurve.intFormRatiosC K Γ
    with hSdef
  have hS : ∀ s ∈ S, φ s = s ^ p := by
    intro s hs
    obtain ⟨k, f, g, pf, pg, hf, hg, hg0, hsv⟩ := hs
    apply Subtype.ext
    rw [hφ, ModularCurve.coe_qExpFrobeniusModL]
    push_cast
    rw [hsv, map_div₀, ModularCurve.qExpand_intSeriesC_eq_pow, ModularCurve.qExpand_intSeriesC_eq_pow,
      div_pow]

  have hgenS : IntermediateField.adjoin K S = ⊤ := by
    apply eq_top_iff.mpr
    intro z _
    set M : IntermediateField K (LaurentSeries K) :=
      (IntermediateField.adjoin K S).map (ModularCurve.qExpFunctionFieldC K Γ).val with hM
    have hle : ModularCurve.qExpFunctionFieldC K Γ ≤ M := by
      show IntermediateField.adjoin K (ModularCurve.intFormRatiosC K Γ) ≤ M
      apply IntermediateField.adjoin_le_iff.mpr
      intro w hw
      show w ∈ (M : Set (LaurentSeries K))
      rw [hM, IntermediateField.coe_map]
      refine ⟨⟨w, ModularCurve.intFormRatiosC_subset K Γ hw⟩, ?_, rfl⟩
      exact IntermediateField.subset_adjoin K S
        (show (⟨w, _⟩ : ModularCurve.qExpFunctionFieldC K Γ) ∈ S from hw)
    have hz : (z : LaurentSeries K) ∈ (M : Set (LaurentSeries K)) := hle z.2
    rw [hM, IntermediateField.coe_map] at hz
    obtain ⟨y, hy, hyz⟩ := hz
    have hyz' : y = z := Subtype.ext hyz
    rw [← hyz']
    exact hy

  obtain ⟨E, hfg, hgen, hφE, hcurve⟩ := exists_primeField_form φ S hS hgenS hF
  haveI := hcurve
  obtain ⟨x, hx, hxfin⟩ := hF
  haveI := hxfin
  haveI : AlgebraicCurve.IsCurveOver K (ModularCurve.qExpFunctionFieldC K Γ) :=
    AlgebraicCurve.isCurveOver_of_isAlgClosed_of_transcendental x hx
  exact AlgebraicCurve.Pic0.abelJacobiCard_genusFF_of_frobenius (ZMod p) K E
    (ModularCurve.qExpFunctionFieldC K Γ) hfg hgen φ hφE ℓ hℓ

end S_ModularCurve_abelJacobiCard_genusFF_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_abelJacobiCard_genusFF_qExpFunctionFieldC (solution)
