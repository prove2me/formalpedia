-- Prove2me | solution 1 for GoodReductionJacobian.AbelianSchemePropertyBundle.exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/43b3a03f-0131-5c96-8ca5-e693731d7532

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cech_baseChange_equiv_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_unit_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_AffHom_nonempty_H0_equiv_and_HSucc_equiv_of_bijective
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_of_isPullback
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_subsingleton_HSucc_unit_of_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial AlgebraicGeometry.Scheme.Hom.opensMapFinal AlgebraicGeometry.RelPicard.RigidifiedLineBundle.setoid AlgebraicGeometry.RelPicard.RigidifiedLineBundle.instInhabited AlgebraicGeometry.Scheme.PresheafOfModules.symmetricCategory SheafOfModules.instFaithfulRingSheafPModToPMod SheafOfModules.symmetricCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.PresheafOfModules.monoidalClosed SheafOfModules.instFullRingSheafPModToPMod SheafOfModules.monoidalCategory AlgebraicGeometry.Scheme.Modules.symmetricCategory SheafOfModules.monoidalClosed SheafOfModules.instIsLocalizationPModRingSheafSheafifyFunctorPresheafW SheafOfModules.sheafifyFunctor_monoidal AlgebraicGeometry.Scheme.Modules.monoidalClosed AlgebraicGeometry.instMonoidalPresheafOfModulesModulesSheafify AlgebraicGeometry.Scheme.Modules.monoidalCategory PresheafOfModules.instMonoidalClosed PresheafOfModules.InternalHom.instModuleCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies PresheafOfModules.InternalHom.instModuleCarrierObjOppositeRingCatCompCommRingCatForget₂RingHomCarrierCarrierAbPresheaf PresheafOfModules.InternalHom.instSMulCarrierObjOppositeCommRingCatSubtypePiFamilyMemAddSubgroupNaturalFamilies AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.baseChangePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_coe GoodReductionJacobian.RelativeGroupLaw.baseChange_inv GoodReductionJacobian.RelativeGroupLaw.baseChangePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.baseChange_mul GoodReductionJacobian.RelativeGroupLaw.baseChange_one GoodReductionJacobian.RelativeGroupLaw.nsmul_zero GoodReductionJacobian.RelativeGroupLaw.mem_torsionSubset GoodReductionJacobian.RelativeGroupLaw.nsmul_succ NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst NeronSpecialFibreInfra.neronEndRestrictEquiv_apply NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd NeronSpecialFibreInfra.neronEndExtension_genericFibreRestrict NeronSpecialFibreInfra.specClosedFibreInclusion_eq NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_fst_assoc NeronSpecialFibreInfra.specialFibreRestrict_coe_comp_snd_assoc NeronSpecialFibreInfra.genericFibreRestrict_neronEndExtension NeronSpecialFibreInfra.homOverId_coe NeronSpecialFibreInfra.homOverComp_coe NeronSpecialFibreInfra.fibreRestrictAlong_coe_comp_snd_assoc GoodReductionJacobian.RelativeGroupLaw.fibre_inv GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_coe GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_toBase GoodReductionJacobian.RelativeGroupLaw.fibre_mul"
p2m_attr_erase "simp" "GoodReductionJacobian.RelativeGroupLaw.fibrePointToBase_ofBase GoodReductionJacobian.RelativeGroupLaw.fibre_one GoodReductionJacobian.RelativeGroupLaw.fibrePointOfBase_coe AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RigidifiedLineBundle.mk.injEq GoodReductionJacobian.relativeGroupLawOfGrpObj_inv GoodReductionJacobian.relativeGroupLawOfGrpObj_mul GoodReductionJacobian.overHomEquivSchemeHomOver_apply_coe GoodReductionJacobian.relativeGroupLawOfGrpObj_one GoodReductionJacobian.overHomEquivSchemeHomOver_symm_apply_left SheafOfModules.tensorUnit_eq AlgebraicGeometry.Scheme.Modules.tensorUnit_eq PresheafOfModules.InternalHom.presheaf_map_apply PresheafOfModules.InternalHom.curryFamily_app PresheafOfModules.InternalHom.add_app PresheafOfModules.InternalHom.smul_app PresheafOfModules.InternalHom.zero_app PresheafOfModules.ihomObj_map_val PresheafOfModules.ihomFunctor_map PresheafOfModules.InternalHom.restrict_app PresheafOfModules.InternalHom.postcomp_app PresheafOfModules.InternalHom.neg_app PresheafOfModules.curry'_app_val PresheafOfModules.InternalHom.presheaf_obj PresheafOfModules.ihomFunctor_obj PresheafOfModules.ihomObj_obj PresheafOfModules.InternalHom.sub_app PresheafOfModules.ihomMap_app_val AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap"
p2m_attr_erase "simp" "AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap"
p2m_attr_erase "simp" "ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces"

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian IsLocalRing
open scoped TensorProduct

universe u

namespace P2mFibreTransfer

open AlgebraicGeometry.OModulePresheaf

section ChainIso

variable {R : Type*} [CommRing R]
variable {C₀ C₁ C₂ D₀ D₁ D₂ : Type*}
  [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁] [AddCommGroup C₂] [Module R C₂]
  [AddCommGroup D₀] [Module R D₀] [AddCommGroup D₁] [Module R D₁] [AddCommGroup D₂] [Module R D₂]

theorem map_ker_eq_ker (d : C₀ →ₗ[R] C₁) (d' : D₀ →ₗ[R] D₁) (φ₀ : C₀ ≃ₗ[R] D₀) (φ₁ : C₁ ≃ₗ[R] D₁)
    (h : ∀ x, φ₁ (d x) = d' (φ₀ x)) :
    (LinearMap.ker d).map (φ₀ : C₀ →ₗ[R] D₀) = LinearMap.ker d' := by
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker, LinearEquiv.coe_coe]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← h, hx, map_zero]
  · intro hy
    refine ⟨φ₀.symm y, ?_, φ₀.apply_symm_apply y⟩
    apply φ₁.injective
    rw [h, φ₀.apply_symm_apply, hy, map_zero]

def kerEquiv (d : C₀ →ₗ[R] C₁) (d' : D₀ →ₗ[R] D₁) (φ₀ : C₀ ≃ₗ[R] D₀) (φ₁ : C₁ ≃ₗ[R] D₁)
    (h : ∀ x, φ₁ (d x) = d' (φ₀ x)) : LinearMap.ker d ≃ₗ[R] LinearMap.ker d' :=
  LinearEquiv.ofSubmodules φ₀ _ _ (map_ker_eq_ker d d' φ₀ φ₁ h)

theorem kerEquiv_coe (d : C₀ →ₗ[R] C₁) (d' : D₀ →ₗ[R] D₁) (φ₀ : C₀ ≃ₗ[R] D₀) (φ₁ : C₁ ≃ₗ[R] D₁)
    (h : ∀ x, φ₁ (d x) = d' (φ₀ x)) (x : LinearMap.ker d) :
    ((kerEquiv d d' φ₀ φ₁ h x : LinearMap.ker d') : D₀) = φ₀ x := rfl

theorem kerEquiv_symm_coe (d : C₀ →ₗ[R] C₁) (d' : D₀ →ₗ[R] D₁) (φ₀ : C₀ ≃ₗ[R] D₀) (φ₁ : C₁ ≃ₗ[R] D₁)
    (h : ∀ x, φ₁ (d x) = d' (φ₀ x)) (y : LinearMap.ker d') :
    (((kerEquiv d d' φ₀ φ₁ h).symm y : LinearMap.ker d) : C₀) = φ₀.symm y := by
  rw [LinearEquiv.eq_symm_apply, ← kerEquiv_coe d d' φ₀ φ₁ h, LinearEquiv.apply_symm_apply]

def hsuccEquiv (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂) (d₀' : D₀ →ₗ[R] D₁) (d₁' : D₁ →ₗ[R] D₂)
    (φ₀ : C₀ ≃ₗ[R] D₀) (φ₁ : C₁ ≃ₗ[R] D₁) (φ₂ : C₂ ≃ₗ[R] D₂)
    (h₀ : ∀ x, φ₁ (d₀ x) = d₀' (φ₀ x)) (h₁ : ∀ x, φ₂ (d₁ x) = d₁' (φ₁ x)) :
    (LinearMap.ker d₁ ⧸ (LinearMap.range d₀).comap (LinearMap.ker d₁).subtype) ≃ₗ[R]
      (LinearMap.ker d₁' ⧸ (LinearMap.range d₀').comap (LinearMap.ker d₁').subtype) :=
  Submodule.Quotient.equiv _ _ (kerEquiv d₁ d₁' φ₁ φ₂ h₁) (by
    ext y
    simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_range,
      LinearEquiv.coe_coe]
    constructor
    · rintro ⟨x, ⟨c, hc⟩, rfl⟩
      exact ⟨φ₀ c, by rw [kerEquiv_coe, ← h₀, hc]⟩
    · rintro ⟨c, hc⟩
      refine ⟨(kerEquiv d₁ d₁' φ₁ φ₂ h₁).symm y, ⟨φ₀.symm c, ?_⟩, LinearEquiv.apply_symm_apply _ _⟩
      rw [kerEquiv_symm_coe, LinearEquiv.eq_symm_apply, h₀, φ₀.apply_symm_apply, hc])

end ChainIso

theorem cech_equiv_of_cochainEquiv {R : Type u} [CommRing R] {V W : Scheme.{u}}
    {π : V ⟶ Spec (.of R)} {π' : W ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (G : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : W.OrderedAffineCover)
    (φ : ∀ i, F.cochain K i ≃ₗ[R] G.cochain K' i)
    (hφ : ∀ (i : ℕ) (c : F.cochain K i), φ (i + 1) (F.d K i c) = G.d K' i (φ i c)) :
    Nonempty (F.H0 K ≃ₗ[R] G.H0 K') ∧ ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] G.HSucc K' i) :=
  ⟨⟨kerEquiv _ _ (φ 0) (φ 1) (hφ 0)⟩,
    fun i => ⟨hsuccEquiv _ _ _ _ (φ i) (φ (i + 1)) (φ (i + 2)) (hφ i) (hφ (i + 1))⟩⟩

section PushComap

variable {R : Type u} [CommRing R] {V W : Scheme.{u}} {π : V ⟶ Spec (.of R)}

noncomputable def resEquivOfEq {π' : W ⟶ Spec (.of R)} (H : OModulePresheaf π') {U U' : W.Opens} (h : U = U') :
    H.obj U' ≃ₗ[R] H.obj U :=
  { H.res h.le with
    invFun := H.res h.ge
    left_inv := fun x => by
      show H.res h.ge (H.res h.le x) = x
      rw [H.res_res]; exact H.res_refl_apply U' x
    right_inv := fun x => by
      show H.res h.le (H.res h.ge x) = x
      rw [H.res_res]; exact H.res_refl_apply U x }

theorem resEquivOfEq_apply {π' : W ⟶ Spec (.of R)} (H : OModulePresheaf π') {U U' : W.Opens} (h : U = U')
    (x : H.obj U') : resEquivOfEq H h x = H.res h.le x := rfl

variable (γ : W ⟶ V) [IsAffineHom γ] (H : OModulePresheaf (γ ≫ π)) (K : V.OrderedAffineCover)

noncomputable def pushforwardCochainEquiv (i : ℕ) :
    (pushforward π γ H).cochain K i ≃ₗ[R] H.cochain (K.comap γ) i where
  toFun c s := H.res (K.comap_inter γ s).le (c s)
  invFun c s := H.res (K.comap_inter γ s).ge (c s)
  map_add' c c' := funext fun s => map_add _ _ _
  map_smul' r c := funext fun s => LinearMap.map_smul _ r (c s)
  left_inv c := funext fun s => by
    show H.res _ (H.res _ (c s)) = c s
    rw [H.res_res]; exact H.res_refl_apply _ (c s)
  right_inv c := funext fun s => by
    show H.res _ (H.res _ (c s)) = c s
    rw [H.res_res]; exact H.res_refl_apply _ (c s)

theorem pushforwardCochainEquiv_apply (i : ℕ) (c : (pushforward π γ H).cochain K i) (s : K.Idx i) :
    pushforwardCochainEquiv γ H K i c s = H.res (K.comap_inter γ s).le (c s) := rfl

theorem pushforwardCochainEquiv_d (i : ℕ) (c : (pushforward π γ H).cochain K i) :
    pushforwardCochainEquiv γ H K (i + 1) ((pushforward π γ H).d K i c)
      = H.d (K.comap γ) i (pushforwardCochainEquiv γ H K i c) := by
  funext s
  have hd : (pushforward π γ H).d K i c s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      H.res ((TopologicalSpace.Opens.map γ.base).monotone (K.inter_le_inter_face s j)) (c (K.face s j)) :=
    OModulePresheaf.d_apply _ _ _ _ _
  rw [pushforwardCochainEquiv_apply, hd, map_sum, OModulePresheaf.d_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, H.res_res, pushforwardCochainEquiv_apply, H.res_res]
  rfl

theorem pushforward_cech_equiv :
    Nonempty ((pushforward π γ H).H0 K ≃ₗ[R] H.H0 (K.comap γ)) ∧
      ∀ i : ℕ, Nonempty ((pushforward π γ H).HSucc K i ≃ₗ[R] H.HSucc (K.comap γ) i) :=
  cech_equiv_of_cochainEquiv _ _ K (K.comap γ) (pushforwardCochainEquiv γ H K) (pushforwardCochainEquiv_d γ H K)

end PushComap

section IsoTransport

variable {R : Type u} [CommRing R] {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of R)) (f : Y ⟶ X)

noncomputable def appAffHom : AffHom (unit πX) (pushforwardUnit πX f) where
  app U :=
    { toFun := fun x => (f.app U.1).hom x
      map_add' := fun x y => map_add _ x y
      map_smul' := fun r x => by
        letI := Scheme.TwoAffineOpenCover.algebraOfHom πX U.1
        letI := Scheme.TwoAffineOpenCover.algebraOfHom (f ≫ πX) (f ⁻¹ᵁ U.1)
        show (f.app U.1).hom (algebraMap R Γ(X, U.1) r * (show Γ(X, U.1) from x))
          = algebraMap R Γ(Y, f ⁻¹ᵁ U.1) r * (f.app U.1).hom x
        rw [map_mul, ← OModulePresheaf.appLE_algebraMap (π := πX) f U.1 r, Scheme.Hom.appLE_eq_app] }
  app_smul U a x := by
    show (f.app U.1).hom (a * (show Γ(X, U.1) from x)) = (f.appLE U.1 (f ⁻¹ᵁ U.1) le_rfl).hom a * (f.app U.1).hom x
    rw [Scheme.Hom.appLE_eq_app, map_mul]
  naturality {U U'} h := by
    refine LinearMap.ext fun x => ?_
    show (f.app U.1).hom ((X.presheaf.map (homOfLE h).op).hom x)
      = (Y.presheaf.map (homOfLE ((TopologicalSpace.Opens.map f.base).monotone h)).op).hom ((f.app U'.1).hom x)
    rw [← CommRingCat.comp_apply, f.naturality]
    rfl

theorem appAffHom_apply (U : X.affineOpens) (x : Γ(X, U.1)) :
    (appAffHom πX f).app U x = (f.app U.1).hom x := rfl

theorem appAffHom_bijective [IsIso f] (U : X.affineOpens) : Function.Bijective ((appAffHom πX f).app U) :=
  ConcreteCategory.bijective_of_isIso (f.app U.1)

theorem unit_cech_congr {π₁ π₂ : Y ⟶ Spec (.of R)} (h : π₁ = π₂) (K : Y.OrderedAffineCover) :
    Nonempty ((unit π₁).H0 K ≃ₗ[R] (unit π₂).H0 K) ∧
      ∀ i : ℕ, Nonempty ((unit π₁).HSucc K i ≃ₗ[R] (unit π₂).HSucc K i) := by
  subst h
  exact ⟨⟨LinearEquiv.refl _ _⟩, fun _ => ⟨LinearEquiv.refl _ _⟩⟩

theorem unit_cech_equiv_of_iso [IsSeparated πX] (e : Y ≅ X) (πY : Y ⟶ Spec (.of R)) (he : e.hom ≫ πX = πY)
    (K : X.OrderedAffineCover) :
    Nonempty ((unit πX).H0 K ≃ₗ[R] (unit πY).H0 (K.comap e.hom)) ∧
      ∀ i : ℕ, Nonempty ((unit πX).HSucc K i ≃ₗ[R] (unit πY).HSucc (K.comap e.hom) i) := by
  have hA := OModulePresheaf.AffHom.nonempty_H0_equiv_and_HSucc_equiv_of_bijective (appAffHom πX e.hom)
    (fun U => appAffHom_bijective πX e.hom U) K
  have hB := pushforward_cech_equiv (π := πX) e.hom (unit (e.hom ≫ πX)) K
  have hC := unit_cech_congr (h := he) (K.comap e.hom)
  obtain ⟨⟨a0⟩, aS⟩ := hA
  obtain ⟨⟨b0⟩, bS⟩ := hB
  obtain ⟨⟨c0⟩, cS⟩ := hC
  refine ⟨⟨a0.trans (b0.trans c0)⟩, fun i => ?_⟩
  obtain ⟨a⟩ := aS i
  obtain ⟨b⟩ := bS i
  obtain ⟨c⟩ := cS i
  exact ⟨a.trans (b.trans c)⟩

end IsoTransport

scoped instance opensMapFinal {X Y : Scheme.{u}} (f : X ⟶ Y) : (TopologicalSpace.Opens.map f.base).Final :=
  CategoryTheory.final_of_representablyFlat _

noncomputable def pullbackUnitIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (Scheme.Modules.pullback f).obj (SheafOfModules.unit Y.ringCatSheaf) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  haveI h : IsIso (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) := inferInstance
  @asIso _ _ _ _ _ h

theorem unit_eq_ofModules {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) :
    unit π = ofModules π (SheafOfModules.unit V.ringCatSheaf) :=
  rfl

theorem unit_cech_baseChange_field
    (k₀ : Type u) [Field k₀] (k : Type u) [Field k] [Algebra k₀ k]
    {X : Scheme.{u}} (fk : X ⟶ Spec (.of k₀)) [IsSeparated fk]
    [IsSeparated (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap k₀ k))]
    {Y : Scheme.{u}} (fY : Y ⟶ Spec (.of k)) [IsSeparated fY] (iY : Y ⟶ X)
    (hY : IsPullback iY fY fk (Scheme.TwoAffineOpenCover.specMap k₀ k))
    (𝒦 : X.OrderedAffineCover) (𝒦Y : Y.OrderedAffineCover) :
    Nonempty ((unit fY).H0 𝒦Y ≃ₗ[k] k ⊗[k₀] (unit fk).H0 𝒦) ∧
      ∀ n : ℕ, Nonempty ((unit fY).HSucc 𝒦Y n ≃ₗ[k] k ⊗[k₀] (unit fk).HSucc 𝒦 n) := by
  rw [unit_eq_ofModules fk]

  let e : Y ≅ pullback fk (Scheme.TwoAffineOpenCover.specMap k₀ k) := hY.isoPullback
  have he : e.hom ≫ pullback.snd fk (Scheme.TwoAffineOpenCover.specMap k₀ k) = fY := hY.isoPullback_hom_snd

  have h4 := (OModulePresheaf.nonempty_cech_baseChange_equiv_of_locallyTrivial fk 𝒦
    (SheafOfModules.unit X.ringCatSheaf) (fun x => ⟨⊤, trivial, ⟨pullbackUnitIso (⊤ : X.Opens).ι⟩⟩) k).2
    inferInstance

  have h3 := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso
    (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap k₀ k))
    (pullbackUnitIso (pullback.fst fk (Scheme.TwoAffineOpenCover.specMap k₀ k))) (𝒦.baseChange fk k)

  have h2 := unit_cech_equiv_of_iso (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap k₀ k)) e fY he
    (𝒦.baseChange fk k)

  have h1 := OModulePresheaf.nonempty_cechEquiv_unit_of_isSeparated fY 𝒦Y ((𝒦.baseChange fk k).comap e.hom)
  rw [← unit_eq_ofModules (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap k₀ k))] at h3
  refine ⟨?_, fun n => ?_⟩
  · obtain ⟨E4⟩ := h4.1
    obtain ⟨E3⟩ := h3.1
    obtain ⟨E2⟩ := h2.1
    obtain ⟨E1⟩ := h1.1
    exact ⟨E1.trans (E2.symm.trans (E3.symm.trans E4))⟩
  · obtain ⟨E4⟩ := h4.2 n
    obtain ⟨E3⟩ := h3.2.1 n
    obtain ⟨E2⟩ := h2.2 n
    obtain ⟨E1⟩ := h1.2 n
    exact ⟨E1.trans (E2.symm.trans (E3.symm.trans E4))⟩

theorem ker_le_ker_of_isArtinianRing
    {T' T : Type u} [CommRing T'] [IsLocalRing T'] [IsArtinianRing T'] [CommRing T]
    (π : T' →+* T) (hπ : Function.Surjective π)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    {k : Type u} [Field k] (ρ' : T →+* k) :
    RingHom.ker ρ ≤ RingHom.ker ρ' := by
  intro x hx
  obtain ⟨x', rfl⟩ := hπ x
  have hx' : x' ∈ maximalIdeal T' := by
    rw [← IsLocalRing.residue_eq_zero_iff, ← hρ]
    exact (RingHom.mem_ker).mp hx
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := T')
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  have hxn : x' ^ n = 0 := by
    have hmem := Ideal.pow_mem_pow hx' n
    rw [hn] at hmem
    exact (Submodule.mem_bot T').mp hmem
  refine (RingHom.mem_ker).mpr ?_
  have hnil : IsNilpotent (ρ' (π x')) := ⟨n, by rw [← map_pow, ← map_pow, hxn, map_zero, map_zero]⟩
  exact hnil.eq_zero

end P2mFibreTransfer
p2m_reactivate "P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField.P2mFibreTransfer"

open P2mFibreTransfer AlgebraicGeometry.OModulePresheaf in
theorem solution
    (T' T : Type u) [CommRing T'] [IsLocalRing T'] [IsArtinianRing T']
    [CommRing T] (π : T' →+* T) (hπ : Function.Surjective π) (hker : IsNilpotent (RingHom.ker π))
    {A₀ : Scheme.{u}} (f₀ : A₀ ⟶ Spec (CommRingCat.of T)) (h₀ : AbelianSchemePropertyBundle T f₀)
    (hH1 : ∃ (k : Type u) (_ : Field k) (_ : IsAlgClosed k)
      (Ak' : Scheme.{u}) (fk' : Ak' ⟶ Spec (CommRingCat.of k)) (i : Ak' ⟶ A₀) (ρ' : T →+* k)
      (_ : IsPullback i fk' f₀ (Spec.map (CommRingCat.ofHom ρ'))) (g : ℕ) (_ : SmoothOfRelativeDimension g fk')
      (𝒦 : Ak'.OrderedAffineCover), g ≤ (OModulePresheaf.unit fk').cechFinrank 𝒦 1)
    (ρ : T →+* ResidueField T') (hρ : ρ.comp π = residue T')
    {Ak : Scheme.{u}} (fk : Ak ⟶ Spec (CommRingCat.of (ResidueField T')))
    (i₀ : Ak ⟶ A₀) (hi₀ : IsPullback i₀ fk f₀ (Spec.map (CommRingCat.ofHom ρ))) :
    ∃ g : ℕ, ∀ 𝒦 : Ak.OrderedAffineCover,
      g ≤ (OModulePresheaf.unit fk).cechFinrank 𝒦 1 ∧
        ∀ n : ℕ, g ≤ n → Subsingleton ((OModulePresheaf.unit fk).HSucc 𝒦 n) := by
  obtain ⟨k, _instF, _instAC, Ak', fk', i, ρ', hi, g, _instSm, 𝒦', hg⟩ := hH1

  have hρsurj : Function.Surjective ρ := fun y => by
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    exact ⟨π x, by rw [← hρ]; rfl⟩
  have hkerle : RingHom.ker ρ ≤ RingHom.ker ρ' := ker_le_ker_of_isArtinianRing π hπ ρ hρ ρ'
  let j : ResidueField T' →+* k :=
    (Ideal.Quotient.lift (RingHom.ker ρ) ρ' fun x hx => (RingHom.mem_ker).mp (hkerle hx)).comp
      (RingHom.quotientKerEquivOfSurjective hρsurj).symm.toRingHom
  have hj : j.comp ρ = ρ' := by
    show ((Ideal.Quotient.lift (RingHom.ker ρ) ρ' fun x hx => (RingHom.mem_ker).mp (hkerle hx)).comp
      (RingHom.quotientKerEquivOfSurjective hρsurj).symm.toRingHom).comp ρ = ρ'
    rw [RingHom.comp_assoc, RingHom.quotientKerEquivOfSurjective_symm_comp]
    exact RingHom.ext fun x => Ideal.Quotient.lift_mk (RingHom.ker ρ) ρ' (fun a ha => (RingHom.mem_ker).mp (hkerle ha))
  letI : Algebra (ResidueField T') k := j.toAlgebra
  haveI : Module.Free (ResidueField T') k := Module.Free.of_divisionRing _ _
  haveI : Module.FaithfullyFlat (ResidueField T') k := inferInstance

  have hSpec : Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom ρ) = Spec.map (CommRingCat.ofHom ρ') := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hj]
  have hw : i ≫ f₀ = (fk' ≫ Spec.map (CommRingCat.ofHom j)) ≫ Spec.map (CommRingCat.ofHom ρ) := by
    rw [Category.assoc, hSpec]; exact hi.w
  have hi'₁ : hi₀.lift i (fk' ≫ Spec.map (CommRingCat.ofHom j)) hw ≫ i₀ = i := hi₀.lift_fst _ _ _
  have hi'₂ : hi₀.lift i (fk' ≫ Spec.map (CommRingCat.ofHom j)) hw ≫ fk = fk' ≫ Spec.map (CommRingCat.ofHom j) :=
    hi₀.lift_snd _ _ _
  have hi' : IsPullback (hi₀.lift i (fk' ≫ Spec.map (CommRingCat.ofHom j)) hw) fk' fk
      (Scheme.TwoAffineOpenCover.specMap (ResidueField T') k) := by
    refine IsPullback.of_right ?_ hi'₂ hi₀
    rw [hi'₁]
    show IsPullback i fk' f₀ (Spec.map (CommRingCat.ofHom j) ≫ Spec.map (CommRingCat.ofHom ρ))
    rw [hSpec]; exact hi

  have habk : AbelianSchemePropertyBundle (ResidueField T') fk := AbelianSchemePropertyBundle.of_isPullback h₀ hi₀
  have habk' : AbelianSchemePropertyBundle k fk' := AbelianSchemePropertyBundle.of_isPullback h₀ hi
  have habP : AbelianSchemePropertyBundle k
      (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap (ResidueField T') k)) :=
    AbelianSchemePropertyBundle.of_isPullback habk (IsPullback.of_hasPullback fk _)
  haveI : IsProper fk := habk.proper
  haveI : IsProper fk' := habk'.proper
  haveI : IsProper (pullback.snd fk (Scheme.TwoAffineOpenCover.specMap (ResidueField T') k)) := habP.proper

  refine ⟨g, fun 𝒦 => ?_⟩
  have hT := unit_cech_baseChange_field (ResidueField T') k fk fk' _ hi' 𝒦 𝒦'
  refine ⟨?_, fun n hn => ?_⟩
  ·
    obtain ⟨E⟩ := hT.2 0
    rw [OModulePresheaf.cechFinrank_succ] at hg ⊢
    haveI : Module.Free (ResidueField T') ((OModulePresheaf.unit fk).HSucc 𝒦 0) := Module.Free.of_divisionRing _ _
    rw [E.finrank_eq, Module.finrank_baseChange] at hg
    exact hg
  ·
    obtain ⟨E⟩ := hT.2 n
    have hv : Subsingleton ((OModulePresheaf.unit fk').HSucc 𝒦' n) :=
      AbelianSchemePropertyBundle.subsingleton_HSucc_unit_of_le k fk' habk' g 𝒦' n hn
    have hv' : Subsingleton (k ⊗[ResidueField T'] (OModulePresheaf.unit fk).HSucc 𝒦 n) :=
      E.symm.toEquiv.subsingleton
    exact (Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right (ResidueField T') k).mp hv'

end S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField
end P2MW
export P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_le_cechFinrank_and_subsingleton_HSucc_of_isPullback_residueField (solution)
