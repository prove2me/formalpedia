-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/d2ba2b92-21a6-532b-a067-9e8a8a1b3b49

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_zpow_iso_tensorPow_of_symmetric
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_of_isFinite_endKerStr
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_flat_of_isFinite
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_surjective_and_endDegree_eq_finrank_of_isFinite_of_flat
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_polynomial_forall_eulerChar_twist_tensorPow_eq
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_nonempty_pullback_tensorPow_iso
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_ofModules_of_locallyTrivial
import Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
import Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_GeometricallyIrreducible_geometricallyConnected
import Theorems.Thm_AlgebraicGeometry_OModulePresheaf_nonempty_cechEquiv_ofModules_of_iso
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.Modules.preservesBinaryProducts_opensMap AlgebraicGeometry.Scheme.Modules.pullback_monoidal AlgebraicGeometry.Scheme.Modules.sheafify_isLocalization' AlgebraicGeometry.Scheme.Modules.preservesTerminal_opensMap AlgebraicGeometry.Scheme.Modules.pullback₀_monoidal AlgebraicGeometry.Scheme.Modules.preservesFiniteProducts_opensMap AlgebraicGeometry.Scheme.Modules.instLiftingPresheafOfModulesSheafifyPresheafWOpensCarrierCarrierCommRingCatGrothendieckTopologyObjFunctorOppositeIsSheafSheafCompPullback₀Pullback PresheafOfModules.PullbackMonoidal.pullback_monoidal PresheafOfModules.PullbackMonoidal.isIso_δ PresheafOfModules.pushforward_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_η PresheafOfModules.free_monoidal PresheafOfModules.restrictScalars_laxMonoidal PresheafOfModules.PullbackMonoidal.isIso_δ_gS PresheafOfModules.pullback_oplaxMonoidal PresheafOfModules.PullbackMonoidal.instPreservesColimitsOfSizeCompOppositeCommRingCatRingCatForget₂RingHomCarrierCarrierPb PresheafOfModules.pullback_monoidal' AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.RelEffCartierDiv.isIso_subschemeIota_snd_of_degree_one AlgebraicGeometry.isIso_ker_graphOver_subschemeIota_snd AlgebraicGeometry.isClosedImmersion_graphOver AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion"
p2m_attr_erase "instance" "SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation"
p2m_attr_erase "instance" "instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup"
p2m_attr_erase "simp" "PresheafOfModules.freeεIso_hom_app PresheafOfModules.freeμIso_hom_app AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicCondition.mk.sizeOf_spec AlgebraicGeometry.RelPicard.RepresentsRelSubPic.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.RelPicard.SubPicCondition.onClasses_mk AlgebraicGeometry.RelPicard.relSubPicPresheaf_map_coe"
p2m_attr_erase "simp" "CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.injEq AlgebraicGeometry.RelPicard.SubPicGroupCondition.mk.sizeOf_spec AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul"
p2m_attr_erase "simp" "AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.qExpand_coeff_mul ModularCurve.qExpandₐ_apply ModularCurve.jqN_one ModularCurve.qExpand_single ModularCurve.dedekindPsi_one ModularCurve.ModularPolynomialData.mk.sizeOf_spec ModularCurve.evalAtJ_X ModularCurve.ModularPolynomialData.mk.injEq ModularCurve.constantCoeff_jNum ModularCurve.constantCoeff_eisenstein4 ModularCurve.qExpand_C ModularCurve.coeff_jq_neg_one ModularCurve.constantCoeff_jNumQ ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_ofRelEffDivisor AlgebraicGeometry.RelEffCartierDiv.toRelEffDivisor_I AlgebraicGeometry.mapOnProdOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.mk.sizeOf_spec AlgebraicGeometry.RelEffCartierDiv.mk.injEq AlgebraicGeometry.mapOnProdOver_snd AlgebraicGeometry.mapOnProdOver_fst AlgebraicGeometry.mapOnProdOver_snd_assoc AlgebraicGeometry.mapOnProdOver_id AlgebraicCurve.RelEffDivisor.mk.sizeOf_spec AlgebraicCurve.mapOnProd_fst AlgebraicCurve.mapOnProd_fst_assoc AlgebraicCurve.mapOnProd_snd AlgebraicCurve.UnivDivisorPack.mk.injEq AlgebraicCurve.RelEffDivisor.mk.injEq AlgebraicCurve.UnivDivisorPack.mk.sizeOf_spec AlgebraicCurve.mapOnProd_snd_assoc AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicGeometry.graphOver_fst_assoc AlgebraicGeometry.RelEffCartierDiv.toPoint_comp AlgebraicGeometry.RelEffCartierDiv.toPoint_comp_assoc AlgebraicGeometry.graphOver_fst AlgebraicGeometry.RelEffCartierDiv.ofPoint_I AlgebraicGeometry.graphOver_snd AlgebraicGeometry.graphOver_snd_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.algEquivZeroGroupCut_toSubPicCondition AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst"
p2m_attr_erase "simp" "CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open TopologicalSpace Opposite

universe u

namespace P2mDegNIsog

section V1

open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

local infixl:80 " ⊚ " => NeronModelInfra.schemeHomOverComp

section Points

variable (L : RelativeGroupLaw K f)

theorem compT_mul {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f)
    (β δ : SchemeHomOver f f) :
    z ⊚ (L.mul f β δ) = L.mul t (z ⊚ β) (z ⊚ δ) := by
  have h := L.mul_natural f t z.1 z.2 β δ
  have e : ∀ δ : SchemeHomOver f f, GoodReductionJacobian.schemeHomOverComp z.1 z.2 δ = z ⊚ δ :=
    fun δ => Subtype.ext rfl
  rw [e, e, e] at h
  exact h

theorem compT_one {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (z : SchemeHomOver t f) :
    z ⊚ (L.one f) = L.one t := by
  have h := L.one_natural f t z.1 z.2
  have e : GoodReductionJacobian.schemeHomOverComp z.1 z.2 (L.one f) = z ⊚ (L.one f) := Subtype.ext rfl
  rw [e] at h
  exact h

theorem pow_eq_nsmul {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x : SchemeHomOver t f) (n : ℕ) :
    letI := L.pointGroup t; x ^ n = L.nsmul t n x := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, ih]; rfl

theorem comp_idPoint {T : Scheme.{u}} {t : T ⟶ Spec (CommRingCat.of K)} (x : SchemeHomOver t f) :
    x ⊚ (RelativeGroupLaw.idPoint (f := f)) = x :=
  Subtype.ext (Category.comp_id _)

theorem isHom_nsmul (hc : L.IsCommutative) (n : ℕ) {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
    (x y : SchemeHomOver t f) :
    (L.mul t x y) ⊚ (L.nsmul f n RelativeGroupLaw.idPoint) =
      L.mul t (x ⊚ L.nsmul f n RelativeGroupLaw.idPoint) (y ⊚ L.nsmul f n RelativeGroupLaw.idPoint) := by
  induction n with
  | zero =>
      change (L.mul t x y) ⊚ (L.one f) = L.mul t (x ⊚ L.one f) (y ⊚ L.one f)
      rw [compT_one, compT_one, compT_one, L.one_mul]
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, compT_mul, compT_mul, compT_mul, ih, comp_idPoint, comp_idPoint,
        comp_idPoint]
      letI := L.pointCommGroup hc t
      change (x ⊚ L.nsmul f n RelativeGroupLaw.idPoint * (y ⊚ L.nsmul f n RelativeGroupLaw.idPoint)) * (x * y) =
        (x ⊚ L.nsmul f n RelativeGroupLaw.idPoint * x) * (y ⊚ L.nsmul f n RelativeGroupLaw.idPoint * y)
      exact mul_mul_mul_comm _ _ _ _

end Points

theorem isCommMonObj (L : RelativeGroupLaw K f) (hc : L.IsCommutative) :
    letI := L.grpObjOverMk; IsCommMonObj (Over.mk f) :=
  (L.isCommMonObj_grpObjOverMk_iff_mul_comm).mpr (fun t x y => hc t x y)

private theorem _root_.P2mDegNIsog.geometricallyConnected [IsAlgClosed K] (hA : AbelianSchemePropertyBundle K f) :
    GeometricallyConnected f := by
  haveI : IsIntegral A := GoodReductionJacobian.AbelianSchemePropertyBundle.isIntegral_of_field hA
  haveI : IrreducibleSpace A := inferInstance
  haveI : GeometricallyIrreducible f := GeometricallyIrreducible.of_irreducibleSpace_of_isAlgClosed f
  exact GeometricallyIrreducible.geometricallyConnected f

p2m_export "P2mDegNIsog" "geometricallyConnected"

def unbundleHom (L : RelativeGroupLaw K f) :
    letI := L.grpObjOverMk; letI := L.pointGroup f;
    (Over.mk f ⟶ Over.mk f) →* SchemeHomOver f f :=
  letI := L.grpObjOverMk; letI := L.pointGroup f
  { toFun := overHomToSchemeHomOver
    map_one' := L.overHomToSchemeHomOver_one f
    map_mul' := fun a b => L.overHomToSchemeHomOver_mul f a b }

theorem toOverHom_idPoint : schemeHomOverToOverHom (RelativeGroupLaw.idPoint (f := f)) = 𝟙 (Over.mk f) :=
  Over.OverMorphism.ext (by simp [schemeHomOverToOverHom])

theorem left_one_zpow_natCast (L : RelativeGroupLaw K f) (n : ℕ) :
    letI := L.grpObjOverMk;
    ((𝟙 (Over.mk f)) ^ (n : ℤ)).left = (L.nsmul f n RelativeGroupLaw.idPoint).1 := by
  letI := L.grpObjOverMk; letI := L.pointGroup f
  rw [zpow_natCast]
  have h := map_pow (unbundleHom L) (𝟙 (Over.mk f)) n
  change overHomToSchemeHomOver ((𝟙 (Over.mk f)) ^ n) = (overHomToSchemeHomOver (𝟙 (Over.mk f))) ^ n at h
  rw [← toOverHom_idPoint, overHomToSchemeHomOver_schemeHomOverToOverHom, pow_eq_nsmul L f] at h
  rw [toOverHom_idPoint] at h
  exact congrArg Subtype.val h

theorem left_one_inv (L : RelativeGroupLaw K f) :
    letI := L.grpObjOverMk;
    ((𝟙 (Over.mk f))⁻¹).left = (L.inv f RelativeGroupLaw.idPoint).1 := by
  letI := L.grpObjOverMk
  have h := L.overHomToSchemeHomOver_inv f (𝟙 (Over.mk f))
  rw [← toOverHom_idPoint, overHomToSchemeHomOver_schemeHomOverToOverHom] at h
  rw [toOverHom_idPoint] at h
  exact congrArg Subtype.val h

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  Skeleton.toSkeleton_tensorObj X Y

theorem cls_unit : toSkeleton (𝟙_ C) = (1 : Skeleton C) := Skeleton.one_eq.symm

end Skel

theorem cls_tensorPow {Z : Scheme.{u}} (N : Z.Modules) (n : ℕ) :
    toSkeleton (N.tensorPow n) = toSkeleton N ^ n := by
  induction n with
  | zero => rw [Scheme.Modules.tensorPow_zero, cls_unit, pow_zero]
  | succ n ih => rw [Scheme.Modules.tensorPow_succ, cls_tensor, ih, pow_succ]

theorem exists_orderedAffineCover (hf : IsProper f) : Nonempty A.OrderedAffineCover := by
  haveI : QuasiCompact f := inferInstance
  haveI : CompactSpace (Spec (CommRingCat.of K)) := inferInstanceAs (CompactSpace (PrimeSpectrum K))
  haveI : CompactSpace A := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : A.affineOpens => ((V : A.Opens) : Set A))
    (fun V => (V : A.Opens).isOpen) (by
      intro x _
      have hx : x ∈ ((⊤ : A.Opens) : Set A) := trivial
      rw [← iSup_affineOpens_eq_top A, TopologicalSpace.Opens.coe_iSup] at hx
      exact hx)
  letI : LinearOrder (s : Set A.affineOpens) :=
    LinearOrder.lift' (fun i => Fintype.equivFin (s : Set A.affineOpens) i) (Equiv.injective _)
  refine ⟨⟨(s : Set A.affineOpens), fun i => (i.1 : A.Opens), fun i => i.1.2, ?_⟩⟩
  apply le_antisymm le_top
  intro x _
  have hx := hs (Set.mem_univ x)
  rw [TopologicalSpace.Opens.mem_iSup]
  simp only [Set.mem_iUnion] at hx
  obtain ⟨V, hV, hxV⟩ := hx
  exact ⟨⟨V, hV⟩, hxV⟩

theorem eulerChar_congr {M M' : A.Modules} (e : M ≅ M') (𝒦 : A.OrderedAffineCover) :
    (OModulePresheaf.ofModules f M).eulerChar 𝒦 = (OModulePresheaf.ofModules f M').eulerChar 𝒦 := by
  obtain ⟨⟨e0⟩, hS, -⟩ := OModulePresheaf.nonempty_cechEquiv_ofModules_of_iso f e 𝒦
  have h : ∀ i, (OModulePresheaf.ofModules f M).cechFinrank 𝒦 i = (OModulePresheaf.ofModules f M').cechFinrank 𝒦 i := by
    intro i
    cases i with
    | zero => exact e0.finrank_eq
    | succ j => obtain ⟨e⟩ := hS j; exact e.finrank_eq
  rw [OModulePresheaf.eulerChar_def, OModulePresheaf.eulerChar_def]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

section Alg

p2m_open "Polynomial AlgebraicGeometry.Polynomial"

def dil (q : ℚ[X]) (c : ℚ) : ℚ[X] := q.sum fun i a => C (a * c ^ i) * X ^ i

theorem dil_eval (q : ℚ[X]) (c m : ℚ) : (dil q c).eval m = q.eval (c * m) := by
  rw [dil, Polynomial.sum, eval_finsetSum, eval_eq_sum, Polynomial.sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [eval_mul, eval_C, eval_pow, eval_X, mul_pow]
  ring

theorem dil_coeff (q : ℚ[X]) (c : ℚ) (g : ℕ) : (dil q c).coeff g = c ^ g * q.coeff g := by
  rw [dil, Polynomial.sum, finsetSum_coeff]
  simp only [coeff_C_mul, coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · ring
  · rw [mem_support_iff, not_not] at h
    rw [h, mul_zero]

end Alg

end V1

namespace Isog

open AlgebraicGeometry.OModulePresheaf

section Chi

variable {R : Type u} [CommRing R]

theorem eulerChar_eq_of_equiv {V V' : Scheme.{u}} {π : V ⟶ Spec (.of R)} {π' : V' ⟶ Spec (.of R)}
    (F : OModulePresheaf π) (F' : OModulePresheaf π') (K : V.OrderedAffineCover) (K' : V'.OrderedAffineCover)
    (hcard : Fintype.card K.ι = Fintype.card K'.ι)
    (h0 : Nonempty (F.H0 K ≃ₗ[R] F'.H0 K')) (hs : ∀ i : ℕ, Nonempty (F.HSucc K i ≃ₗ[R] F'.HSucc K' i)) :
    F.eulerChar K = F'.eulerChar K' := by
  have h : ∀ i, F.cechFinrank K i = F'.cechFinrank K' i := by
    intro i
    cases i with
    | zero => obtain ⟨e⟩ := h0; exact e.finrank_eq
    | succ j => obtain ⟨e⟩ := hs j; exact e.finrank_eq
  rw [eulerChar_def, eulerChar_def, hcard]
  exact Finset.sum_congr rfl fun i _ => by rw [h i]

theorem eulerChar_ofModules_congr {V : Scheme.{u}} {π π' : V ⟶ Spec (.of R)} (h : π = π') (X : V.Modules)
    (K : V.OrderedAffineCover) : (ofModules π X).eulerChar K = (ofModules π' X).eulerChar K := by
  subst h; rfl

end Chi

section PushUnit

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem preimage_eq_bot (U : V.Opens) (hU : (U : Set V) = ∅) : ι ⁻¹ᵁ U = ⊥ := by
  ext z
  simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
  intro hz
  have : ι.base z ∈ (U : Set V) := hz
  rw [hU] at this
  exact this

theorem subsingleton_sections_of_eq_bot (W : Z.Opens) (h : W = ⊥) : Subsingleton Γ(Z, W) := by
  subst h
  infer_instance

theorem supportedIn_top : (pushforwardUnit π ι).SupportedIn ⊤ := fun U hU =>
  subsingleton_sections_of_eq_bot (ι ⁻¹ᵁ U.1)
    (preimage_eq_bot ι U.1 (by simpa [Closeds.coe_top, Set.inter_univ] using hU))

theorem res_rfl (W : Z.Opens) (x : Γ(Z, W)) : Z.presheaf.map (homOfLE (le_refl W)).op x = x := by
  rw [Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W)), Z.presheaf.map_id]; rfl

theorem appLE_rfl_apply (U : V.Opens) (a : Γ(V, U)) : ι.appLE U (ι ⁻¹ᵁ U) le_rfl a = ι.app U a := by
  show Z.presheaf.map (homOfLE (le_refl _)).op (ι.app U a) = _
  exact res_rfl (ι ⁻¹ᵁ U) _

theorem isCoherent [IsFinite ι] : (pushforwardUnit π ι).IsCoherent := by
  intro U
  have hfin : (ι.app U.1).hom.Finite := IsFinite.finite_app ι U.1 U.2
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := by
    ext a; exact appLE_rfl_apply ι U.1 a
  letI : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hfin' : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact hfin
    exact this
  exact hfin'

theorem loc_core [IsAffineHom ι] (U : V.affineOpens) (g : Γ(Z, ι ⁻¹ᵁ U.1)) (W' : Z.Opens) (hle : W' ≤ ι ⁻¹ᵁ U.1)
    (hW' : W' = Z.basicOpen g) :
    (∀ x : Γ(Z, W'), ∃ (n : ℕ) (y : Γ(Z, ι ⁻¹ᵁ U.1)),
        Z.presheaf.map (homOfLE hle).op y = Z.presheaf.map (homOfLE hle).op (g ^ n) * x) ∧
      (∀ y : Γ(Z, ι ⁻¹ᵁ U.1), Z.presheaf.map (homOfLE hle).op y = 0 → ∃ n : ℕ, g ^ n * y = 0) := by
  subst hW'
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  haveI : IsLocalization.Away g Γ(Z, Z.basicOpen g) := hW.isLocalization_basicOpen g
  have halg : ∀ y : Γ(Z, ι ⁻¹ᵁ U.1),
      algebraMap Γ(Z, ι ⁻¹ᵁ U.1) Γ(Z, Z.basicOpen g) y = Z.presheaf.map (homOfLE hle).op y := fun y => by
    rw [Subsingleton.elim (homOfLE hle) (homOfLE (Z.basicOpen_le g))]; rfl
  constructor
  · intro x
    obtain ⟨⟨y, ⟨_, n, rfl⟩⟩, h⟩ := IsLocalization.surj (Submonoid.powers g) x
    refine ⟨n, y, ?_⟩
    rw [← halg, ← halg, ← h, mul_comm]
  · intro y hy
    rw [← halg] at hy
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalization.map_eq_zero_iff (Submonoid.powers g) _ _).mp hy
    exact ⟨n, hn⟩

theorem preimage_basicOpen_eq (U : V.affineOpens) (f : Γ(V, U.1)) :
    ι ⁻¹ᵁ V.basicOpen f = Z.basicOpen (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f) := by
  rw [appLE_rfl_apply]; exact Scheme.preimage_basicOpen ι f

theorem pre_le (U : V.affineOpens) (f : Γ(V, U.1)) : ι ⁻¹ᵁ V.basicOpen f ≤ ι ⁻¹ᵁ U.1 :=
  fun _ hx => V.basicOpen_le f hx

theorem smul_basicOpen (U : V.affineOpens) (f : Γ(V, U.1)) (a : Γ(V, U.1)) (x : Γ(Z, ι ⁻¹ᵁ V.basicOpen f)) :
    ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op).hom a •
        (show (pushforwardUnit π ι).obj (V.basicOpen f) from x)) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from
        Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a) * x) := by
  show ι.appLE (V.basicOpen f) (ι ⁻¹ᵁ V.basicOpen f) le_rfl ((V.presheaf.map (homOfLE (V.basicOpen_le f)).op) a) * x
    = _
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.map_appLE, Scheme.Hom.appLE_map]

theorem smul_top (U : V.affineOpens) (a : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (a • (show (pushforwardUnit π ι).obj U.1 from y)) =
      (show (pushforwardUnit π ι).obj U.1 from ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl a * y) := rfl

theorem res_eq (U : V.affineOpens) (f : Γ(V, U.1)) (y : Γ(Z, ι ⁻¹ᵁ U.1)) :
    (pushforwardUnit π ι).res (V.basicOpen_le f) (show (pushforwardUnit π ι).obj U.1 from y) =
      (show (pushforwardUnit π ι).obj (V.basicOpen f) from Z.presheaf.map (homOfLE (pre_le ι U f)).op y) := by
  show Z.presheaf.map _ y = _
  rw [Subsingleton.elim (homOfLE ((Opens.map ι.base).monotone (V.basicOpen_le f))) (homOfLE (pre_le ι U f))]

theorem isQuasicoherent [IsAffineHom ι] : (pushforwardUnit π ι).IsQuasicoherent := by
  intro U f
  set g : Γ(Z, ι ⁻¹ᵁ U.1) := ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl f with hg
  obtain ⟨h1, h2⟩ := loc_core ι U g (ι ⁻¹ᵁ V.basicOpen f) (pre_le ι U f) (preimage_basicOpen_eq ι U f)
  constructor
  · intro x
    obtain ⟨n, y, hy⟩ := h1 x
    refine ⟨n, y, ?_⟩
    rw [res_eq, smul_basicOpen]
    show Z.presheaf.map (homOfLE (pre_le ι U f)).op y =
      Z.presheaf.map (homOfLE (pre_le ι U f)).op (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n)) *
        (show Γ(Z, ι ⁻¹ᵁ V.basicOpen f) from x)
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hy
  · intro y hy
    rw [res_eq] at hy
    obtain ⟨n, hn⟩ := h2 y hy
    refine ⟨n, ?_⟩
    rw [smul_top]
    show ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl (f ^ n) * (show Γ(Z, ι ⁻¹ᵁ U.1) from y) = 0
    rw [map_pow (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom]
    exact hn

end PushUnit

section Rank

variable {R : Type u} [CommRing R] {V Z : Scheme.{u}} (π : V ⟶ Spec (.of R)) (ι : Z ⟶ V)

theorem finrank_comp_iso {X Y Y' : Scheme.{u}} (g : X ⟶ Y) [Flat g] [IsFinite g] (e : Y ≅ Y') (z : Y') :
    Scheme.Hom.finrank (g ≫ e.hom) z = Scheme.Hom.finrank g (e.inv.base z) := by
  have sq : IsPullback (𝟙 X) (g ≫ e.hom) g e.inv := IsPullback.of_horiz_isIso ⟨by simp⟩
  exact Scheme.Hom.finrank_of_isPullback _ _ _ _ sq z

theorem rankAtStalk_pushforwardUnit_obj [IsFinite ι] [Flat ι] (U : V.affineOpens) (r : ℕ)
    (hr : ∀ y : V, Scheme.Hom.finrank ι y = r) (𝔭 : PrimeSpectrum Γ(V, U.1)) :
    Module.rankAtStalk (R := Γ(V, U.1)) ((pushforwardUnit π ι).obj U.1) 𝔭 = r := by
  have heq : ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl = ι.app U.1 := Scheme.Hom.appLE_eq_app ι
  letI alg : Algebra Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  haveI : Module.Finite Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Finite := by rw [heq]; exact IsFinite.finite_app ι U.1 U.2
    exact this
  haveI : Module.Flat Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) := by
    have : (ι.appLE U.1 (ι ⁻¹ᵁ U.1) le_rfl).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) (f := ι) inferInstance U ⟨ι ⁻¹ᵁ U.1, U.2.preimage ι⟩ le_rfl
    exact this
  have key := Scheme.Hom.finrank_SpecMap_algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1) 𝔭
  have hmap : CommRingCat.ofHom (algebraMap Γ(V, U.1) Γ(Z, ι ⁻¹ᵁ U.1)) = ι.app U.1 := by
    rw [← heq]; rfl
  rw [hmap] at key

  have hU : IsAffineOpen U.1 := U.2
  have hW : IsAffineOpen (ι ⁻¹ᵁ U.1) := U.2.preimage ι
  have hnat : Spec.map (ι.app U.1) = hW.isoSpec.inv ≫ ((ι ∣_ U.1) ≫ hU.isoSpec.hom) := by
    rw [IsAffineOpen.isoSpec_hom, ← Scheme.Opens.toSpecΓ_naturality, ← Category.assoc,
      IsAffineOpen.isoSpec_inv_toSpecΓ, Category.id_comp]
  have hfr : Scheme.Hom.finrank (Spec.map (ι.app U.1)) 𝔭 = r := by
    rw [hnat, Scheme.Hom.finrank_comp_left_of_isIso, finrank_comp_iso,
      Scheme.Hom.finrank_of_isPullback _ _ _ _ (isPullback_morphismRestrict ι U.1).flip]
    exact hr _
  rw [hfr] at key
  exact key.symm

end Rank

section Setup

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

theorem connectedSpace (hA : AbelianSchemePropertyBundle K f) : ConnectedSpace A := by
  have h := hA.connectedFibres (IsLocalRing.closedPoint K)
  have h' : _root_.IsConnected (Set.univ : Set A) := by
    convert h using 1
    exact (Set.eq_univ_of_forall fun _ => Subsingleton.elim _ _).symm
  exact connectedSpace_iff_univ.mpr h'

theorem krullDim_top_le (g : ℕ) [SmoothOfRelativeDimension g f] :
    topologicalKrullDim ((⊤ : Closeds A) : Set A) ≤ g :=
  (Topology.IsInducing.topologicalKrullDim_le (Topology.IsEmbedding.subtypeVal.isInducing)).trans
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g)

theorem exists_chart_prime [IsIntegral A] [Nonempty A] (𝒦 : A.OrderedAffineCover) :
    ∃ (U₀ : A.affineOpens) (𝔭 : PrimeSpectrum Γ(A, U₀.1)), (∃ i, U₀.1 = 𝒦.U i) ∧ 𝔭.asIdeal = ⊥ := by
  obtain ⟨a⟩ := (inferInstance : Nonempty A)
  have ha : a ∈ (⊤ : A.Opens) := trivial
  rw [← 𝒦.iSup_eq_top, Opens.mem_iSup] at ha
  obtain ⟨i, hi⟩ := ha
  haveI : Nonempty (𝒦.U i) := ⟨⟨a, hi⟩⟩
  exact ⟨⟨𝒦.U i, 𝒦.isAffineOpen i⟩, ⟨⊥, Ideal.isPrime_bot⟩, ⟨i, rfl⟩, rfl⟩

end Setup

section Chain

variable {K : Type u} [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))

theorem isInvertible_tensorPow {𝓛 : A.Modules} (h𝓛 : Scheme.Modules.IsInvertible 𝓛) (n : ℕ) :
    Scheme.Modules.IsInvertible (𝓛.tensorPow n) := by
  induction n with
  | zero => exact Scheme.Modules.isInvertible_unit A
  | succ n ih => exact ih.tensor h𝓛

variable [IsSeparated f] (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f) [IsAffineHom γ.1]

include h𝓛 in

theorem eulerChar_twist_eq (m : ℕ) :
    ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
  have hN : Scheme.Modules.IsInvertible (𝓛.tensorPow m) := isInvertible_tensorPow h𝓛 m

  have e1 : ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)).eulerChar 𝒦 =
      (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap γ.1) := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_pullback_comap_twist_pushforwardUnit f γ.1 𝒦 (𝓛.tensorPow m) hN.1
    exact (eulerChar_eq_of_equiv (ofModules (γ.1 ≫ f) ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      ((pushforwardUnit f γ.1).twist (𝓛.tensorPow m)) (𝒦.comap γ.1) 𝒦 rfl h0 hs).symm

  have e2 := eulerChar_ofModules_congr γ.2 ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)) (𝒦.comap γ.1)

  have hq : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).IsQuasicoherent :=
    isQuasicoherent_ofModules_of_locallyTrivial f _ (hN.pullback γ.1).1
  have e3 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar (𝒦.comap γ.1) =
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 := by
    obtain ⟨h0, hs⟩ := nonempty_cechEquiv_ofModules_of_isQuasicoherent_of_isSeparated f
      ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)) hq (𝒦.comap γ.1) 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))) (𝒦.comap γ.1) 𝒦 rfl h0 hs

  have e4 : (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m))).eulerChar 𝒦 =
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 := by
    obtain ⟨e⟩ := Scheme.Modules.nonempty_pullback_tensorPow_iso γ.1 𝓛 m
    obtain ⟨h0, hs, -⟩ := nonempty_cechEquiv_ofModules_of_iso f e 𝒦
    exact eulerChar_eq_of_equiv (ofModules f ((Scheme.Modules.pullback γ.1).obj (𝓛.tensorPow m)))
      (ofModules f (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)) 𝒦 𝒦 rfl h0 hs
  rw [e1, e2, e3, e4]

end Chain

section ProjIsog

variable (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
  (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]
  (𝒦 : A.OrderedAffineCover) (𝓛 : A.Modules) (h𝓛 : Scheme.Modules.IsInvertible 𝓛)
  (γ : SchemeHomOver f f)
  (hγ : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K)) (x y : SchemeHomOver t f),
    NeronModelInfra.schemeHomOverComp (L.mul t x y) γ =
      L.mul t (NeronModelInfra.schemeHomOverComp x γ) (NeronModelInfra.schemeHomOverComp y γ))
  (hfin : IsFinite (L.endKerStr γ))
  (p q : Polynomial ℚ)
  (hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback γ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) = p.eval (m : ℚ))
  (hq : ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPow m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ))

include hA hγ hfin hp hq h𝓛 in

theorem coeff_eq_endDegree_mul_coeff : p.coeff g = (L.endDegree γ : ℚ) * q.coeff g := by
  classical
  haveI := hA.proper
  haveI := hA.smooth
  haveI : ConnectedSpace A := connectedSpace hA
  haveI : IsIntegral A := AbelianSchemePropertyBundle.isIntegral_of_field hA

  haveI := hfin
  haveI : IsFinite γ.1 := RelativeGroupLaw.isFinite_of_isFinite_endKerStr K f L γ hγ
  haveI : Flat γ.1 := AbelianSchemePropertyBundle.flat_of_isFinite K hA γ
  obtain ⟨-, -, hrank⟩ := RelativeGroupLaw.surjective_and_endDegree_eq_finrank_of_isFinite_of_flat K f L γ

  set G : OModulePresheaf f := pushforwardUnit f γ.1 with hG
  have hGc : G.IsCoherent := isCoherent f γ.1
  have hGq : G.IsQuasicoherent := isQuasicoherent f γ.1
  have hGs : G.SupportedIn ⊤ := supportedIn_top f γ.1

  obtain ⟨p', -, hp'⟩ := exists_polynomial_forall_eulerChar_twist_tensorPow_eq f 𝒦 G hGc hGq ⊤ hGs g
    (krullDim_top_le (f := f) g) 𝓛 h𝓛.1

  have hpp : p' = p := by
    refine Polynomial.eq_of_infinite_eval_eq p' p
      ((Set.infinite_range_of_injective Nat.cast_injective).mono ?_)
    rintro _ ⟨m, rfl⟩
    show p'.eval (m : ℚ) = p.eval (m : ℚ)
    rw [← hp' m, ← hp m, hG, eulerChar_twist_eq f 𝒦 𝓛 h𝓛 γ m]

  obtain ⟨U₀, 𝔭, -, h𝔭⟩ := exists_chart_prime (A := A) 𝒦
  have hlead := coeff_eq_rankAtStalk_mul_coeff_of_forall_eulerChar_twist_tensorPow_eq f 𝒦 𝓛 h𝓛.1 g
    (SmoothOfRelativeDimension.topologicalKrullDim_le f g) q hq G hGc hGq p' hp' U₀ 𝔭 h𝔭
  have hrk : Module.rankAtStalk (R := Γ(A, U₀.1)) (G.obj U₀.1) 𝔭 = L.endDegree γ :=
    rankAtStalk_pushforwardUnit_obj f γ.1 U₀ (L.endDegree γ) (fun y => (hrank y).symm) 𝔭
  rw [← hpp, hlead, hrk]

end ProjIsog

end Isog

section Tail

open scoped CategoryTheory.MonObj

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}

section EtaleKernel

theorem locallyOfFinitePresentation_of_field (q : A ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType q] : LocallyOfFinitePresentation q := by
  haveI : IsNoetherianRing (Γ(Spec (CommRingCat.of K), ⊤) : CommRingCat.{u}) :=
    isNoetherianRing_of_ringEquiv K
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have h := (HasRingHomProperty.iff_of_source_openCover (P := @LocallyOfFiniteType)
    (f := q) A.affineCover).mp inferInstance
  exact HasRingHomProperty.of_source_openCover (P := @LocallyOfFinitePresentation)
    A.affineCover (fun i => RingHom.FinitePresentation.of_finiteType.mp (h i))

theorem etale_endKerStr_nsmul (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    [LocallyOfFiniteType f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  have hunit : IsUnit (n : K) := isUnit_iff_ne_zero.mpr hn
  haveI hfu : FormallyUnramified (L.schemeNsmul n) :=
    GoodReductionJacobian.RelativeGroupLaw.formallyUnramified_schemeNsmul_of_isUnit_of_isLocalRing
      L (fun t x y => hc t x y) n hunit
  haveI : FormallyUnramified (L.nsmul f n RelativeGroupLaw.idPoint).1 := hfu
  haveI : LocallyOfFiniteType ((L.nsmul f n RelativeGroupLaw.idPoint).1 ≫ f) := by
    rw [(L.nsmul f n RelativeGroupLaw.idPoint).2]; infer_instance
  haveI : LocallyOfFiniteType (L.nsmul f n RelativeGroupLaw.idPoint).1 :=
    locallyOfFiniteType_of_comp _ f
  haveI : FormallyUnramified (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFiniteType (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    MorphismProperty.pullback_snd _ _ inferInstance
  haveI : LocallyOfFinitePresentation (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) :=
    locallyOfFinitePresentation_of_field _
  haveI : Flat (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := inferInstance
  exact Etale.of_formallyUnramified_of_flat _

theorem isFinite_endKerStr_nsmul [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative)
    (hA : AbelianSchemePropertyBundle K f) (n : ℕ) (hn : (n : K) ≠ 0) :
    IsFinite (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := by
  haveI : IsProper f := hA.proper
  haveI : Etale (L.endKerStr (L.nsmul f n RelativeGroupLaw.idPoint)) := etale_endKerStr_nsmul L hc n hn
  exact (GoodReductionJacobian.RelativeGroupLaw.isFinite_endKerStr_and_natCard_eq_endDegree_of_etale
    K f L (L.nsmul f n RelativeGroupLaw.idPoint)).1

end EtaleKernel

section Main

variable [IsAlgClosed K] (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
  (g : ℕ) [SmoothOfRelativeDimension g f]

include hc hA

theorem main (n : ℕ) (hn : (n : K) ≠ 0) : L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g) := by

  obtain ⟨𝒦⟩ := exists_orderedAffineCover (f := f) hA.proper
  obtain ⟨𝓛, h𝓛, hsym, q, hq0, hq⟩ :=
    RelativeGroupLaw.exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq
      K f L hA g 𝒦

  letI := L.grpObjOverMk
  haveI := isCommMonObj L hc
  have hsym' : Nonempty ((Scheme.Modules.pullback ((𝟙 (Over.mk f))⁻¹).left).obj 𝓛 ≅ 𝓛) := by
    rw [left_one_inv L]; exact hsym
  set φ : SchemeHomOver f f := L.nsmul f n RelativeGroupLaw.idPoint with hφ
  have hN : Nonempty ((Scheme.Modules.pullback φ.1).obj 𝓛 ≅ 𝓛.tensorPow (n * n)) := by
    have h := Scheme.Modules.nonempty_pullback_zpow_iso_tensorPow_of_symmetric K f hA.smooth hA.proper
      (geometricallyConnected (f := f) hA) 𝓛 h𝓛 hsym' (n : ℤ)
    rw [left_one_zpow_natCast L n, show ((n : ℤ) * (n : ℤ)).toNat = n * n by
      rw [← Nat.cast_mul]; exact Int.toNat_natCast (n * n)] at h
    exact h
  obtain ⟨eN⟩ := hN

  have hcls : ∀ m : ℕ, Nonempty ((((Scheme.Modules.pullback φ.1).obj 𝓛).tensorPow m) ≅ 𝓛.tensorPow (n * n * m)) := by
    intro m
    apply toSkeleton_eq_toSkeleton_iff.mp
    rw [cls_tensorPow, cls_tensorPow, toSkeleton_eq_toSkeleton_iff.mpr ⟨eN⟩, cls_tensorPow, ← pow_mul]

  have hp : ∀ m : ℕ, ((OModulePresheaf.ofModules f
      (((Scheme.Modules.pullback φ.1).obj 𝓛).tensorPow m)).eulerChar 𝒦 : ℚ) =
        (dil q ((n : ℚ) * n)).eval (m : ℚ) := by
    intro m
    obtain ⟨e⟩ := hcls m
    rw [eulerChar_congr (f := f) e 𝒦, hq (n * n * m), dil_eval]
    push_cast
    ring_nf

  have hfinKer : IsFinite (L.endKerStr φ) := isFinite_endKerStr_nsmul L hc hA n hn
  have key := Isog.coeff_eq_endDegree_mul_coeff K f L hA g 𝒦 𝓛 h𝓛
    φ (fun {T} t x y => isHom_nsmul L hc n t x y) hfinKer (dil q ((n : ℚ) * n)) q hp hq
  rw [dil_coeff] at key
  have hq0' : q.coeff g ≠ 0 := ne_of_gt hq0
  have h1 : ((L.endDegree φ : ℕ) : ℚ) = ((n : ℚ) * n) ^ g := mul_right_cancel₀ hq0' key.symm
  have h2 : ((L.endDegree φ : ℕ) : ℚ) = ((n ^ (2 * g) : ℕ) : ℚ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2

end Main

end Tail

end P2mDegNIsog

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    L.endDegree (L.nsmul f n RelativeGroupLaw.idPoint) = n ^ (2 * g) :=
  P2mDegNIsog.main L hc hA g n hn

end

end S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_nsmul_idPoint_eq_pow_of_natCast_ne_zero (solution)
