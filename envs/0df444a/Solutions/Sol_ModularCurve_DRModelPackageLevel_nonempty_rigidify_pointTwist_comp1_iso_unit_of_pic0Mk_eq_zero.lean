-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/cb35713b-11f8-535d-9541-2c26dc99e947

import Mathlib
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_DRModelPackageLevelAPI
import Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Theorems.Thm_AlgebraicCurve_CurveModel_exists_representsRelSubPic_abelJacobi_of_isAlgClosed
import Theorems.Thm_AlgebraicGeometry_RelPicard_RepresentsRelSubPic_nonempty_pullbackAlong_mul_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_nonempty_module_tensor_invModule_iso
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_tensor_iso_mul_module
import Theorems.Thm_AlgebraicGeometry_Scheme_Hom_nonempty_pullback_ker_pow_invModule_iso_of_isIso
import Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_isInvertible_I
import Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
p2m_attr_erase "instance" "TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel"

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

universe u v

namespace PrincTriv

def ClsMon (X : Scheme.{u}) : Type (u + 1) := Quotient (isIsomorphicSetoid X.Modules)

variable {X Y : Scheme.{u}}

def cls (A : X.Modules) : ClsMon X := Quotient.mk _ A

theorem cls_eq_iff {A B : X.Modules} : cls A = cls B ↔ Nonempty (A ≅ B) :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

scoped instance : CommMonoid (ClsMon X) where
  mul := Quotient.map₂ (fun A B => A ⊗ B) (fun _ _ hA _ _ hB => ⟨hA.some ⊗ᵢ hB.some⟩)
  one := cls (𝟙_ X.Modules)
  mul_assoc a b c := Quotient.inductionOn₃ a b c fun _ _ _ => Quotient.sound ⟨α_ _ _ _⟩
  one_mul a := Quotient.inductionOn a fun _ => Quotient.sound ⟨λ_ _⟩
  mul_one a := Quotient.inductionOn a fun _ => Quotient.sound ⟨ρ_ _⟩
  mul_comm a b := Quotient.inductionOn₂ a b fun _ _ => Quotient.sound ⟨β_ _ _⟩

theorem cls_tensor (A B : X.Modules) : cls (A ⊗ B) = cls A * cls B := rfl

theorem cls_unit : cls (𝟙_ X.Modules) = 1 := rfl

def unitOf (A B : X.Modules) (h : Nonempty (A ⊗ B ≅ 𝟙_ X.Modules)) : (ClsMon X)ˣ where
  val := cls A
  inv := cls B
  val_inv := by rw [← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h
  inv_val := by rw [mul_comm, ← cls_tensor, ← cls_unit]; exact cls_eq_iff.mpr h

@[scoped simp] theorem val_unitOf (A B : X.Modules) (h) : (unitOf A B h : ClsMon X) = cls A := rfl
@[scoped simp] theorem inv_unitOf (A B : X.Modules) (h) : ((unitOf A B h)⁻¹ : (ClsMon X)ˣ) = (cls B : ClsMon X) := rfl

def pullbackCls (f : X ⟶ Y) : ClsMon Y →* ClsMon X where
  toFun := Quotient.map (fun A => (Scheme.Modules.pullback f).obj A) (fun _ _ h => ⟨(Scheme.Modules.pullback f).mapIso h.some⟩)
  map_one' := Quotient.sound ⟨Scheme.Modules.pullbackTensorUnitObjIso f⟩
  map_mul' a b := Quotient.inductionOn₂ a b fun A B => Quotient.sound ⟨Scheme.Modules.pullbackTensorObjIso f A B⟩

theorem pullbackCls_cls (f : X ⟶ Y) (A : Y.Modules) :
    pullbackCls f (cls A) = cls ((Scheme.Modules.pullback f).obj A) := rfl

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

namespace PrincTriv

variable {X Y : Scheme.{u}}

def idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) : (ClsMon X)ˣ :=
  unitOf I.module I.invModule hI.nonempty_module_tensor_invModule_iso.1

@[scoped simp] theorem val_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    (idealUnit I hI : ClsMon X) = cls I.module := rfl

@[scoped simp] theorem val_inv_idealUnit (I : X.IdealSheafData) (hI : I.IsInvertible) :
    ((idealUnit I hI)⁻¹ : (ClsMon X)ˣ) = (cls I.invModule : ClsMon X) := rfl

theorem idealUnit_congr {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible) (h : I = J) :
    idealUnit I hI = idealUnit J hJ := by subst h; rfl

theorem idealUnit_mul {I J : X.IdealSheafData} (hI : I.IsInvertible) (hJ : J.IsInvertible)
    (hIJ : (I * J).IsInvertible) : idealUnit (I * J) hIJ = idealUnit I hI * idealUnit J hJ := by
  ext
  show cls (I * J).module = cls I.module * cls J.module
  rw [← cls_tensor]
  obtain ⟨μ, -⟩ := hI.exists_tensor_iso_mul_module hJ
  exact (cls_eq_iff.mpr ⟨μ⟩).symm

theorem idealUnit_pow {I : X.IdealSheafData} (hI : I.IsInvertible) (k : ℕ) :
    idealUnit (I ^ k) (hI.pow k) = idealUnit I hI ^ k := by
  induction k with
  | zero =>
    have h00 : (I ^ 0 * I ^ 0).IsInvertible := by rw [← pow_add]; exact hI.pow 0
    have h2 : idealUnit (I ^ 0) (hI.pow 0) * idealUnit (I ^ 0) (hI.pow 0) = idealUnit (I ^ 0) (hI.pow 0) := by
      rw [← idealUnit_mul (hI.pow 0) (hI.pow 0) h00]
      exact idealUnit_congr _ _ (by rw [← pow_add])
    rw [show idealUnit I hI ^ 0 = 1 from pow_zero _]
    exact mul_left_cancel (h2.trans (mul_one _).symm)
  | succ k ih =>
    have h' : (I ^ k * I).IsInvertible := (pow_succ I k) ▸ hI.pow (k + 1)
    calc idealUnit (I ^ (k + 1)) (hI.pow (k + 1)) = idealUnit (I ^ k * I) h' := idealUnit_congr _ _ (pow_succ I k)
      _ = idealUnit (I ^ k) (hI.pow k) * idealUnit I hI := idealUnit_mul _ _ _
      _ = idealUnit I hI ^ (k + 1) := by rw [ih, pow_succ]

theorem cls_foldr {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (A B : Fin n → X.Modules) (l : List (Fin n)) :
    cls (l.foldr (fun i M => if c i = j then A i ⊗ B i ⊗ M else M) (𝟙_ X.Modules)) =
      (l.map fun i => if c i = j then cls (A i) * cls (B i) else 1).prod := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, List.map_cons, List.prod_cons]
    split_ifs with h
    · rw [cls_tensor, cls_tensor, ih, mul_assoc]
    · rw [ih, one_mul]

theorem cls_twist {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2) (I : Fin n → X.IdealSheafData)
    (hI : ∀ i, (I i).IsInvertible) (pos neg : Fin n → ℕ) :
    cls ((List.finRange n).foldr
        (fun i M => if c i = j then ((I i) ^ (pos i)).invModule ⊗ ((I i) ^ (neg i)).module ⊗ M else M)
        (𝟙_ X.Modules)) =
      ↑((∏ i ∈ Finset.univ.filter (fun i => c i = j), idealUnit (I i) (hI i) ^ ((pos i : ℤ) - (neg i : ℤ)))⁻¹) := by
  rw [cls_foldr c j (fun i => ((I i) ^ (pos i)).invModule) (fun i => ((I i) ^ (neg i)).module),
    ← Fin.prod_univ_def, ← Finset.prod_filter, ← Finset.prod_inv_distrib, Units.coe_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [show cls (((I i) ^ (pos i)).invModule) = ↑((idealUnit _ ((hI i).pow (pos i)))⁻¹) from rfl,
    show cls (((I i) ^ (neg i)).module) = ↑(idealUnit _ ((hI i).pow (neg i))) from rfl,
    idealUnit_pow, idealUnit_pow, ← Units.val_mul, ← zpow_neg, neg_sub, zpow_sub, zpow_natCast, zpow_natCast,
    mul_comm]

theorem prod_inv_mul_zpow {ι G : Type*} [CommGroup G] [DecidableEq ι] (s : Finset ι) (a : ι → G) (b : G) (m : ι → ℤ) :
    ∏ i ∈ s, ((a i)⁻¹ * b) ^ (m i) = (∏ i ∈ s, (a i) ^ (m i))⁻¹ * b ^ (∑ i ∈ s, m i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, Finset.sum_insert hi, ih, mul_zpow, inv_zpow, zpow_add, mul_inv]
    ac_rfl

theorem map_pullbackCls_idealUnit_ker {T : Scheme.{u}} (f : Y ⟶ X) [IsIso f] (p : T ⟶ X) [IsClosedImmersion p]
    (p' : T ⟶ Y) (hp : p' ≫ f = p) (hI : p.ker.IsInvertible) (hI' : p'.ker.IsInvertible) :
    Units.map (pullbackCls f : ClsMon X →* ClsMon Y) (idealUnit p.ker hI) = idealUnit p'.ker hI' := by
  ext
  show pullbackCls f (cls p.ker.module) = cls p'.ker.module
  have h := (Scheme.Hom.nonempty_pullback_ker_pow_invModule_iso_of_isIso f p p' hp hI hI' 1).2
  rw [pow_one, pow_one] at h
  rw [pullbackCls_cls]
  exact cls_eq_iff.mpr h

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

namespace PrincTriv

section Generic

variable {K : Type u} [Field K] [IsAlgClosed K] {F : Type v} [Field F] [Algebra K F] [IsCurveOver K F]

theorem jac_prod_eq_one (M : CurveModel K F) {ι : Type*} [DecidableEq ι] (S : Finset ι)
    (x : ι → (Spec (CommRingCat.of K) ⟶ M.C)) (hx : ∀ i, x i ≫ M.toBase = 𝟙 _)
    (s : Spec (CommRingCat.of K) ⟶ M.C) (hs : s ≫ M.toBase = 𝟙 _)
    (m : ι → ℤ)
    (D : ↥(Divisor.degZero (K := K) (F := F)))
    (hD : (D : Divisor K F) = ∑ i ∈ S, Finsupp.single (M.pointEquivPlace ⟨x i, hx i⟩) (m i))
    (h0 : Pic0.mk D = 0) :
    ∏ i ∈ S, idealUnit (RelEffCartierDiv.ofPoint M.toBase (x i) (hx i)).I
        (RelEffCartierDiv.isInvertible_I _) ^ (m i) = 1 := by

  have hsum : ∑ i ∈ S, m i = 0 := by
    have h := D.2
    rw [Divisor.mem_degZero, hD, map_sum] at h
    simpa only [Divisor.degree_single, IsCurveOver.deg_eq_one_of_isAlgClosed, Nat.cast_one, mul_one] using h

  obtain ⟨DJ, hJ, aj, -, -, -, -, hcl, pts, hadd, haj⟩ :=
    AlgebraicCurve.CurveModel.exists_representsRelSubPic_abelJacobi_of_isAlgClosed K F M ⟨s, hs⟩
  choose Dv hDv hpts using haj

  have hIx : ∀ (y : Spec (CommRingCat.of K) ⟶ M.C) (hy : y ≫ M.toBase = 𝟙 _),
      (RelEffCartierDiv.ofPoint M.toBase y hy).I.IsInvertible := fun y hy => RelEffCartierDiv.isInvertible_I _
  have hs1 : (𝟙 _ ≫ s) ≫ M.toBase = 𝟙 (Spec (CommRingCat.of K)) := by rw [Category.id_comp, hs]

  let Φf : Pic0 K F → ClsMon (pullback M.toBase (𝟙 (Spec (CommRingCat.of K)))) :=
    fun Q => cls (hJ.poincare.pullbackAlong (pts Q)).L
  have hmul : ∀ Q Q' : Pic0 K F, Φf (Q + Q') = Φf Q * Φf Q' := fun Q Q' => by
    show cls _ = cls _ * cls _
    rw [hadd, ← cls_tensor]
    exact cls_eq_iff.mpr (RepresentsRelSubPic.nonempty_pullbackAlong_mul_iso
      (P := algEquivZeroGroupCut M.toBase ⟨s, hs⟩) hJ (𝟙 _) (pts Q) (pts Q'))

  have hval : ∀ (y : Spec (CommRingCat.of K) ⟶ M.C) (hy : y ≫ M.toBase = 𝟙 _),
      Φf (Pic0.mk (Dv ⟨y, hy⟩)) = ↑((idealUnit _ (hIx y hy))⁻¹ * idealUnit _ (hIx (𝟙 _ ≫ s) hs1)) := by
    intro y hy
    have hq : pts (Pic0.mk (Dv ⟨y, hy⟩)) =
        ⟨y ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (y ≫ ·) aj.2).trans hy)⟩ := Subtype.ext (hpts ⟨y, hy⟩)
    show cls _ = _
    rw [hq, Units.val_mul, val_inv_idealUnit, val_idealUnit, ← cls_tensor]
    exact cls_eq_iff.mpr (hcl K (𝟙 _) ⟨y, hy⟩)

  have hone : Φf 0 = 1 := by
    have hz0 : Pic0.mk (Dv ⟨s, hs⟩) = 0 := by
      rw [← Pic0.mk_zero]
      congr 1
      apply Subtype.ext
      rw [hDv]
      exact sub_self _
    have h2 : Φf 0 * Φf 0 = Φf 0 := by rw [← hmul, add_zero]
    rw [← hz0, hval s hs, ← Units.val_mul, Units.val_inj] at h2
    rw [← hz0, hval s hs, mul_left_cancel (h2.trans (mul_one _).symm), Units.val_one]

  let Φ : Multiplicative (Pic0 K F) →* ClsMon (pullback M.toBase (𝟙 (Spec (CommRingCat.of K)))) :=
    { toFun := fun Q => Φf Q.toAdd, map_one' := hone, map_mul' := fun Q Q' => hmul Q.toAdd Q'.toAdd }
  have hΦ : ∀ i ∈ S, Φ.toHomUnits (Multiplicative.ofAdd (Pic0.mk (Dv ⟨x i, hx i⟩))) =
      (idealUnit _ (hIx (x i) (hx i)))⁻¹ * idealUnit _ (hIx (𝟙 _ ≫ s) hs1) := fun i _ => Units.ext (hval (x i) (hx i))

  have hDsum : D = ∑ i ∈ S, m i • Dv ⟨x i, hx i⟩ := by
    apply Subtype.ext
    have hterm : ∀ i, ((m i • Dv ⟨x i, hx i⟩ : ↥(Divisor.degZero (K := K) (F := F))) : Divisor K F) =
        Finsupp.single (M.pointEquivPlace ⟨x i, hx i⟩) (m i) - m i • Finsupp.single (M.pointEquivPlace ⟨s, hs⟩) 1 := by
      intro i
      rw [AddSubgroupClass.coe_zsmul, hDv, smul_sub, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hD, AddSubmonoidClass.coe_finsetSum, Finset.sum_congr rfl fun i _ => hterm i, Finset.sum_sub_distrib,
      ← Finset.sum_smul, hsum, zero_smul, sub_zero]
  have hmk : Pic0.mk D = ∑ i ∈ S, m i • Pic0.mk (Dv ⟨x i, hx i⟩) := by
    change (QuotientAddGroup.mk' _) D = ∑ i ∈ S, m i • (QuotientAddGroup.mk' _) (Dv ⟨x i, hx i⟩)
    rw [hDsum, map_sum]
    exact Finset.sum_congr rfl fun i _ => map_zsmul _ _ _
  have key : Φ.toHomUnits (Multiplicative.ofAdd (Pic0.mk D)) = 1 := by rw [h0, ofAdd_zero, map_one]
  rw [hmk, ofAdd_sum, map_prod] at key
  simp_rw [ofAdd_zsmul, map_zpow] at key
  rw [Finset.prod_congr rfl fun i hi => by rw [hΦ i hi], prod_inv_mul_zpow, hsum, zpow_zero, mul_one,
    inv_eq_one] at key
  exact key

theorem cls_pointTwist_eq_one (M : CurveModel K F) {X' : Scheme.{u}} (f0 : X' ⟶ Spec (CommRingCat.of K))
    [IsSeparated f0] [SmoothOfRelativeDimension 1 f0]
    (e : M.C ⟶ X') [IsIso e] (he : e ≫ f0 = M.toBase)
    {n : ℕ} (c : Fin n → Fin 2) (j : Fin 2)
    (z : Fin n → (Spec (CommRingCat.of K) ⟶ X')) (hz : ∀ i, z i ≫ f0 = 𝟙 _)
    (w : Fin n → Place K F)
    (hw : ∀ i, ∃ h : (inv e).base ((z i).base (IsLocalRing.closedPoint K)) ∈ closedPoints M.C, M.placeOfPoint ⟨_, h⟩ = w i)
    (pos neg : Fin n → ℕ)
    (Dz : ↥(Divisor.degZero (K := K) (F := F)))
    (hDz : (Dz : Divisor K F) = ∑ i ∈ Finset.univ.filter (fun i => c i = j), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)))
    (h0 : Pic0.mk Dz = 0) :
    cls ((List.finRange n).foldr
        (fun i N => if c i = j then
          ((RelEffCartierDiv.ofPoint f0 (z i) (hz i)).I ^ (pos i)).invModule ⊗
            ((RelEffCartierDiv.ofPoint f0 (z i) (hz i)).I ^ (neg i)).module ⊗ N
          else N)
        (𝟙_ _)) = 1 := by
  have hI0 : ∀ i, (RelEffCartierDiv.ofPoint f0 (z i) (hz i)).I.IsInvertible := fun i => RelEffCartierDiv.isInvertible_I _
  rw [cls_twist c j (fun i => (RelEffCartierDiv.ofPoint f0 (z i) (hz i)).I) hI0 pos neg]
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · rw [Finset.univ_eq_empty, Finset.filter_empty, Finset.prod_empty, inv_one, Units.val_one]
  obtain ⟨i₀⟩ := hn
  have he' : inv e ≫ M.toBase = f0 := by rw [← he, IsIso.inv_hom_id_assoc]
  have hz' : ∀ i, (z i ≫ inv e) ≫ M.toBase = 𝟙 _ := fun i => by rw [Category.assoc, he', hz]

  obtain ⟨φ, hφ⟩ : ∃ φ : pullback M.toBase (𝟙 (Spec (CommRingCat.of K))) ⟶ pullback f0 (𝟙 (Spec (CommRingCat.of K))),
      φ = pullback.map M.toBase (𝟙 _) f0 (𝟙 _) e (𝟙 _) (𝟙 _) (by rw [Category.comp_id, he]) (by simp) := ⟨_, rfl⟩
  haveI : IsIso φ := by rw [hφ]; infer_instance
  have hgr : ∀ i, graphOver M.toBase (z i ≫ inv e) (hz' i) ≫ φ = graphOver f0 (z i) (hz i) := by
    intro i
    apply pullback.hom_ext
    · rw [Category.assoc, hφ, pullback.lift_fst, graphOver_fst_assoc, Category.assoc, IsIso.inv_hom_id,
        Category.comp_id, graphOver_fst]
    · rw [Category.assoc, hφ, pullback.lift_snd, graphOver_snd_assoc, graphOver_snd]
  have hIM : ∀ i, (RelEffCartierDiv.ofPoint M.toBase (z i ≫ inv e) (hz' i)).I.IsInvertible :=
    fun i => RelEffCartierDiv.isInvertible_I _
  have htr : ∀ i, Units.map (pullbackCls (inv φ) : ClsMon _ →* ClsMon _) (idealUnit _ (hIM i)) = idealUnit _ (hI0 i) :=
    fun i => map_pullbackCls_idealUnit_ker (inv φ) (graphOver M.toBase (z i ≫ inv e) (hz' i)) (graphOver f0 (z i) (hz i))
      (by rw [← hgr i, Category.assoc, IsIso.hom_inv_id, Category.comp_id]) (hIM i) (hI0 i)

  have hpl : ∀ i, M.pointEquivPlace ⟨z i ≫ inv e, hz' i⟩ = w i := fun i => by
    obtain ⟨hmem, hwi⟩ := hw i
    rw [CurveModel.pointEquivPlace_apply, ← hwi]
    congr 1

  have hjac := jac_prod_eq_one M (Finset.univ.filter (fun i => c i = j)) (fun i => z i ≫ inv e) hz'
    (z i₀ ≫ inv e) (hz' i₀) (fun i => (pos i : ℤ) - (neg i : ℤ)) Dz (by simp_rw [hpl]; exact hDz) h0
  have hprod : ∏ i ∈ Finset.univ.filter (fun i => c i = j), idealUnit _ (hI0 i) ^ ((pos i : ℤ) - (neg i : ℤ)) =
      Units.map (pullbackCls (inv φ) : ClsMon _ →* ClsMon _)
        (∏ i ∈ Finset.univ.filter (fun i => c i = j), idealUnit _ (hIM i) ^ ((pos i : ℤ) - (neg i : ℤ))) := by
    rw [map_prod]
    simp_rw [map_zpow, htr]
  rw [hprod, hjac, map_one, inv_one, Units.val_one]

end Generic
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

namespace PrincTriv

def rigidifyUnitIso {T P' : Scheme.{u}} (σ : T ⟶ P') (q : P' ⟶ T) :
    Scheme.Modules.rigidify σ q (𝟙_ P'.Modules) ≅ 𝟙_ P'.Modules :=
  (Iso.refl (𝟙_ P'.Modules) ⊗ᵢ ((Scheme.Modules.pullback q).mapIso
      (Scheme.Modules.dualMapIso (Scheme.Modules.pullbackTensorUnitObjIso σ) ≪≫
        (MonoidalClosed.unitNatIso (C := T.Modules)).symm.app (𝟙_ T.Modules)) ≪≫
    Scheme.Modules.pullbackTensorUnitObjIso q)) ≪≫ λ_ (𝟙_ P'.Modules)

end PrincTriv
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    ∀ [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
      {n : ℕ} (c : Fin n → Fin 2)

      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))))
      (hz : ∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _)
      (w : Fin n → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀))
      (_ : ∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base ((z i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ = w i)
      (pos neg : Fin n → ℕ)
      (Dz : ↥(Divisor.degZero (K := (ResidueField ↥A)) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀))))
      (_ : (Dz : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)))
      (_ : Pic0.mk Dz = 0),
      Nonempty ((Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
          (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) ((List.finRange n).foldr
          (fun i M => if c i = 1 then
            ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
              ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
            else M)
          (𝟙_ _))) ≅
        (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by
  intro _instP ε₀ n c z hz w hw pos neg Dz hDz h0
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  haveI : IsIso (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))) := 𝔓.efib_iso _ _
  haveI : SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) :=
    𝔓.smoothOfRelativeDimension_one_fibre0 (algebraMap (R p) (ResidueField ↥A))
  haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N₀
  obtain ⟨e1⟩ := PrincTriv.cls_eq_iff.mp (PrincTriv.cls_pointTwist_eq_one
    (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))
    (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
    (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))
    (𝔓.hefib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))
    c 1 z hz w hw pos neg Dz hDz h0)
  exact ⟨Scheme.Modules.rigidifyMapIso _ _ e1 ≪≫ PrincTriv.rigidifyUnitIso _ _⟩

end
p2m_reactivate "P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero.PrincTriv"

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero (solution)
