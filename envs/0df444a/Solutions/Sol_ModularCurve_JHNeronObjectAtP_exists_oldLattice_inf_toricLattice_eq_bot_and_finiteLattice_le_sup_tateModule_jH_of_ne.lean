-- Prove2me | solution 1 for ModularCurve.JHNeronObjectAtP.exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/02a63e43-a4e3-53d2-8006-b012aa5e5586

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_AlgebraicCurve_GluedPic0Functoriality
import Definitions.Def_AlgebraicCurve_GluedPic0SliceOps
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_ModularCurve_CharacterLatticePairings
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModularCurve_exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne
import Theorems.Thm_ModularCurve_JHNeronObjectAtP_LevelData_exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions GoodReductionJacobian.RelativeGroupLaw.isIso_endKerStr_schemeHomOverId AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap AlgebraicGeometry.SquareZero.isLocalRing' AlgebraicGeometry.SquareZero.isLocalRing instTopologicallyFGOfFiniteType AlgebraicGeometry.ProjSpace.twistObj.addCommGroup AlgebraicGeometry.ProjSpace.twistFam.module AlgebraicGeometry.ProjSpace.twistObj.module AlgebraicGeometry.ProjSpace.twistObj.moduleSections AlgebraicGeometry.ProjSpace.twistFam.addCommGroup kmfloorsGlue_int_three_isPrime kmfloorsGlue_int_bot_isPrime ValuationSubring.instIsAlgClosedResidueField AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring NeronModelInfra.schemeHomOverNpow_succ NeronModelInfra.schemeHomOverNpow_zero AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart"
p2m_attr_erase "simp" "AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec"
p2m_attr_erase "simp" "TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply AlgebraicGeometry.TangentPoints.map_coe AlgebraicGeometry.SquareZero.basePoint_toBase_assoc AlgebraicGeometry.SquareZero.basePoint_toBase AlgebraicGeometry.SquareZero.basePoint_specMap AlgebraicGeometry.SquareZero.basePointOver_coe AlgebraicGeometry.SquareZero.specMap_toBase_assoc AlgebraicGeometry.SquareZero.specMapOver_coe AlgebraicGeometry.RelPicard.TrivialModDeformations.map_coe AlgebraicGeometry.SquareZero.specMap_toBase AlgebraicGeometry.SquareZero.basePoint_specMap_assoc AlgebraicGeometry.Scheme.relFrobenius_snd AlgebraicGeometry.Scheme.frobenius_preimage AlgebraicGeometry.Scheme.relFrobenius_fst AlgebraicGeometry.Scheme.relFrobenius_snd_assoc AlgebraicGeometry.Scheme.relFrobenius_fst_assoc AlgebraicGeometry.powCharRingHom_apply AlgebraicGeometry.Scheme.frobenius_base AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicGeometry.ProjSpace.twistObj.mk.injEq AlgebraicGeometry.ProjSpace.twistObj.zero_val AlgebraicGeometry.ProjSpace.twistObj.add_val"
p2m_attr_erase "simp" "AlgebraicGeometry.ProjSpace.twist_res_val AlgebraicGeometry.ProjSpace.twist_smul_val AlgebraicGeometry.ProjSpace.twistGradeToObj_val AlgebraicGeometry.ProjSpace.twistObj.smul_val AlgebraicGeometry.ProjSpace.twistGradeEquiv_apply_val AlgebraicGeometry.ProjSpace.twistObj.mk.sizeOf_spec AlgebraicGeometry.schemeFibreEndo_snd AlgebraicGeometry.schemeFibreEndo_fst AlgebraicCurve.KwCfx.kw_cfx_tau_coe AlgebraicCurve.kw_hwcd_dlog_zero AlgebraicCurve.kw_hwcd_mem_regularDifferentials_iff AlgebraicCurve.kw_hwcd_dlog_one AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ValuationSubring.coe_toResidueValuationSubring AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec CohCarrier.frickeH1L_apply CohCarrier.frickeMat_apply_10 CohCarrier.frickeEquiv_symm_apply"
p2m_attr_erase "simp" "CohCarrier.frickeMat_apply_01 CohCarrier.coe_frickeHom CohCarrier.frickeMat_apply_00 CohCarrier.frickeMat_apply_11 CohCarrier.frickeEquiv_apply CohCarrier.frickeH1_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

namespace QPARNBEngine

open TateModule

section Functoriality

variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]

noncomputable def tmap (f : M →+ N) : TateModule p M →ₗ[ℤ_[p]] TateModule p N where
  toFun x := ⟨fun n => f ((x : ℕ → M) n), fun n =>
    ⟨by rw [← map_zsmul, TateModule.torsion, map_zero], by rw [← map_zsmul, TateModule.compat]⟩⟩
  map_add' x y := Subtype.ext (funext fun n => by
    change f (((x + y : TateModule p M) : ℕ → M) n) = f ((x : ℕ → M) n) + f ((y : ℕ → M) n)
    rw [TateModule.coe_add, Pi.add_apply, map_add])
  map_smul' a x := Subtype.ext (funext fun n => by
    change f (((a • x : TateModule p M) : ℕ → M) n) = (((a • ⟨fun n => f ((x : ℕ → M) n), _⟩ : TateModule p N)) : ℕ → N) n
    rw [TateModule.smul_apply, TateModule.smul_apply, map_zsmul])

@[scoped simp]
theorem tmap_apply_coe (f : M →+ N) (x : TateModule p M) (n : ℕ) :
    ((tmap f x : TateModule p N) : ℕ → N) n = f ((x : ℕ → M) n) := rfl

theorem proj_tmap (f : M →+ N) (x : TateModule p M) (n : ℕ) :
    TateModule.proj p N n (tmap f x) = f (TateModule.proj p M n x) := rfl

end Functoriality

section OldRange

variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]

noncomputable def oldParam (α : Fin 2 → (M →+ N)) : (TateModule p M × TateModule p M) →ₗ[ℤ_[p]] TateModule p N :=
  (tmap (α 0)).coprod (tmap (α 1))

noncomputable def oldRange (α : Fin 2 → (M →+ N)) : Submodule ℤ_[p] (TateModule p N) :=
  LinearMap.range (oldParam (p := p) α)

theorem oldParam_apply (α : Fin 2 → (M →+ N)) (w : TateModule p M × TateModule p M) :
    oldParam (p := p) α w = tmap (α 0) w.1 + tmap (α 1) w.2 := by
  rw [oldParam, LinearMap.coprod_apply]

theorem mem_oldRange_iff (α : Fin 2 → (M →+ N)) (x : TateModule p N) :
    x ∈ oldRange (p := p) α ↔
      ∃ w₀ w₁ : TateModule p M, ∀ n : ℕ,
        TateModule.proj p N n x =
          α 0 (TateModule.proj p M n w₀) + α 1 (TateModule.proj p M n w₁) := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨w.1, w.2, fun n => ?_⟩
    rw [oldParam_apply]
    rfl
  · rintro ⟨w₀, w₁, h⟩
    refine ⟨(w₀, w₁), Subtype.ext (funext fun n => ?_)⟩
    rw [oldParam_apply]
    exact (h n).symm

end OldRange

section BoundedKernel

variable {p : ℕ} [Fact p.Prime] {M N : Type} [AddCommGroup M] [AddCommGroup N]

theorem pow_factorization_smul_eq_zero {c : ℕ} (hc : c ≠ 0) (y : M) (m : ℕ) (hm : ((p ^ m : ℕ) : ℤ) • y = 0)
    (hcy : (c : ℤ) • y = 0) : ((p ^ c.factorization p : ℕ) : ℤ) • y = 0 := by
  have hp : p.Prime := Fact.out
  rw [natCast_zsmul] at hm hcy ⊢
  have h1 : addOrderOf y ∣ p ^ m := addOrderOf_dvd_iff_nsmul_eq_zero.2 hm
  have h2 : addOrderOf y ∣ c := addOrderOf_dvd_iff_nsmul_eq_zero.2 hcy
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 h1
  rw [hj] at h2
  have hjle : j ≤ c.factorization p := (hp.pow_dvd_iff_le_factorization hc).1 h2
  refine addOrderOf_dvd_iff_nsmul_eq_zero.1 ?_
  rw [hj]
  exact pow_dvd_pow p hjle

theorem tmap_injective_of_bounded_kernel (f : M →+ N) (c : ℕ) (hc : 0 < c)
    (hker : ∀ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 → f x = 0 → (c : ℤ) • x = 0) :
    Function.Injective (tmap (p := p) f) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  set v := c.factorization p
  refine Subtype.ext (funext fun n => ?_)
  have hlev : ∀ m, f ((x : ℕ → M) m) = 0 := fun m => by
    have := congrArg (fun y : TateModule p N => (y : ℕ → N) m) hx
    simpa only [tmap_apply_coe, TateModule.coe_zero, Pi.zero_apply] using this
  have hkill : ((p ^ v : ℕ) : ℤ) • (x : ℕ → M) (n + v) = 0 :=
    pow_factorization_smul_eq_zero hc.ne' _ (n + v) (TateModule.torsion x (n + v)) (hker _ _ (TateModule.torsion x _) (hlev _))
  rw [TateModule.coe_zero, Pi.zero_apply, ← TateModule.compat_pow x n v, hkill]

theorem exists_pow_smul_mem_range_tmap (f : M →+ N) (c : ℕ) (hc : 0 < c)
    (hker : ∀ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 → f x = 0 → (c : ℤ) • x = 0)
    (hsurj : ∀ (n : ℕ) (y : N), ((p ^ n : ℕ) : ℤ) • y = 0 → ∃ (m : ℕ) (x : M), ((p ^ m : ℕ) : ℤ) • x = 0 ∧ f x = y) :
    ∃ k : ℕ, ∀ Y : TateModule p N, ∃ X : TateModule p M, tmap f X = (((p : ℕ) : ℤ_[p]) ^ k) • Y := by
  set v := c.factorization p with hv
  refine ⟨v, fun Y => ?_⟩

  have hpre : ∀ n, ∃ x : M, (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • x = 0) ∧ f x = (Y : ℕ → N) n := fun n => by
    obtain ⟨m, x, hxm, hfx⟩ := hsurj n _ (TateModule.torsion Y n)
    exact ⟨x, ⟨m, hxm⟩, hfx⟩
  choose x hxtor hfx using hpre

  have htor_zsmul : ∀ (a : ℤ) (y : M), (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • y = 0) → ∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • (a • y) = 0 :=
    fun a y ⟨m, hm⟩ => ⟨m, by rw [smul_comm, hm, smul_zero]⟩
  have htor_sub : ∀ y z : M, (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • y = 0) → (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • z = 0) →
      ∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • (y - z) = 0 := fun y z ⟨m, hm⟩ ⟨m', hm'⟩ =>
    ⟨m + m', by
      rw [smul_sub, pow_add, Nat.cast_mul, mul_comm, mul_smul, hm, smul_zero, mul_comm, mul_smul, hm', smul_zero, sub_zero]⟩

  have hkill : ∀ y : M, (∃ m : ℕ, ((p ^ m : ℕ) : ℤ) • y = 0) → f y = 0 → ((p ^ v : ℕ) : ℤ) • y = 0 :=
    fun y ⟨m, hm⟩ hfy => pow_factorization_smul_eq_zero hc.ne' y m hm (hker m y hm hfy)

  have hXtors : ∀ n, ((p ^ n : ℕ) : ℤ) • (((p ^ v : ℕ) : ℤ) • x n) = 0 := fun n => by
    rw [smul_comm]
    refine hkill _ (htor_zsmul _ _ (hxtor n)) ?_
    rw [map_zsmul, hfx, TateModule.torsion]
  have hXcompat : ∀ n, ((p : ℕ) : ℤ) • (((p ^ v : ℕ) : ℤ) • x (n + 1)) = ((p ^ v : ℕ) : ℤ) • x n := fun n => by
    rw [smul_comm, ← sub_eq_zero, ← smul_sub]
    refine hkill _ (htor_sub _ _ (htor_zsmul _ _ (hxtor _)) (hxtor _)) ?_
    rw [map_sub, map_zsmul, hfx, hfx, TateModule.compat, sub_self]
  refine ⟨⟨fun n => ((p ^ v : ℕ) : ℤ) • x n, fun n => ⟨hXtors n, hXcompat n⟩⟩, Subtype.ext (funext fun n => ?_)⟩
  rw [tmap_apply_coe, ← Nat.cast_pow, TateModule.natCast_padicInt_smul_apply]
  change f (((p ^ v : ℕ) : ℤ) • x n) = ((p ^ v : ℕ) : ℤ) • (Y : ℕ → N) n
  rw [map_zsmul, hfx]

end BoundedKernel

section Assembly

variable {R : Type} [CommRing R] {V W Q : Type} [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup Q] [Module R Q]

theorem inf_eq_bot_and_smul_mem_sup (Tt Tf : Submodule R V) (μ : W →ₗ[R] V) (hμ : ∀ w, μ w ∈ Tf)
    (red : ↥Tf →ₗ[R] Q) (hker : ∀ x : ↥Tf, red x = 0 ↔ (x : V) ∈ Tt)
    (ψ : W →ₗ[R] Q) (hcomm : ∀ w, red ⟨μ w, hμ w⟩ = ψ w) (hψinj : Function.Injective ψ)
    (r : R) (hψcok : ∀ q : Q, ∃ w : W, ψ w = r • q) :
    LinearMap.range μ ⊓ Tt = ⊥ ∧ ∀ x ∈ Tf, r • x ∈ LinearMap.range μ ⊔ Tt := by
  constructor
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨⟨w, rfl⟩, hxt⟩ := hx
    have h0 : red ⟨μ w, hμ w⟩ = 0 := (hker _).2 hxt
    rw [hcomm] at h0
    have hw : w = 0 := hψinj (by rw [h0, map_zero])
    rw [hw, map_zero]
  · intro x hx
    obtain ⟨w, hw⟩ := hψcok (red ⟨x, hx⟩)
    have hdiff : red (r • ⟨x, hx⟩ - ⟨μ w, hμ w⟩) = 0 := by
      rw [map_sub, map_smul, hcomm, hw, sub_self]
    have hmem : ((r • (⟨x, hx⟩ : ↥Tf) - ⟨μ w, hμ w⟩ : ↥Tf) : V) ∈ Tt := (hker _).1 hdiff
    have hcoe : ((r • (⟨x, hx⟩ : ↥Tf) - ⟨μ w, hμ w⟩ : ↥Tf) : V) = r • x - μ w := rfl
    rw [hcoe] at hmem
    have : r • x = μ w + (r • x - μ w) := by abel
    rw [this]
    exact Submodule.add_mem_sup ⟨w, rfl⟩ hmem

end Assembly

section TateAssembly

variable {p : ℕ} [Fact p.Prime] {M N P : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]

theorem exists_oldRange_clauses (α : Fin 2 → (M →+ N)) (Tt Tf : Submodule ℤ_[p] (TateModule p N))
    (hold : ∀ w : TateModule p M × TateModule p M, oldParam (p := p) α w ∈ Tf)
    (red : ↥Tf →ₗ[ℤ_[p]] TateModule p (P × P))
    (hker : ∀ x : ↥Tf, red x = 0 ↔ (x : TateModule p N) ∈ Tt)
    (sp : TateModule p M ≃ₗ[ℤ_[p]] TateModule p P)
    (prodIso : (TateModule p P × TateModule p P) ≃ₗ[ℤ_[p]] TateModule p (P × P))
    (Rmap : P × P →+ P × P)
    (hcomm : ∀ w : TateModule p M × TateModule p M,
      red ⟨oldParam (p := p) α w, hold w⟩ = tmap Rmap (prodIso (sp w.1, sp w.2)))
    (c : ℕ) (hc : 0 < c)
    (hRker : ∀ (m : ℕ) (z : P × P), ((p ^ m : ℕ) : ℤ) • z = 0 → Rmap z = 0 → (c : ℤ) • z = 0)
    (hRsurj : ∀ (n : ℕ) (z : P × P), ((p ^ n : ℕ) : ℤ) • z = 0 → ∃ (m : ℕ) (y : P × P), ((p ^ m : ℕ) : ℤ) • y = 0 ∧ Rmap y = z) :
    ∃ Told : Submodule ℤ_[p] (TateModule p N),
      (∀ x : TateModule p N, x ∈ Told ↔
        ∃ w₀ w₁ : TateModule p M, ∀ n : ℕ,
          TateModule.proj p N n x = α 0 (TateModule.proj p M n w₀) + α 1 (TateModule.proj p M n w₁)) ∧
      Told ≤ Tf ∧ Told ⊓ Tt = ⊥ ∧
      ∃ k : ℕ, ∀ x ∈ Tf, ((((p : ℕ) : ℤ_[p])) ^ k) • x ∈ Told ⊔ Tt := by

  let spsp : (TateModule p M × TateModule p M) →ₗ[ℤ_[p]] (TateModule p P × TateModule p P) :=
    (sp : TateModule p M →ₗ[ℤ_[p]] TateModule p P).prodMap (sp : TateModule p M →ₗ[ℤ_[p]] TateModule p P)
  let ψ : (TateModule p M × TateModule p M) →ₗ[ℤ_[p]] TateModule p (P × P) :=
    (tmap Rmap).comp ((prodIso : (TateModule p P × TateModule p P) →ₗ[ℤ_[p]] TateModule p (P × P)).comp spsp)
  have hψ : ∀ w, ψ w = tmap Rmap (prodIso (sp w.1, sp w.2)) := fun w => rfl
  have hRinj := tmap_injective_of_bounded_kernel (p := p) Rmap c hc hRker
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_range_tmap (p := p) Rmap c hc hRker hRsurj
  have hspsp_bij : Function.Bijective spsp := by
    refine ⟨fun a b h => ?_, fun y => ⟨(sp.symm y.1, sp.symm y.2), ?_⟩⟩
    · have h1 := congrArg Prod.fst h
      have h2 := congrArg Prod.snd h
      exact Prod.ext (sp.injective h1) (sp.injective h2)
    · exact Prod.ext (sp.apply_symm_apply y.1) (sp.apply_symm_apply y.2)
  have hψinj : Function.Injective ψ := hRinj.comp (prodIso.injective.comp hspsp_bij.1)
  have hψcok : ∀ q, ∃ w, ψ w = (((p : ℕ) : ℤ_[p]) ^ k) • q := fun q => by
    obtain ⟨X, hX⟩ := hk q
    obtain ⟨y, hy⟩ := prodIso.surjective X
    obtain ⟨w, hw⟩ := hspsp_bij.2 y
    refine ⟨w, ?_⟩
    change tmap Rmap (prodIso (spsp w)) = _
    rw [hw, hy, hX]
  obtain ⟨hB1, hCUT⟩ := inf_eq_bot_and_smul_mem_sup Tt Tf (oldParam (p := p) α) hold red hker ψ
    (fun w => (hcomm w).trans (hψ w).symm) hψinj ((((p : ℕ) : ℤ_[p])) ^ k) hψcok
  refine ⟨oldRange (p := p) α, mem_oldRange_iff α, ?_, hB1, k, hCUT⟩
  rintro _ ⟨w, rfl⟩
  exact hold w

end TateAssembly

end QPARNBEngine
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine"

section Geometry

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve ModularCurve.XHDRLevel ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

open scoped MatrixGroups

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP diamondActionModL infSubgroup xHFunctionFieldBar JH qExpFunctionFieldC qExpand qExpFrobeniusPushforwardModL jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData toricPts finPts ptsSp ssFinset pts surjective g pts_add G ptsSp_add L LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne"
namespace QPARNBGeom
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

theorem ofFibrePt_baseChange_mul_toFibrePt {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}
    {ι : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R)} {f : X ⟶ Spec (CommRingCat.of R)}
    (L : RelativeGroupLaw R f) (x y : SchemeHomOver ι f) :
    ofFibrePt ((L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y)) = L.mul ι x y := by
  apply Subtype.ext
  change (RelativeGroupLaw.baseChangePointToBase ι ((L.baseChange ι).mul (𝟙 _) (toFibrePt x) (toFibrePt y))).1 = _
  rw [RelativeGroupLaw.baseChangePointToBase_mul]
  have hx : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt x) = schemeHomOverComp (𝟙 _) rfl x := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  have hy : RelativeGroupLaw.baseChangePointToBase ι (toFibrePt y) = schemeHomOverComp (𝟙 _) rfl y := by
    rw [toFibrePt, RelativeGroupLaw.baseChangePointToBase_ofBase]
    exact Subtype.ext (Category.id_comp _).symm
  rw [hx, hy, ← L.mul_natural ι (𝟙 _ ≫ ι) (𝟙 _) rfl x y, GoodReductionJacobian.schemeHomOverComp_coe, Category.id_comp]

variable {p M : ℕ} [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)}

theorem extendsToPlace_of_abelianSchemePropertyBundle (Λ : LevelData p M H hpM A)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (x : SchemeHomOver (genPt p) Λ.f) : ExtendsToPlace A Λ.σA x := by
  have hprop : IsProper Λ.f := hΛ.proper
  have hvc : ValuativeCriterion Λ.f := by
    have h := congrFun (congrFun (congrFun AlgebraicGeometry.IsProper.eq_valuativeCriterion _) _) Λ.f
    rw [h] at hprop
    exact hprop.1.1.1
  let S : ValuativeCommSq Λ.f :=
    { R := ↥A, K := AlgebraicClosure ℚ, i₁ := x.1, i₂ := Λ.σA,
      commSq := ⟨by rw [x.2, ← Λ.hσA]; rfl⟩ }
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (hvc.existence S).exists_lift
  exact ⟨⟨l, hl₂⟩, hl₁.symm⟩

variable [Fact p.Prime] {hA : A.LiesOverPrime p} [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : LevelData p M H hpM A}

theorem apply_mem_finPts_of_zsmul_eq_zero (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (i : Fin 2) (m : ℕ) (w : JH (M / p) (infSubgroup p M H hpM)) (hw : ((m : ℕ) : ℤ) • w = 0) :
    αpull i w ∈ O.finPts m := by
  refine AddSubgroup.subset_closure ⟨AlgebraicCurve.Pic0.mem_torsion.2 (by rw [← map_zsmul, hw, map_zero]), ?_⟩
  obtain ⟨s, hs⟩ := extendsToPlace_of_abelianSchemePropertyBundle Λ hΛ (Λ.pts w)
  refine ⟨schemeHomOverComp s (degPull i), ?_⟩
  rw [hpull, hs, NeronModelInfra.schemeHomOverComp_coe, Category.assoc]

theorem schemeHomOverComp_resPt_mul (O : JHNeronObjectAtP p M H hpM A hA Λ) (s₀ s₁ : SchemeHomOver Λ.σA O.g) :
    NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) (O.L.mul Λ.σA s₀ s₁) =
      O.L.mul (resPt A ≫ Λ.σA) (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s₀)
        (NeronModelInfra.schemeHomOverComp ⟨resPt A, rfl⟩ s₁) := by
  have h := O.L.mul_natural Λ.σA (resPt A ≫ Λ.σA) (resPt A) rfl s₀ s₁
  have e : ∀ s : SchemeHomOver Λ.σA O.g, NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) s =
      GoodReductionJacobian.schemeHomOverComp (resPt A) rfl s := fun s => Subtype.ext rfl
  rw [e, e, e, h]

theorem schemeHomOverComp_barPt_mul (O : JHNeronObjectAtP p M H hpM A hA Λ) (s₀ s₁ : SchemeHomOver Λ.σA O.g) :
    GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (O.L.mul Λ.σA s₀ s₁) =
      O.L.mul (genPt p) (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s₀)
        (GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA s₁) :=
  O.L.mul_natural Λ.σA (genPt p) (barPt A) Λ.hσA s₀ s₁

theorem ptsSp_symm_mul (O : JHNeronObjectAtP p M H hpM A hA Λ) (u v : SchemeHomOver (resPt A ≫ Λ.σA) O.g) :
    O.ptsSp.symm (O.L.mul (resPt A ≫ Λ.σA) u v) = O.ptsSp.symm u + O.ptsSp.symm v := by
  apply O.ptsSp.injective
  rw [Equiv.apply_symm_apply, O.ptsSp_add, Equiv.apply_symm_apply, Equiv.apply_symm_apply,
    ofFibrePt_baseChange_mul_toFibrePt]

end ModularCurve.JHNeronObjectAtP.QPARNBGeom
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine"

namespace ModularCurve
p2m_export "ModularCurve" "XHDRLevel.ΓN XHDRModelAtP diamondActionModL infSubgroup xHFunctionFieldBar JH qExpFunctionFieldC qExpand qExpFrobeniusPushforwardModL jqModC JHNeronObjectAtP.LevelData JHNeronObjectAtP JZeroNeronObjectAtP exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne"
namespace JHNeronObjectAtP
p2m_export "ModularCurve.JHNeronObjectAtP" "ΓN Fbar LevelData toricPts finPts ptsSp ssFinset pts surjective g pts_add G ptsSp_add L LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne"
namespace QPARNBReduce
p2m_open "ModularCurve.JHNeronObjectAtP ModularCurve"

open TateModule QPARNBEngine

noncomputable def prodIso (p : ℕ) [Fact p.Prime] (P : Type) [AddCommGroup P] :
    (TateModule p P × TateModule p P) ≃ₗ[ℤ_[p]] TateModule p (P × P) where
  toFun z := ⟨fun n => (((z.1 : TateModule p P) : ℕ → P) n, ((z.2 : TateModule p P) : ℕ → P) n), fun n =>
    ⟨Prod.ext (by simpa using TateModule.torsion z.1 n) (by simpa using TateModule.torsion z.2 n),
     Prod.ext (by simpa using TateModule.compat z.1 n) (by simpa using TateModule.compat z.2 n)⟩⟩
  invFun x := (tmap (AddMonoidHom.fst P P) x, tmap (AddMonoidHom.snd P P) x)
  map_add' z z' := Subtype.ext (funext fun n => rfl)
  map_smul' a z := Subtype.ext (funext fun n => by
    refine Prod.ext ?_ ?_
    · change (((a • z.1 : TateModule p P)) : ℕ → P) n = _
      rw [TateModule.smul_apply, RingHom.id_apply, TateModule.smul_apply]; rfl
    · change (((a • z.2 : TateModule p P)) : ℕ → P) n = _
      rw [TateModule.smul_apply, RingHom.id_apply, TateModule.smul_apply]; rfl)
  left_inv z := Prod.ext (Subtype.ext (funext fun n => rfl)) (Subtype.ext (funext fun n => rfl))
  right_inv x := Subtype.ext (funext fun n => rfl)

@[scoped simp] theorem prodIso_apply_coe (p : ℕ) [Fact p.Prime] (P : Type) [AddCommGroup P]
    (z : TateModule p P × TateModule p P) (n : ℕ) :
    ((prodIso p P z : TateModule p (P × P)) : ℕ → P × P) n = (((z.1 : TateModule p P) : ℕ → P) n, ((z.2 : TateModule p P) : ℕ → P) n) := rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem of_geometricInputs
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

    (Tt Tf : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))
    (hTf : ∀ x : TateModule ℓ (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.finPts (ℓ ^ n))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

    (red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hred_pin : ∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
      TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s)))
    (hred_ker : ∀ x : ↥Tf, red x = 0 ↔ (x : TateModule ℓ (JH M H)) ∈ Tt)

    (hOldFin : ∀ (i : Fin 2) (n : ℕ) (w : JH (M / p) (infSubgroup p M H hpM)),
      ((ℓ ^ n : ℕ) : ℤ) • w = 0 → αpull i w ∈ O.finPts (ℓ ^ n))

    (sp : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) ≃ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))

    (hcompat : ∀ (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) × TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)))
        (hw : QPARNBEngine.oldParam (p := ℓ) αpull w ∈ Tf) (n : ℕ),
      TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n
          (red ⟨QPARNBEngine.oldParam (p := ℓ) αpull w, hw⟩) =
        (TateModule.proj ℓ _ n (sp w.1) + Fstar (TateModule.proj ℓ _ n (sp w.2)),
          Fstar (TateModule.proj ℓ _ n (sp w.1)) + δ (TateModule.proj ℓ _ n (sp w.2)))) :
    ∃ Told : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)),

      (∀ x : TateModule ℓ (JH M H), x ∈ Told ↔
        ∃ w₀ w₁ : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
          TateModule.proj ℓ (JH M H) n x =
            αpull 0 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
              αpull 1 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₁)) ∧

      Told ≤ Tf ∧

      Told ⊓ Tt = ⊥ ∧

      ∃ k : ℕ, ∀ x ∈ Tf, (((ℓ : ℕ) : ℤ_[ℓ]) ^ k) • x ∈ Told ⊔ Tt := by
  classical

  have hold : ∀ w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) × TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)),
      QPARNBEngine.oldParam (p := ℓ) αpull w ∈ Tf := fun w => by
    refine (hTf _).2 fun n => ?_
    have e : TateModule.proj ℓ (JH M H) n (QPARNBEngine.oldParam (p := ℓ) αpull w) =
        αpull 0 (((w.1 : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) +
          αpull 1 (((w.2 : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) : ℕ → JH (M / p) (infSubgroup p M H hpM)) n) := by
      rw [QPARNBEngine.oldParam_apply]; rfl
    rw [e]
    exact AddSubgroup.add_mem _ (hOldFin 0 n _ (TateModule.torsion w.1 n)) (hOldFin 1 n _ (TateModule.torsion w.2 n))

  let Rmap : (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) →+
      (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) :=
    AlgebraicCurve.Pic0Pair.blockOp (AddMonoidHom.id _) Fstar Fstar δ
  have hRmap : ∀ z, Rmap z = (z.1 + Fstar z.2, Fstar z.1 + δ z.2) := fun z => by
    rcases z with ⟨z₀, z₁⟩
    exact AlgebraicCurve.Pic0Pair.blockOp_apply _ _ _ _ z₀ z₁

  have hcomm : ∀ w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) × TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)),
      red ⟨QPARNBEngine.oldParam (p := ℓ) αpull w, hold w⟩ = QPARNBEngine.tmap Rmap (prodIso ℓ _ (sp w.1, sp w.2)) := fun w => by
    refine Subtype.ext (funext fun n => ?_)
    have h := hcompat w (hold w) n
    rw [TateModule.proj_apply] at h
    rw [h, QPARNBEngine.tmap_apply_coe, prodIso_apply_coe, hRmap]
    rfl

  have hpN : ¬ p ∣ M / p := fun h => hpM2 (by
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have := Nat.div_mul_cancel hpM
    rw [hc] at this
    rw [← this]; ring)
  obtain ⟨c, hc, hK, hS⟩ :=
    ModularCurve.exists_nsmul_eq_zero_and_exists_eq_frobeniusDegeneracyPair_torsion_qExpFunctionFieldC_of_ne
      (ResidueField ↥A) p (M / p) hpN (infSubgroup p M H hpM) F Finv Fstar hF hFinv hFstar pb δ hδ ℓ hℓp
  have hRker : ∀ (m : ℕ) (z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      ((ℓ ^ m : ℕ) : ℤ) • z = 0 → Rmap z = 0 → (c : ℤ) • z = 0 := fun m z hz hR => by
    rw [hRmap] at hR
    have hz1 : ((ℓ ^ m : ℕ) : ℤ) • z.1 = 0 := by simpa using congrArg Prod.fst hz
    have hz2 : ((ℓ ^ m : ℕ) : ℤ) • z.2 = 0 := by simpa using congrArg Prod.snd hz
    obtain ⟨h1, h2⟩ := hK m z.1 z.2 (AlgebraicCurve.Pic0.mem_torsion.2 hz1) (AlgebraicCurve.Pic0.mem_torsion.2 hz2)
      (congrArg Prod.fst hR) (congrArg Prod.snd hR)
    rw [natCast_zsmul]
    exact Prod.ext h1 h2
  have hRsurj : ∀ (n : ℕ) (z : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
      ((ℓ ^ n : ℕ) : ℤ) • z = 0 → ∃ (m : ℕ) (y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))),
        ((ℓ ^ m : ℕ) : ℤ) • y = 0 ∧ Rmap y = z := fun n z hz => by
    have hz1 : ((ℓ ^ n : ℕ) : ℤ) • z.1 = 0 := by simpa using congrArg Prod.fst hz
    have hz2 : ((ℓ ^ n : ℕ) : ℤ) • z.2 = 0 := by simpa using congrArg Prod.snd hz
    obtain ⟨m, y₀, y₁, hy₀, hy₁, e₀, e₁⟩ := hS n z.1 z.2 (AlgebraicCurve.Pic0.mem_torsion.2 hz1) (AlgebraicCurve.Pic0.mem_torsion.2 hz2)
    refine ⟨m, (y₀, y₁), Prod.ext (AlgebraicCurve.Pic0.mem_torsion.1 hy₀) (AlgebraicCurve.Pic0.mem_torsion.1 hy₁), ?_⟩
    rw [hRmap]
    exact Prod.ext e₀ e₁
  exact QPARNBEngine.exists_oldRange_clauses (p := ℓ) αpull Tt Tf hold red hred_ker sp (prodIso ℓ _) Rmap hcomm c hc hRker hRsurj

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem proj_red_oldParam_eq
    {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
    {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    {Λ : JHNeronObjectAtP.LevelData p M H hpM A} (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    {ℓ : ℕ} [Fact ℓ.Prime] (Tf : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (Fstar δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))
    (red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hred_pin : ∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
      TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s)))
    (sp : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) ≃ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hsp : ∀ (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM))) (n : ℕ) (s : SchemeHomOver Λ.σA Λ.f),
        (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w)).1 = barPt A ≫ s.1 →
        TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (sp w) =
          Λ.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s))
    (w : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)) × TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)))
    (hw : QPARNBEngine.oldParam (p := ℓ) αpull w ∈ Tf) (n : ℕ) :
    TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n
        (red ⟨QPARNBEngine.oldParam (p := ℓ) αpull w, hw⟩) =
      (TateModule.proj ℓ _ n (sp w.1) + Fstar (TateModule.proj ℓ _ n (sp w.2)),
        Fstar (TateModule.proj ℓ _ n (sp w.1)) + δ (TateModule.proj ℓ _ n (sp w.2))) := by

  obtain ⟨t₀, ht₀⟩ := QPARNBGeom.extendsToPlace_of_abelianSchemePropertyBundle Λ hΛ
    (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.1))
  obtain ⟨t₁, ht₁⟩ := QPARNBGeom.extendsToPlace_of_abelianSchemePropertyBundle Λ hΛ
    (Λ.pts (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.2))

  have hs₀ : O.pts (αpull 0 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.1)) =
      GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (NeronModelInfra.schemeHomOverComp t₀ (degPull 0)) :=
    Subtype.ext (by
      rw [hpull, ht₀, GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
  have hs₁ : O.pts (αpull 1 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.2)) =
      GoodReductionJacobian.schemeHomOverComp (barPt A) Λ.hσA (NeronModelInfra.schemeHomOverComp t₁ (degPull 1)) :=
    Subtype.ext (by
      rw [hpull, ht₁, GoodReductionJacobian.schemeHomOverComp_coe, NeronModelInfra.schemeHomOverComp_coe, Category.assoc])
  have hlev : TateModule.proj ℓ (JH M H) n (QPARNBEngine.oldParam (p := ℓ) αpull w) =
      αpull 0 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.1) +
        αpull 1 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w.2) := by
    rw [QPARNBEngine.oldParam_apply]; rfl

  have hsec : (O.pts (TateModule.proj ℓ (JH M H) n
      ((⟨QPARNBEngine.oldParam (p := ℓ) αpull w, hw⟩ : ↥Tf) : TateModule ℓ (JH M H)))).1 =
      barPt A ≫ (O.L.mul Λ.σA (NeronModelInfra.schemeHomOverComp t₀ (degPull 0))
        (NeronModelInfra.schemeHomOverComp t₁ (degPull 1))).1 := by
    change (O.pts (TateModule.proj ℓ (JH M H) n (QPARNBEngine.oldParam (p := ℓ) αpull w))).1 = _
    rw [hlev, O.pts_add, hs₀, hs₁, ← QPARNBGeom.schemeHomOverComp_barPt_mul, GoodReductionJacobian.schemeHomOverComp_coe]
  rw [hred_pin _ n _ hsec, QPARNBGeom.schemeHomOverComp_resPt_mul, QPARNBGeom.ptsSp_symm_mul, map_add]

  have e₀ : NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA)
        (NeronModelInfra.schemeHomOverComp t₀ (degPull 0)) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp
        (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) t₀) (degPull 0) :=
    Subtype.ext (Category.assoc _ _ _).symm
  have e₁ : NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA)
        (NeronModelInfra.schemeHomOverComp t₁ (degPull 1)) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp
        (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) t₁) (degPull 1) :=
    Subtype.ext (Category.assoc _ _ _).symm
  have h₀ : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
        (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) (NeronModelInfra.schemeHomOverComp t₀ (degPull 0)))) =
      (TateModule.proj ℓ _ n (sp w.1), Fstar (TateModule.proj ℓ _ n (sp w.1))) := by
    have h := hpullsp 0 (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) t₀)
    rw [if_pos rfl, ← hsp w.1 n t₀ ht₀] at h
    exact (congrArg (fun y => GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm y)) e₀).trans h
  have h₁ : GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (NeronModelInfra.schemeHomOverComp
        (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) (NeronModelInfra.schemeHomOverComp t₁ (degPull 1)))) =
      (Fstar (TateModule.proj ℓ _ n (sp w.2)), δ (TateModule.proj ℓ _ n (sp w.2))) := by
    have h := hpullsp 1 (NeronModelInfra.schemeHomOverComp (⟨resPt A, rfl⟩ : SchemeHomOver (resPt A ≫ Λ.σA) Λ.σA) t₁)
    rw [if_neg (show ¬ ((1 : Fin 2) = 0) by decide), ← hsp w.2 n t₁ ht₁] at h
    exact (congrArg (fun y => GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm y)) e₁).trans h
  exact (congrArg₂ (· + ·) h₀ h₁).trans (Prod.mk_add_mk _ _ _ _)

end ModularCurve.JHNeronObjectAtP.QPARNBReduce
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve.JHNeronObjectAtP.QPARNBReduce"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve.JHNeronObjectAtP"
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve"

end Geometry
p2m_reactivate "P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.QPARNBEngine P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve.JHNeronObjectAtP P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve.JHNeronObjectAtP.QPARNBReduce"

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicCurve IsLocalRing ModularCurve P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne.ModularCurve ModularCurve.JZeroNeronObjectAtP AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve ModularCurve.CharacterLattice"

p2m_open "ModularCurve.XHDRLevel~ΓN"
open _root_.ModularCurve.JHNeronObjectAtP (ΓN Fbar)
open scoped MatrixGroups

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]

    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (𝔛 : XHDRModelAtP p M H hpM hj)
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hθ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(xHFunctionFieldBar M H)) (u : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))), (f : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)) →
        ((θ f : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = qExpand (AlgebraicClosure ℚ) p (u : LaurentSeries (AlgebraicClosure ℚ)))
    (hwgen : ∀ (y y' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔛.Meta.C // q ≫ 𝔛.Meta.toBase = 𝟙 _}),
      y'.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ ≫ 𝔛.w.hom = y.1 ≫ 𝔛.eeta ≫ pullback.fst _ _ →
      𝔛.Meta.pointEquivPlace y' = SemilinearAut.ofAlgAut θ • 𝔛.Meta.pointEquivPlace y)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ))

    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (hD : RepresentsRelSubPic (toBase p (ΓM M H) hj) 𝔛.εinf (algEquivZeroCut (toBase p (ΓM M H) hj) 𝔛.εinf) (⟨O.G, O.g, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).1, (O.L.one (𝟙 (Spec (CommRingCat.of (R p))))).2⟩ : RelativePic0Designation (R p) (toBase p (ΓM M H) hj)))

    (hΛ : GoodReductionJacobian.AbelianSchemePropertyBundle (baseRing p) Λ.f)
    (hσ : Λ.σA = Spec.map (CommRingCat.ofHom ρ))
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)

    (Tt Tf : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)))
    (hTt : ∀ x : TateModule ℓ (JH M H), x ∈ Tt ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.toricPts (ℓ ^ n))
    (hTf : ∀ x : TateModule ℓ (JH M H), x ∈ Tf ↔ ∀ n : ℕ, TateModule.proj ℓ (JH M H) n x ∈ O.finPts (ℓ ^ n))

    (F Finv Fstar : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hF : ∀ z, F z = qExpFrobeniusPushforwardModL (ResidueField ↥A) (ΓN p M H hpM) p z)
    (hFinv : F.comp Finv = AddMonoidHom.id _ ∧ Finv.comp F = AddMonoidHom.id _)
    (hFstar : ∀ z, Fstar z = (p : ℤ) • Finv z)

    (pb : (ZMod (M / p))ˣ) (hpb : ((pb : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (δ : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) →+
      Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)))
    (hδ : ∀ z, δ z = SemilinearAut.ofAlgAut (diamondActionModL (ResidueField ↥A) (M / p) (infSubgroup p M H hpM)
      (CuspForm.gammaLift (M / p) pb)) • z)

    (αpull : Fin 2 → (JH (M / p) (infSubgroup p M H hpM) →+ JH M H))
    (degPull : Fin 2 → SchemeHomOver Λ.f O.g)
    (hpull : ∀ (i : Fin 2) (x : JH (M / p) (infSubgroup p M H hpM)),
      (O.pts (αpull i x)).1 = (Λ.pts x).1 ≫ (degPull i).1)
    (hpull_mul : ∀ (i : Fin 2) {T : Scheme.{0}} (s : T ⟶ base p) (x y : SchemeHomOver s Λ.f),
      schemeHomOverComp (Λ.L.mul s x y) (degPull i) =
        O.L.mul s (schemeHomOverComp x (degPull i)) (schemeHomOverComp y (degPull i)))

    (hpullsp : ∀ (i : Fin 2) (x : SchemeHomOver (resPt A ≫ Λ.σA) Λ.f),
      GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp x (degPull i))) =
        if i = 0 then (Λ.ptsSp.symm x, Fstar (Λ.ptsSp.symm x))
        else (Fstar (Λ.ptsSp.symm x), δ (Λ.ptsSp.symm x)))

    (hΛpts_add : ∀ x y : JH (M / p) (infSubgroup p M H hpM), Λ.pts (x + y) = Λ.L.mul _ (Λ.pts x) (Λ.pts y))
    (hΛptsSp_add : ∀ x y : Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)),
      Λ.ptsSp (x + y) = ofFibrePt ((Λ.L.baseChange (resPt A ≫ Λ.σA)).mul _ (toFibrePt (Λ.ptsSp x)) (toFibrePt (Λ.ptsSp y))))

    (red : ↥Tf →ₗ[ℤ_[ℓ]] TateModule ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))))
    (hred_pin : ∀ (x : ↥Tf) (n : ℕ) (s : SchemeHomOver Λ.σA O.g),
      (O.pts (TateModule.proj ℓ (JH M H) n (x : TateModule ℓ (JH M H)))).1 = barPt A ≫ s.1 →
      TateModule.proj ℓ (Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A)) × Pic0 (ResidueField ↥A) (Fbar p M H hpM (ResidueField ↥A))) n (red x) =
        GluedPic0.toPic0Pair O.ssFinset (O.ptsSp.symm (schemeHomOverComp ⟨resPt A, rfl⟩ s)))
    (hred_ker : ∀ x : ↥Tf, red x = 0 ↔ (x : TateModule ℓ (JH M H)) ∈ Tt) :
    ∃ Told : Submodule ℤ_[ℓ] (TateModule ℓ (JH M H)),

      (∀ x : TateModule ℓ (JH M H), x ∈ Told ↔
        ∃ w₀ w₁ : TateModule ℓ (JH (M / p) (infSubgroup p M H hpM)), ∀ n : ℕ,
          TateModule.proj ℓ (JH M H) n x =
            αpull 0 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₀) +
              αpull 1 (TateModule.proj ℓ (JH (M / p) (infSubgroup p M H hpM)) n w₁)) ∧

      Told ≤ Tf ∧

      Told ⊓ Tt = ⊥ ∧

      ∃ k : ℕ, ∀ x ∈ Tf, (((ℓ : ℕ) : ℤ_[ℓ]) ^ k) • x ∈ Told ⊔ Tt := by

  obtain ⟨sp, hsp⟩ :=
    ModularCurve.JHNeronObjectAtP.LevelData.exists_linearEquiv_tateModule_proj_eq_ptsSp_symm_section_of_ne
      p M H hpM A hA Λ hΛ hΛpts_add hΛptsSp_add ℓ hℓp

  have hOldFin : ∀ (i : Fin 2) (n : ℕ) (w : JH (M / p) (infSubgroup p M H hpM)),
      ((ℓ ^ n : ℕ) : ℤ) • w = 0 → αpull i w ∈ O.finPts (ℓ ^ n) := fun i n w hw =>
    ModularCurve.JHNeronObjectAtP.QPARNBGeom.apply_mem_finPts_of_zsmul_eq_zero O hΛ αpull degPull hpull i (ℓ ^ n) w hw
  exact ModularCurve.JHNeronObjectAtP.QPARNBReduce.of_geometricInputs p M H hpM hpM2 hHp hj 𝔛 θ hθ hwgen A hA ρ hρ Λ O hD hΛ hσ
    ℓ hℓp Tt Tf hTt hTf F Finv Fstar hF hFinv hFstar pb hpb δ hδ αpull degPull hpull hpull_mul hpullsp hΛpts_add hΛptsSp_add
    red hred_pin hred_ker hOldFin sp
    (fun w hw n => ModularCurve.JHNeronObjectAtP.QPARNBReduce.proj_red_oldParam_eq O hΛ Tf Fstar δ αpull degPull hpull hpullsp
      red hred_pin sp hsp w hw n)

end S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne
end P2MW
export P2MW.S_ModularCurve_JHNeronObjectAtP_exists_oldLattice_inf_toricLattice_eq_bot_and_finiteLattice_le_sup_tateModule_jH_of_ne (solution)
