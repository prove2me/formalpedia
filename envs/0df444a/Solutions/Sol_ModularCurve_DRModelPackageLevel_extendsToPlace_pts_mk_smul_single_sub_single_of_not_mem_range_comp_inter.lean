-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/03eeaaa3-263b-57df-9b87-bc6f39d51cf4

import Mathlib
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
import Theorems.Thm_ModularCurve_DRModelPackageLevel_residue_comp_section_smul_eq_of_mem_inertia
import Theorems.Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_smoothLocus_of_mem_range_fst_geomGeneric
import Theorems.Thm_ModularCurve_DRModelPackageLevel_mem_preimage_smoothLocus_iff_not_mem_range_comp_inter
import Theorems.Thm_ValuationSubring_eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap SheafOfModules.isIso_ihomModelToIhom ModularCurve.PhiGen.instNeZeroPhiGenCosetA instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve"
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx"
p2m_attr_erase "instance" "AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup"
p2m_attr_erase "instance" "ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule PresheafOfModules.ExteriorPower.instModulePresheafAb ModularCurve.JZeroNeronObjectAtP.LevelModel.Meta₀_chart_nonempty ModularCurve.JZeroNeronObjectAtP.LevelModel.eeta₀_iso"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec"
p2m_attr_erase "simp" "compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃"
p2m_attr_erase "simp" "WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply"
p2m_attr_erase "simp" "AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply ModularCurve.JZeroNeronObjectAtP.LevelModel.mk.injEq ModularCurve.JZeroNeronObjectAtP.LevelModel.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.DRLevel ModularCurve.JZeroNeronObjectAtP"

attribute [local instance] ModularCurve.DRModelPackageLevel.neZero_mul

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)
    [IsProper (toBase N₀ p)]

    (D : RelativePic0Designation (R p) (toBase N₀ p))
    (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

    (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
    (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

    (ajQ : SchemeHomOver (baseChange (R p) (toBase N₀ p) ℚ) (D.baseChange ℚ).toBase)
    (hajQε : (sectionBaseChange ℚ 𝔓.εinf).1 ≫ ajQ.1 = (D.baseChange ℚ).zeroSection)
    (hajQ : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ℚ))
        (x : SchemeHomOver t (baseChange (R p) (toBase N₀ p) ℚ)),
      Nonempty ((hDQ.poincare.pullbackAlong
          ⟨x.1 ≫ ajQ.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) ajQ.2).trans x.2)⟩).L ≅
        (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) x.1 x.2).lineBundle ⊗
          (RelEffCartierDiv.ofPoint (baseChange (R p) (toBase N₀ p) ℚ) (t ≫ (sectionBaseChange ℚ 𝔓.εinf).1)
            ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) (sectionBaseChange ℚ 𝔓.εinf).2).trans
              (Category.comp_id t)))).idealModule))

    (kQ : pullback (toBase N₀ p) (genPt p) ⟶ pullback (toBase N₀ p) (specMap (R p) ℚ))
    (hkQ₁ : kQ ≫ pullback.fst (toBase N₀ p) (specMap (R p) ℚ) = pullback.fst (toBase N₀ p) (genPt p))
    (hkQ₂ : kQ ≫ pullback.snd (toBase N₀ p) (specMap (R p) ℚ) = pullback.snd (toBase N₀ p) (genPt p) ≫ specMap ℚ (AlgebraicClosure ℚ))

    (ajbar : 𝔓.Meta.C ⟶ D.P) (hajbar : ajbar = 𝔓.eeta ≫ kQ ≫ ajQ.1 ≫ pullback.fst D.toBase (specMap (R p) ℚ))
    (hajbar_over : ajbar ≫ D.toBase = 𝔓.Meta.toBase ≫ genPt p)
    (εbar : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
    (hεbar : εbar.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1) (hεbar_aj : εbar.1 ≫ ajbar = genPt p ≫ D.zeroSection)

    (pts : JZero (N₀ * p) ≃ SchemeHomOver (genPt p) D.toBase)
    (hpts_add : ∀ x y : JZero (N₀ * p),
      pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
    (hpts_galois : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
      (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
    (hpts_aj : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
      s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
      ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
        (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
          Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :
    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N₀
    ∀ (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)))
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (_hs : Spec.map (CommRingCat.ofHom A.subtype) ≫ s.1 =
        ((𝔓.Meta.pointEquivPlace).symm V).1 ≫ 𝔓.eeta ≫
          pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))))
      (y : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ))
      (_hy₁ : y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1)
      (_hy₂ : y ≫ pullback.snd _ _ = 𝟙 _),
      ¬ (Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 0).base ∧
          Set.range y.base ⊆ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 1).base) →
        ∀ σ ∈ A.inertiaSubgroupIn ℚ,
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))),
            ExtendsToPlace A (Spec.map (CommRingCat.ofHom ρ))
              (pts (Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1, hdeg⟩)) := by
  intro V s hs y hy₁ hy₂ hnot σ hσ hdeg
  classical
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A

  obtain ⟨s₁, hs₁, -⟩ := ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm
    N₀ p hpN₀ 𝔓 A ρ hρ (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V)
  have hres : Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s₁.1 =
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 :=
    ModularCurve.DRModelPackageLevel.residue_comp_section_smul_eq_of_mem_inertia N₀ p hpN₀ 𝔓 A ρ hρ σ hσ V s hs s₁ hs₁

  set ypt := y.base (IsLocalRing.closedPoint (ResidueField ↥A)) with hyptdef
  have hrange : Set.range y.base = {ypt} := by
    ext z; constructor
    · rintro ⟨t, rfl⟩; rw [Set.mem_singleton_iff, show t = IsLocalRing.closedPoint _ from Subsingleton.elim _ _]
    · rintro rfl; exact ⟨_, rfl⟩
  have hnot' : ¬ (ypt ∈ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 0).base ∧
      ypt ∈ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) 1).base) := by
    rintro ⟨h0, h1⟩
    exact hnot ⟨by rw [hrange]; exact Set.singleton_subset_iff.mpr h0, by rw [hrange]; exact Set.singleton_subset_iff.mpr h1⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : Fin 2, ypt ∈ Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) c₀).base := by
    rcases 𝔓.comp_jointly_surjective (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) ypt with h | h
    exacts [⟨0, h⟩, ⟨1, h⟩]

  have hysm : (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom ((IsLocalRing.residue ↥A).comp ρ)))).base ypt ∈
      (𝔓.smoothLocus : Set (X N₀ p)) :=
    (ModularCurve.DRModelPackageLevel.mem_preimage_smoothLocus_iff_not_mem_range_comp_inter N₀ p hpN₀ 𝔓
      (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) ypt).mpr hnot'

  have hpts : ∀ a : Spec (CommRingCat.of ↥A), a = IsLocalRing.closedPoint ↥A ∨
      a = (Spec.map (CommRingCat.ofHom A.subtype)).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) := by
    intro a
    by_cases ha : a.asIdeal = IsLocalRing.maximalIdeal ↥A
    · left; exact PrimeSpectrum.ext ha
    · right
      have hb : a.asIdeal = ⊥ :=
        ValuationSubring.eq_bot_of_isPrime_of_ne_maximalIdeal_of_liesOverPrime (Fact.out) A hA a.asIdeal ha
      apply PrimeSpectrum.ext
      rw [hb]
      symm
      show Ideal.comap A.subtype (IsLocalRing.maximalIdeal (AlgebraicClosure ℚ)) = ⊥
      rw [IsLocalRing.isField_iff_maximalIdeal_eq.mp (Field.toIsField (AlgebraicClosure ℚ))]
      exact Ideal.comap_bot_of_injective A.subtype Subtype.val_injective
  have hsmooth : ∀ (t : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
      (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))),
      Spec.map (CommRingCat.ofHom A.subtype) ≫ t.1 = ((𝔓.Meta.pointEquivPlace).symm W).1 ≫ 𝔓.eeta ≫
        pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (DRLevel.R p) (AlgebraicClosure ℚ)))) →
      Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ t.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 →
      Set.range t.1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)) := by
    intro t W ht htres
    rintro _ ⟨a, rfl⟩
    rcases hpts a with rfl | rfl
    ·
      have e1 : t.1.base (IsLocalRing.closedPoint ↥A) =
          (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ t.1).base (IsLocalRing.closedPoint _) := by
        rw [Scheme.Hom.comp_apply]
        congr 1
        exact (IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)).symm
      rw [e1, htres, ← hy₁, Scheme.Hom.comp_apply]
      exact hysm
    ·
      apply ModularCurve.DRModelPackageLevel.mem_smoothLocus_of_mem_range_fst_geomGeneric N₀ p hpN₀ 𝔓
      refine ⟨(((𝔓.Meta.pointEquivPlace).symm W).1 ≫ 𝔓.eeta).base (IsLocalRing.closedPoint _), ?_⟩
      rw [← Scheme.Hom.comp_apply, Category.assoc, ← ht, Scheme.Hom.comp_apply]
  have hsm_s : Set.range s.1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)) := hsmooth s V hs rfl
  have hsm_s₁ : Set.range s₁.1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)) := hsmooth s₁ _ hs₁ hres

  let sv : Fin 2 → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p) := ![s, s₁]
  let pos : Fin 2 → ℕ := ![0, 1]
  let neg : Fin 2 → ℕ := ![1, 0]
  have hsmv : ∀ i, Set.range (sv i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)) := by
    intro i; fin_cases i
    exacts [hsm_s, hsm_s₁]
  have hy₁v : ∀ i : Fin 2, y ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (sv i).1 := by
    intro i; fin_cases i
    · exact hy₁
    · exact hy₁.trans hres.symm
  have hcv : ∀ i : Fin 2, Set.range y.base ⊆
      Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) ((fun _ => c₀) i)).base := by
    intro i; rw [hrange]; exact Set.singleton_subset_iff.mpr hc₀
  have hdegv : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => (fun _ : Fin 2 => c₀) i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
    intro j
    by_cases hj : c₀ = j
    · rw [Finset.filter_true_of_mem (fun _ _ => hj), Fin.sum_univ_two]
      simp [pos, neg]
    · rw [Finset.filter_false_of_mem (fun _ _ => hj), Finset.sum_empty]
  obtain ⟨a, ha⟩ := ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
    N₀ p hpN₀ 𝔓 D hD A hA ρ hρ sv hsmv (fun _ => c₀) (fun _ => y) hy₁v (fun _ => hy₂) hcv pos neg hdegv

  let q : Fin 2 → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _} :=
    ![(𝔓.Meta.pointEquivPlace).symm V, (𝔓.Meta.pointEquivPlace).symm (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V)]
  have hqs : ∀ i, (q i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ (sv i).1 := by
    intro i; fin_cases i
    · exact hs.symm
    · exact hs₁.symm
  have hn : (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 := by rw [Fin.sum_univ_two]; simp [pos, neg]
  have hDx : ((⟨arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1, hdeg⟩ :
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))) :
        Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
      ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (q i)) ((pos i : ℤ) - (neg i : ℤ)) := by
    rw [Fin.sum_univ_two]
    show arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • (Finsupp.single V (1 : ℤ)) - Finsupp.single V 1 =
      Finsupp.single (𝔓.Meta.pointEquivPlace ((𝔓.Meta.pointEquivPlace).symm V)) ((0 : ℕ) - (1 : ℕ) : ℤ) +
        Finsupp.single (𝔓.Meta.pointEquivPlace ((𝔓.Meta.pointEquivPlace).symm
          (arithmeticGalois (modularFunctionFieldFull (N₀ * p)) σ • V))) ((1 : ℕ) - (0 : ℕ) : ℤ)
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, AlgebraicCurve.SemilinearAut.smul_single]
    simp only [Nat.cast_zero, Nat.cast_one, zero_sub, sub_zero, Finsupp.single_neg]
    abel
  have hG3 := ModularCurve.DRModelPackageLevel.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
    N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add hpts_galois hpts_aj
    A ρ hρ sv hsmv q hqs pos neg hn _ hDx a ha
  exact ⟨a, hG3⟩

end S_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_extendsToPlace_pts_mk_smul_single_sub_single_of_not_mem_range_comp_inter (solution)
