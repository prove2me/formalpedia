-- Prove2me | solution 1 for ModularCurve.DRModelPackageLevel.abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/3f31ce01-c0d2-5106-a515-f575f2f738d9

import Mathlib
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pullbackCurve_comp0_sectionTwist_iso
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero
import Theorems.Thm_ModularCurve_DRModelPackageLevel_nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero
import Definitions.Def_ModularCurve_NodeDescentTower
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_finiteDimensional_adjoin_coeffEmb_jq_of_neZero
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_isSeparable
import Theorems.Thm_ModularCurve_DRModelPackageLevel_existsUnique_section_comp_eq_pointEquivPlace_symm
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
import Theorems.Thm_ModularCurve_DRModelPackageLevel_pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceFst_of_isStrictFst
import Theorems.Thm_ModularCurve_DRModelPackageLevel_exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
import Definitions.Def_ModularCurve_JZeroNeronObjectAtP
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_DRModelPackageLevel
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelPicardPullback
import Definitions.Def_AlgebraicGeometry_ModulesRigidify
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveBase
import Definitions.Def_AlgebraicGeometry_RelSubPicBaseChange
import Definitions.Def_AlgebraicGeometry_RelativePic0DesignationBaseChange
import Definitions.Def_GoodReductionJacobian_RelativeGroupLawBaseChange
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero instIsScalarTowerIntegralClosure instNeZeroIdealUnderOfNontrivialOfIsDomainOfIsIntegral_definitions instAlgebraIntegralClosure_1 isInvariant_integralClosure instAlgebraIntegralClosure continuousSMulDiscrete_integralClosure mulSemiringActionIntegralClosure smulCommClass_integralClosure instIsDomainIntegralClosure instIsIntegralIntegralClosure instCommRingIntegralClosure instFaithfulSMulIntegralClosure instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar"
p2m_attr_erase "instance" "ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "instance" "WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular SheafOfModules.isIso_ihomModelToIhom TwoChartCech.Sections.M0_moduleA TwoChartCech.Sections.M1_module TwoChartCech.Cover.A01_algebra TwoChartCech.Cover.A0_algebra TwoChartCech.Cover.A1_commRing TwoChartCech.Cover.A1_algebra TwoChartCech.Sections.M01_module TwoChartCech.Sections.M0_addCommGroup TwoChartCech.Sections.M0_tower TwoChartCech.Sections.M01_addCommGroup TwoChartCech.Cover.A0_commRing TwoChartCech.Sections.M1_tower TwoChartCech.Sections.M01_moduleA TwoChartCech.Sections.M0_module TwoChartCech.Sections.M1_moduleA TwoChartCech.Sections.M1_addCommGroup TwoChartCech.Cover.A01_commRing TwoChartCech.Sections.M01_tower CoherentBaseChange.TwoTermComplex.C0_module CoherentBaseChange.TwoTermComplex.C0_addCommGroup CoherentBaseChange.TwoTermComplex.C1_module CoherentBaseChange.TwoTermComplex.C1_addCommGroup CoherentBaseChange.TwoTermComplex.C0_free CoherentBaseChange.TwoTermComplex.C1_finite CoherentBaseChange.TwoTermComplex.C0_finite CoherentBaseChange.TwoTermComplex.C1_free AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallyInjectiveFunUliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsLocallySurjectiveFunUliftYonedaGluedToSheafOfIsLocallySurjectiveZariskiTopologyDescFunctorOppositeType AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsOpenImmersionToGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.instIsIsoSheafZariskiTopologyTypeUliftYonedaGluedToSheaf AlgebraicGeometry.RelPicard.instIsOpenImmersionToGlued PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.FGSubalgebra.instIsDirectedLe AlgebraicGeometry.FGSubalgebra.instQuasiSeparatedSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsCofilteredOpposite"
p2m_attr_erase "instance" "AlgebraicGeometry.FGSubalgebra.instIsAffineObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instNonempty AlgebraicGeometry.FGSubalgebra.instNonemptySubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instCompactSpaceCarrierCarrierCommRingCatObjOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsDirectedSubtypeLeSubalgebraValFG AlgebraicGeometry.FGSubalgebra.instIsAffineHomMapOppositeSchemeSpecDiagram AlgebraicGeometry.FGSubalgebra.instIsFiltered AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicGeometry.FGSubalgebra.tensorStage_directedSystem AlgebraicGeometry.RelEffCartierDiv.isClosedImmersion_subschemeι_resProdMap AlgebraicGeometry.RelEffCartierDiv.isOpenImmersion_resProdMap ModularCurve.JZeroNeronObjectAtP.LevelModel.Meta₀_chart_nonempty ModularCurve.JZeroNeronObjectAtP.LevelModel.eeta₀_iso"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app"
p2m_attr_erase "simp" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord RegularLocalRingQuotientAscent.dualNumberFst_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"
p2m_attr_erase "simp" "WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero"
p2m_attr_erase "simp" "TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply"
p2m_attr_erase "simp" "SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply ModularCurve.DRLevel.fibreMap0_fst_assoc ModularCurve.DRLevel.fibreMap_snd_assoc ModularCurve.DRLevel.fibreMap_snd ModularCurve.DRLevel.sectionFibre_fst ModularCurve.DRLevel.fibreMap0_snd ModularCurve.DRLevel.sectionFibre_fst_assoc ModularCurve.DRLevel.sectionFibre_snd ModularCurve.DRLevel.fibreMap_fst ModularCurve.DRLevel.sectionFibreOver_snd ModularCurve.DRModelPackageLevel.εinf0_snd_assoc ModularCurve.DRLevel.fibreMap0_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst ModularCurve.DRModelPackageLevel.εinf0_snd ModularCurve.DRLevel.sectionFibreOver_snd_assoc ModularCurve.DRLevel.sectionFibreOver_fst_assoc ModularCurve.DRLevel.fibreMap_fst_assoc ModularCurve.DRLevel.fibreMap0_fst ModularCurve.DRLevel.sectionFibre_snd_assoc AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U1 AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.injEq AlgebraicGeometry.SmoothProperCurve.FiniteMapData.mk.sizeOf_spec AlgebraicGeometry.SmoothProperCurve.FiniteMapData.twoAffineOpenCover_U0 AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.injEq AlgebraicGeometry.Scheme.TwoAffineOpenCover.mk.sizeOf_spec AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U1 AlgebraicGeometry.Scheme.TwoAffineOpenCover.pullback_U0 TwoChartCech.Sections.mk.injEq TwoChartCech.Cover.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.GrothendieckComplex.mk.injEq TwoChartCech.Sections.mk.sizeOf_spec TwoChartCech.Cover.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r0_apply TwoChartCech.GrothendieckComplex.mk.sizeOf_spec TwoChartCech.Cover.lineBundle_r1_apply CoherentBaseChange.TwoTermComplex.mk.sizeOf_spec CoherentBaseChange.TwoTermComplex.mk.injEq CategoryTheory.Functor.OverTotal.ofFibre_fst CategoryTheory.Functor.overTotal_map_fst AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_J AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t' AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYoneda_toGlued_uliftYonedaGluedToSheaf_assoc AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_toGlued AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_openCover_map AlgebraicGeometry.Scheme.LocalRepresentabilityULift.uliftYonedaGluedToSheaf_app_comp AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_V AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_t AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_U AlgebraicGeometry.Scheme.LocalRepresentabilityULift.glueData_f AlgebraicGeometry.RelPicard.designationOfRepresentableBy_P AlgebraicGeometry.RelPicard.designationOfRepresentableBy_toBase AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc"
p2m_attr_erase "simp" "AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.FGSubalgebra.cocone_ι_app_apply AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.LFP.stageHom_val AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp AlgebraicGeometry.RelEffCartierDiv.functor_map_fst AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_pullbackAlong AlgebraicGeometry.RelEffCartierDiv.IsUniversal.homEquiv_symm_apply AlgebraicGeometry.RelEffCartierDiv.IsUniversal.lift_comp_assoc AlgebraicGeometry.RelEffCartierDiv.supportedIn_top AlgebraicGeometry.RelEffCartierDiv.mem_supportedIn_iff AlgebraicGeometry.RelEffCartierDiv.supportedIn_top_eq"
p2m_attr_erase "simp" "AlgebraicGeometry.RelEffCartierDiv.restrictAlong_extendAlong AlgebraicGeometry.RelEffCartierDiv.extendAlong_I AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd AlgebraicGeometry.RelEffCartierDiv.restrictAlong_I AlgebraicGeometry.RelEffCartierDiv.extendAlong_restrictAlong AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_snd_assoc AlgebraicGeometry.RelEffCartierDiv.resProdMap_fst CoherentBaseChange.FibreH0Family.mk.sizeOf_spec CoherentBaseChange.FibreH0Family.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.injEq AlgebraicGeometry.Scheme.Modules.ProjPresentation.mk.sizeOf_spec AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj ModularCurve.JZeroNeronObjectAtP.LevelModel.mk.injEq ModularCurve.JZeroNeronObjectAtP.LevelModel.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry P2MW.S_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField.AlgebraicGeometry NeronModelInfra GoodReductionJacobian AlgebraicGeometry.RelPicard AlgebraicGeometry.SmoothProperCurve AlgebraicCurve IsLocalRing ModularCurve ModularCurve.JZeroNeronObjectAtP~LevelModel ModularCurve.DRLevel"

theorem M3Sol.isCurveOver_bar (M : ℕ) [NeZero M] :
    AlgebraicCurve.IsCurveOver (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M) := by
  let x : ↥(ModularCurve.modularFunctionFieldBar M) :=
    ⟨ModularCurve.coeffEmb (AlgebraicClosure ℚ) ModularCurve.jq,
      ModularCurve.coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (ModularCurve.jq_mem_full M)⟩
  have hx : Transcendental (AlgebraicClosure ℚ) x := by
    intro halg
    apply ModularCurve.transcendental_jqModC (AlgebraicClosure ℚ)
    have h := halg.algHom (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M)
      (LaurentSeries (AlgebraicClosure ℚ)))
    have hval : (IsScalarTower.toAlgHom (AlgebraicClosure ℚ) ↥(ModularCurve.modularFunctionFieldBar M)
        (LaurentSeries (AlgebraicClosure ℚ))) x = ModularCurve.jqModC (AlgebraicClosure ℚ) := by
      show (x : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)
      exact ModularCurve.NodeLocalized.coeffEmb_jq_eq
    rwa [hval] at h
  haveI hfin := ModularCurve.finiteDimensional_adjoin_coeffEmb_jq_of_neZero M
  haveI : Algebra.IsSeparable (IntermediateField.adjoin (AlgebraicClosure ℚ) ({x} : Set ↥(ModularCurve.modularFunctionFieldBar M)))
      ↥(ModularCurve.modularFunctionFieldBar M) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact AlgebraicCurve.isCurveOver_of_transcendental_of_isSeparable (AlgebraicClosure ℚ) _ x hx hfin inferInstance

section PTEXT
open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry
p2m_export "AlgebraicGeometry" "Spec.map_comp Surjective SmoothOfRelativeDimension IsProper Scheme.Modules.pullback Scheme.Hom GeometricallyIntegral Scheme.Hom.stalkMap_congr_point_assoc stalkClosedPointIso Scheme.Hom.stalkMap_congr_hom Spec Scheme.Hom.stalkMap_comp Spec.map Scheme ext_of_isDominant_of_isSeparated Scheme.stalkClosedPointTo pointEquivClosedPoint IsSeparated IsDominant Scheme.Modules SpecToEquivOfLocalRing_eq_iff isDominant_iff pointEquivClosedPoint_apply_coe Scheme.Hom.stalkMap_id SpecToEquivOfLocalRing RelPicard.postComp Scheme.Modules.rigidify Scheme.Modules.rigidifyMapIso RelEffCartierDiv RelEffCartierDiv.ofPoint"
p2m_open "AlgebraicGeometry"

theorem RingHom.eq_of_isLocalRing_of_comp_eq_id
    {A K : Type*} [CommRing A] [IsLocalRing A] [Field K]
    (φ ψ : A →+* K) (ι : K →+* A)
    (hφ : φ.comp ι = RingHom.id K) (hψ : ψ.comp ι = RingHom.id K) : φ = ψ := by
  have hφs : Function.Surjective φ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hφ k⟩
  have hψs : Function.Surjective ψ := fun k => ⟨ι k, by simpa using RingHom.congr_fun hψ k⟩
  have hker : RingHom.ker φ = RingHom.ker ψ := by
    rw [IsLocalRing.ker_eq_maximalIdeal φ hφs, IsLocalRing.ker_eq_maximalIdeal ψ hψs]
  ext a
  have h1 : a - ι (φ a) ∈ RingHom.ker φ := by
    rw [RingHom.mem_ker, map_sub, sub_eq_zero]
    simpa using (RingHom.congr_fun hφ (φ a)).symm
  rw [hker, RingHom.mem_ker, map_sub, sub_eq_zero] at h1
  rw [h1]
  simpa using (RingHom.congr_fun hψ (φ a)).symm

namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Modules.pullback Hom mk Hom.stalkMap_congr_point_assoc Hom.stalkMap_congr_hom Hom.stalkMap_comp stalkClosedPointTo Modules residue Hom.stalkMap_id Modules.rigidify Modules.rigidifyMapIso" end Scheme
p2m_open_scoped "AlgebraicGeometry.Scheme" in

theorem Scheme.ext_of_section_base_eq {κ : Type u} [Field κ] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of κ)) (p q : Spec (.of κ) ⟶ X)
    (hp : p ≫ f = 𝟙 _) (hq : q ≫ f = 𝟙 _)
    (h : p (closedPoint κ) = q (closedPoint κ)) : p = q := by

  have hpt : ∀ y : Spec (.of κ), y = closedPoint κ := fun y => Subsingleton.elim _ _

  have key : ∀ (r : Spec (.of κ) ⟶ X) (_ : r ≫ f = 𝟙 _),
      f.stalkMap (r (closedPoint κ)) ≫ r.stalkMap (closedPoint κ) =
        ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (r (closedPoint κ)))))).hom := by
    intro r hr
    have := Scheme.Hom.stalkMap_congr_hom _ _ hr (closedPoint κ)
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_id] at this

    erw [Category.comp_id] at this
    exact this

  let ι : CommRingCat.of κ ⟶ X.presheaf.stalk (p (closedPoint κ)) :=
    (stalkClosedPointIso (.of κ)).inv ≫
      ((Spec (.of κ)).presheaf.stalkCongr (.of_eq (hpt (f (p (closedPoint κ)))).symm)).hom ≫
        f.stalkMap (p (closedPoint κ))
  have h1 : ι ≫ Scheme.stalkClosedPointTo p = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [reassoc_of% (key p hp)]
    simp
  have h2 : ι ≫ ((X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q) = 𝟙 _ := by
    simp only [ι, Scheme.stalkClosedPointTo, Category.assoc]
    rw [Scheme.Hom.stalkMap_congr_point_assoc f _ _ h, reassoc_of% (key q hq)]
    simp

  apply (SpecToEquivOfLocalRing X (.of κ)).injective
  refine SpecToEquivOfLocalRing_eq_iff.mpr ⟨h, ?_⟩
  change Scheme.stalkClosedPointTo p =
    (X.presheaf.stalkCongr (.of_eq h)).hom ≫ Scheme.stalkClosedPointTo q
  refine CommRingCat.hom_ext ?_
  refine RingHom.eq_of_isLocalRing_of_comp_eq_id (K := κ) _ _ ι.hom ?_ ?_
  · rw [← CommRingCat.hom_comp, h1, CommRingCat.hom_id]
  · rw [← CommRingCat.hom_comp, h2, CommRingCat.hom_id]

end AlgebraicGeometry

end PTEXT

theorem M3Sol.ext_of_section_of_apply_eq {X : Scheme.{0}} {K : Type} [Field K] (q : X ⟶ Spec (CommRingCat.of K))
    (f g : Spec (CommRingCat.of K) ⟶ X) (hf : f ≫ q = 𝟙 _) (hg : g ≫ q = 𝟙 _)
    (h : f.base (IsLocalRing.closedPoint K) = g.base (IsLocalRing.closedPoint K)) : f = g :=
  AlgebraicGeometry.Scheme.ext_of_section_base_eq q f g hf hg h

theorem M3Sol.schemeHomOverComp_eq_postComp {R : Type} [CommRing R] {X X' T : Scheme.{0}}
    {x : X ⟶ Spec (CommRingCat.of R)} {x' : X' ⟶ Spec (CommRingCat.of R)} {t : T ⟶ Spec (CommRingCat.of R)}
    (a : SchemeHomOver t x) (φ : SchemeHomOver x x') :
    NeronModelInfra.schemeHomOverComp a φ = AlgebraicGeometry.RelPicard.postComp φ a :=
  Subtype.ext rfl

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 25600000 in

theorem solution
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hpN₀ : ¬ p ∣ N₀) (𝔓 : DRModelPackageLevel N₀ p hpN₀)

    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (ρ : R p →+* ↥A) (hρ : A.subtype.comp ρ = algebraMap (R p) (AlgebraicClosure ℚ)) :

    haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
    letI := instDecidableEqResidueFieldSemistable A
    letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
    letI := heckeModuleBar (N₀ * p)
    letI := heckeModuleBar N₀
    ∀
      (D : RelativePic0Designation (R p) (toBase N₀ p))
      (hD : RepresentsRelSubPic (toBase N₀ p) 𝔓.εinf (algEquivZeroCut (toBase N₀ p) 𝔓.εinf) D)

      (_ : IsSeparated D.toBase)

      (_ : ∀ (y : ↥(fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))),
          ¬ (y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0).base ∧
              y ∈ Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1).base) →
            (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base y ∈
              (𝔓.smoothLocus : Set (X N₀ p)))
      (ε₀ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (R p)))) (toBase0 N₀ p))
      (D₀ : RelativePic0Designation (R p) (toBase0 N₀ p))
      (hD₀ : RepresentsRelSubPic (toBase0 N₀ p) ε₀ (algEquivZeroCut (toBase0 N₀ p) ε₀) D₀)
      [IsProper (baseChange (R p) (toBase N₀ p) (ResidueField ↥A))]
      [IsProper (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))] [SmoothOfRelativeDimension 1 (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      [GeometricallyIntegral (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))]
      (hDκ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)
        (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)) (D.baseChange (ResidueField ↥A)))

      (_ : Nonempty (hDκ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A)
        (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hD₀κ : RepresentsRelSubPic (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)
        (algEquivZeroCut (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) ε₀)) (D₀.baseChange (ResidueField ↥A)))
      (_ : Nonempty (hD₀κ.poincare.L ≅ (BaseChange.ofR (toBase0 N₀ p) ε₀ (ResidueField ↥A)
        (hD₀.poincare.pullbackAlong ⟨pullback.fst D₀.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩)).L))
      (hε₁' : (sectionBaseChange (ResidueField ↥A) ε₀).1 ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0 = (sectionBaseChange (ResidueField ↥A) 𝔓.εinf).1)
      (abq : Fin 2 → SchemeHomOver (D.baseChange (ResidueField ↥A)).toBase (D₀.baseChange (ResidueField ↥A)).toBase)

      (_ : abq 0 = RepresentsRelSubPic.pullbackHom (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        hε₁' hDκ hD₀κ)
      (_ : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of (ResidueField ↥A))) (a : SchemeHomOver t (D.baseChange (ResidueField ↥A)).toBase),
        Nonempty ((hD₀κ.poincare.pullbackAlong (NeronModelInfra.schemeHomOverComp a (abq 1))).L ≅
          Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t (sectionBaseChange (ResidueField ↥A) ε₀))
              (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) t)
            ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
              (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) t)).obj (hDκ.poincare.pullbackAlong a).L)))

      (hDQ : RepresentsRelSubPic (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)
          (algEquivZeroCut (baseChange (R p) (toBase N₀ p) ℚ) (sectionBaseChange ℚ 𝔓.εinf)) (D.baseChange ℚ))
      (hPQ : Nonempty (hDQ.poincare.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf ℚ
          (hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) ℚ), pullback.condition⟩)).L))

      (_ : IsSeparated (baseChange (R p) (toBase N₀ p) ℚ))

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
      (_ : ∀ x y : JZero (N₀ * p),
        pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD).mul _ (pts x) (pts y))
      (_ : ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero (N₀ * p)),
        (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1)
      (_ : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _}),
        s.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) = genPt p ≫ 𝔓.εinf.1 →
        ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar (N₀ * p)),
          (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
            Finsupp.single (𝔓.Meta.pointEquivPlace x) 1 - Finsupp.single (𝔓.Meta.pointEquivPlace s) 1 ∧
          (pts (Pic0.mk Dv)).1 = x.1 ≫ ajbar)

      (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N₀ p)
      (P : PlaceSpecialization A p N₀ data hKr (ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
      (W : Finset (Place (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀))) (_ : ∀ w, w ∈ W ↔ w ∈ ssPlaces p N₀ (ResidueField ↥A))

      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P0.1 =
              (uκ ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 = P.reduceFst (𝔓.Meta.pointEquivPlace y))
      (_ : ∀ (y : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
          (u : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p))
          (_ : barPt A ≫ u.1 = y.1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p))
          (uκ : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) (algebraMap (R p) (ResidueField ↥A)))
          (_ : uκ ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ u.1) (_ : uκ ≫ pullback.snd _ _ = 𝟙 _)
          (_ : P.IsStrictFst (𝔓.Meta.pointEquivPlace y) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace y))
          (P1 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
          (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).base P1.1 =
              (uκ ≫ fibreMap 𝔓.w.hom 𝔓.w_over (algebraMap (R p) (ResidueField ↥A)) ≫ fibreMap0 𝔓.π (algebraMap (R p) (ResidueField ↥A))).base
                (IsLocalRing.closedPoint (ResidueField ↥A)) →
            (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P1 = P.reduceSnd (𝔓.Meta.pointEquivPlace y))

      (x : JZero (N₀ * p))
      (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N₀ * p)))))
      (_ : P.IsGoodDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))))
      (g : ↥(GluingData.admissible (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)))
      (_ : (g : GluingData (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N₀) (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)) =
        P.glueData (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) E)
      (_ : Pic0.mk E = x)
      (s : SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) D.toBase)
      (_ : (pts x).1 = barPt A ≫ s.1)
      (sκ : SchemeHomOver (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) (D.baseChange (ResidueField ↥A)).toBase)
      (_ : sκ.1 ≫ pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)) = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1),
      GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
          (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g) = 0 →
        ∀ i : Fin 2,
          NeronModelInfra.schemeHomOverComp sκ (abq i) =
            ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) (ResidueField ↥A))).one
              (𝟙 (Spec (CommRingCat.of (ResidueField ↥A)))) := by
  haveI : CharP (ResidueField ↥A) p := ValuationSubring.charP_residueField_of_liesOverPrime_def (Fact.out) hA
  letI := instDecidableEqResidueFieldSemistable A
  letI : Algebra (R p) (ResidueField ↥A) := ((IsLocalRing.residue ↥A).comp ρ).toAlgebra
  letI := heckeModuleBar (N₀ * p)
  letI := heckeModuleBar N₀
  intro D hD _hsepD _hsm ε₀ D₀ hD₀ _i1 _i2 _i3 _i4 hDκ hPκ hD₀κ hP₀κ hε₁' abq habq0 habq1
    hDQ hPQ _iSep ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj
    pts hpts_add _hgal hpts_aj data hKr hα hβ P W hW hGC1 hGC2 x E hE g hg hx s hs sκ hsκ h0 i
  classical

  let Mκ := hDκ.poincare.pullbackAlong sκ
  have hMκ : (algEquivZeroCut (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (sectionBaseChange (ResidueField ↥A) 𝔓.εinf)).P (𝟙 _) Mκ :=
    (algEquivZeroCut _ _).pullback_mem _ _ sκ _ hDκ.poincare_mem
  have hsκ_cls : sκ = hDκ.classify (𝟙 _) Mκ hMκ := hDκ.classify_unique (𝟙 _) Mκ hMκ sκ ⟨Iso.refl _⟩

  let P' := hD.poincare.pullbackAlong ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩
  let sbar : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) D.toBase :=
    postComp ⟨pullback.fst D.toBase (specMap (R p) (ResidueField ↥A)), pullback.condition⟩ (BaseChange.overR (ResidueField ↥A) sκ)
  have hsbar : sbar.1 = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ s.1 := hsκ
  have KEYISO : Nonempty (Mκ.L ≅ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) (hD.poincare.pullbackAlong sbar)).L) := by
    refine ⟨?_⟩
    refine (Scheme.Modules.pullback (baseChangeSnd (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) sκ)).mapIso hPκ.some ≪≫ ?_
    refine (BaseChange.ofR_toR_iso (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) ((BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) P').pullbackAlong sκ)).symm ≪≫ ?_
    refine (Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).mapIso ?_
    refine (BaseChange.toR_pullbackAlong_iso (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) sκ (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) P')).symm ≪≫ ?_
    refine (Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) (BaseChange.overR (ResidueField ↥A) sκ))).mapIso
      (BaseChange.toR_ofR_iso (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) P') ≪≫ ?_
    exact RigidifiedLineBundle.pullbackAlongPullbackAlongIso' hD.poincare _ (BaseChange.overR (ResidueField ↥A) sκ)

  have hone_val : ((((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) (ResidueField ↥A))).one
        (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))))) : SchemeHomOver (𝟙 _) (D₀.baseChange (ResidueField ↥A)).toBase) =
      ⟨(D₀.baseChange (ResidueField ↥A)).zeroSection, (D₀.baseChange (ResidueField ↥A)).zeroSection_toBase⟩ := by
    apply Subtype.ext
    rw [RelativeGroupLaw.baseChange_one, RelativeGroupLaw.baseChangePointOfBase_coe]
    show _ = (D₀.baseChange (ResidueField ↥A)).zeroSection
    rw [RelativePic0Designation.baseChange_zeroSection]
    have h1 := (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).one_natural (𝟙 _)
      (𝟙 (Spec (CommRingCat.of (ResidueField ↥A))) ≫ specMap (R p) (ResidueField ↥A)) (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Category.comp_id _)
    have h2 : ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).one (𝟙 _ ≫ specMap (R p) (ResidueField ↥A))).1 =
        specMap (R p) (ResidueField ↥A) ≫ D₀.zeroSection := by
      rw [← h1, GoodReductionJacobian.schemeHomOverComp_coe, RepresentsRelSubPic.relativeGroupLaw_one, Category.id_comp]
    apply pullback.hom_ext
    · rw [pullback.lift_fst, pullback.lift_fst, h2]
    · rw [pullback.lift_snd, pullback.lift_snd]
  have hone_unit : Nonempty ((hD₀κ.poincare.pullbackAlong
      (((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut _ _) hD₀).baseChange (specMap (R p) (ResidueField ↥A))).one (𝟙 _))).L ≅
      (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by
    rw [hone_val]; exact hD₀κ.zero

  let N := hD.poincare.pullbackAlong sbar

  let ψred : SchemeHomOver (𝟙 _ ≫ specMap (R p) (ResidueField ↥A)) (Spec.map (CommRingCat.ofHom ρ)) :=
    ⟨Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)), by
      rw [Category.id_comp]
      show Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρ) =
        Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A)))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]⟩
  have hsbar' : sbar = GoodReductionJacobian.schemeHomOverComp ψred.1 ψred.2 s := Subtype.ext hsbar

  haveI : IsProper (toBase N₀ p) := 𝔓.isProper

  have ENUM : ∃ (n : ℕ) (qq : Fin n → {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ 𝔓.Meta.C // q ≫ 𝔓.Meta.toBase = 𝟙 _})
      (pos neg : Fin n → ℕ),
      (∑ i, ((pos i : ℤ) - (neg i : ℤ))) = 0 ∧
      ((E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p))) =
        ∑ i, Finsupp.single (𝔓.Meta.pointEquivPlace (qq i)) ((pos i : ℤ) - (neg i : ℤ))) ∧
      (∀ i, P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i)) ∨ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i))) := by
    haveI := M3Sol.isCurveOver_bar (N₀ * p)
    set Ed : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p)) := (E : Divisor (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N₀ * p))) with hEd
    let supp := Ed.support
    let e : Fin supp.card ≃ ↥supp := supp.equivFin.symm
    have h1 : ∀ w, (((Ed w).toNat : ℕ) : ℤ) - (((-(Ed w)).toNat : ℕ) : ℤ) = Ed w := fun w => Int.toNat_sub_toNat_neg _
    refine ⟨supp.card, fun i => (𝔓.Meta.pointEquivPlace).symm (e i).1, fun i => (Ed (e i).1).toNat,
      fun i => (-(Ed (e i).1)).toNat, ?_, ?_, ?_⟩
    · simp_rw [h1]
      rw [Equiv.sum_comp e (fun w : ↥supp => Ed w.1), Finset.sum_coe_sort supp (fun w => Ed w)]
      have hE0 : Divisor.degree Ed = 0 := E.2
      rw [← hE0, Divisor.degree, Finsupp.liftAddHom_apply, Finsupp.sum]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [AddMonoidHom.mulRight_apply, IsCurveOver.deg_eq_one_of_isAlgClosed w, Nat.cast_one, mul_one]
    · simp_rw [Equiv.apply_symm_apply, h1]
      rw [Equiv.sum_comp e (fun w : ↥supp => Finsupp.single w.1 (Ed w.1)),
        Finset.sum_coe_sort supp (fun w => Finsupp.single w (Ed w))]
      exact (Finsupp.sum_single Ed).symm
    · intro i
      rw [Equiv.apply_symm_apply]
      exact hE (e i).1 (e i).2
  obtain ⟨n, qq, pos, neg, hn, hDx, hstrict⟩ := ENUM

  have SEC := fun i => ModularCurve.DRModelPackageLevel.existsUnique_section_comp_eq_pointEquivPlace_symm N₀ p hpN₀ 𝔓 A ρ hρ
    (𝔓.Meta.pointEquivPlace (qq i))
  let ss : Fin n → SchemeHomOver (Spec.map (CommRingCat.ofHom ρ)) (toBase N₀ p) := fun i => (SEC i).exists.choose
  have hqs : ∀ i, (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) =
      Spec.map (CommRingCat.ofHom A.subtype) ≫ (ss i).1 := by
    intro i
    have h := (SEC i).exists.choose_spec
    have e : ((𝔓.Meta.pointEquivPlace).symm (𝔓.Meta.pointEquivPlace (qq i))).1 ≫ 𝔓.eeta ≫
        pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (AlgebraicClosure ℚ)))) =
        (qq i).1 ≫ 𝔓.eeta ≫ pullback.fst (toBase N₀ p) (genPt p) := by
      rw [Equiv.symm_apply_apply]
    exact (h.trans e).symm

  have LAB : ∃ (c : Fin n → Fin 2)
      (y : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ)))
      (z : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A)))),
      (∀ i, y i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1) ∧
      (∀ i, y i ≫ pullback.snd _ _ = 𝟙 _) ∧
      (∀ i, Set.range (y i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (c i)).base) ∧
      (∀ i, z i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _) ∧
      (∀ i, z i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (c i) = y i) ∧
      (∀ i, (y i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉
        Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - c i)).base) ∧
      (∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((z i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ =
          if c i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ∧
      (∀ i, (c i = 0 ↔ P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i))) ∧ (c i = 1 ↔ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i)))) := by

    have hexcl : ∀ W, P.IsStrictFst W → P.IsStrictSnd W → False := fun W hF hS => hF.2 (by rw [hF.1, ← hS.1])

    let yy : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ fibre (N₀ := N₀) ((IsLocalRing.residue ↥A).comp ρ)) :=
      fun i => DRLevel.sectionFibreOver ρ (ss i)
    have hyy₁ : ∀ i, yy i ≫ pullback.fst _ _ = Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1 :=
      fun i => pullback.lift_fst _ _ _
    have hyy₂ : ∀ i, yy i ≫ pullback.snd _ _ = 𝟙 _ := fun i => pullback.lift_snd _ _ _

    have key : ∀ i, ∃ (ci : Fin 2) (P0 : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C),
        (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ≫
            𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ci).base P0.1 =
          (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∧
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint P0 =
          (if ci = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))) ∧
        (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) ∉
          Set.range (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (1 - ci)).base ∧
        ((ci = 0 ↔ P.IsStrictFst (𝔓.Meta.pointEquivPlace (qq i))) ∧ (ci = 1 ↔ P.IsStrictSnd (𝔓.Meta.pointEquivPlace (qq i)))) := by
      intro i
      rcases hstrict i with hF | hS
      · obtain ⟨⟨P0, hP0, hpl⟩, hn⟩ := ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceFst_of_isStrictFst
          N₀ p hpN₀ 𝔓 A hA ρ hρ (ResidueField ↥A) (IsLocalRing.residue ↥A) data hKr hα hβ P hGC1 hGC2
          (qq i) hF (ss i) (hqs i).symm (yy i) (hyy₁ i) (hyy₂ i)
        refine ⟨0, P0, hP0, by rw [if_pos rfl]; exact hpl, by rw [sub_zero]; exact hn,
          ⟨fun _ => hF, fun _ => rfl⟩, ⟨fun h => absurd h (by decide), fun hS' => (hexcl _ hF hS').elim⟩⟩
      · obtain ⟨⟨P1, hP1, hpl⟩, hn⟩ := ModularCurve.DRModelPackageLevel.exists_placeOfPoint_eq_reduceSnd_of_isStrictSnd
          N₀ p hpN₀ 𝔓 A hA ρ hρ (ResidueField ↥A) (IsLocalRing.residue ↥A) data hKr hα hβ P hGC1 hGC2
          (qq i) hS (ss i) (hqs i).symm (yy i) (hyy₁ i) (hyy₂ i)
        refine ⟨1, P1, hP1, by rw [if_neg (by decide)]; exact hpl, by rw [sub_self]; exact hn,
          ⟨fun h => absurd h (by decide), fun hF' => (hexcl _ hF' hS).elim⟩, ⟨fun _ => hS, fun _ => rfl⟩⟩
    choose cc PP hPP hpl hnn hciff using key

    let q0 : Fin n → {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C //
        q ≫ (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase = 𝟙 _} :=
      fun i => (pointEquivClosedPoint (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase).symm (PP i)
    have hq0 : ∀ i, (q0 i).1.base (IsLocalRing.closedPoint (ResidueField ↥A)) = (PP i).1 := fun i => by
      have e := pointEquivClosedPoint_apply_coe (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).toBase (q0 i)
      rw [Equiv.apply_symm_apply] at e
      exact e.symm
    let zz : Fin n → (Spec (CommRingCat.of (ResidueField ↥A)) ⟶ pullback (toBase0 N₀ p) (specMap (R p) (ResidueField ↥A))) :=
      fun i => (q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))
    have hzz : ∀ i, zz i ≫ baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A) = 𝟙 _ := fun i => by
      show ((q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))) ≫ pullback.snd _ _ = 𝟙 _
      rw [Category.assoc, 𝔓.hefib, (q0 i).2]
    have hzzpt : ∀ i, (zz i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (cc i)).base
        (IsLocalRing.closedPoint (ResidueField ↥A)) = (yy i).base (IsLocalRing.closedPoint (ResidueField ↥A)) := fun i => by
      rw [← hPP i, ← hq0 i]
      rfl

    have hlab : ∀ i, zz i ≫ 𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) (cc i) = yy i := fun i => by
      refine M3Sol.ext_of_section_of_apply_eq (pullback.snd _ _) _ _ ?_ (hyy₂ i) (hzzpt i)
      rw [Category.assoc, 𝔓.comp_over]
      exact hzz i
    have hcr : ∀ i, Set.range (yy i).base ⊆
        Set.range (𝔓.comp (ResidueField ↥A) ((IsLocalRing.residue ↥A).comp ρ) (cc i)).base := fun i => by
      rintro _ ⟨pt, rfl⟩
      obtain rfl : pt = IsLocalRing.closedPoint (ResidueField ↥A) := Subsingleton.elim _ _
      exact ⟨(zz i).base (IsLocalRing.closedPoint (ResidueField ↥A)), hzzpt i⟩

    have hww : ∀ i, ∃ h : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((zz i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈
          closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C,
        (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).placeOfPoint ⟨_, h⟩ =
          if cc i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i)) := fun i => by
      have e : (inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base
          ((zz i).base (IsLocalRing.closedPoint (ResidueField ↥A))) = (PP i).1 := by
        show ((q0 i).1 ≫ 𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) ≫
          inv (𝔓.efib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)))).base _ = _
        rw [IsIso.hom_inv_id, Category.comp_id]
        exact hq0 i
      refine ⟨e ▸ (PP i).2, ?_⟩
      have hs : (⟨_, e ▸ (PP i).2⟩ : closedPoints (𝔓.Mfib (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A))).C) = PP i :=
        Subtype.ext e
      rw [hs]
      exact hpl i
    exact ⟨cc, yy, zz, hyy₁, hyy₂, hcr, hzz, hlab, hnn, hww, hciff⟩
  obtain ⟨c, y, z, hy₁, hy₂, hc, hz, hzy, hnot, hw, hciff⟩ := LAB
  let w : Fin n → Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀) := fun i =>
    if c i = 0 then P.reduceFst (𝔓.Meta.pointEquivPlace (qq i)) else P.reduceSnd (𝔓.Meta.pointEquivPlace (qq i))

  have hG0 : ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 0), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) := by
    rw [show ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).1 =
        Finsupp.mapDomain P.reduceFst (P.fstDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))) from
      congrArg Prod.fst hg, PlaceSpecialization.fstDiv, hDx, Finsupp.filter_sum, Finsupp.mapDomain_finsetSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hci : c i = 0
    · rw [Finsupp.filter_single_of_pos _ ((hciff i).1.mp hci), Finsupp.mapDomain_single, if_pos hci]
      simp only [w, if_pos hci]
    · rw [Finsupp.filter_single_of_neg _ (fun h => hci ((hciff i).1.mpr h)), Finsupp.mapDomain_zero, if_neg hci]
  have hG1 : ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1 =
        ∑ i ∈ Finset.univ.filter (fun i => c i = 1), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) := by
    rw [show ((g : GluingData (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)
        (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W))).2.1 =
        Finsupp.mapDomain P.reduceSnd (P.sndDiv (E : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N₀ * p)))) from
      congrArg (fun t => t.2.1) hg, PlaceSpecialization.sndDiv, hDx, Finsupp.filter_sum, Finsupp.mapDomain_finsetSum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hci : c i = 1
    · have hci0 : ¬ c i = 0 := by rw [hci]; decide
      rw [Finsupp.filter_single_of_pos _ ((hciff i).2.mp hci), Finsupp.mapDomain_single, if_pos hci]
      simp only [w, if_neg hci0]
    · rw [Finsupp.filter_single_of_neg _ (fun h => hci ((hciff i).2.mpr h)), Finsupp.mapDomain_zero, if_neg hci]
  have hadm := (GluingData.mem_admissible (S := nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)).1 g.2

  have hdeg : ∀ j : Fin 2, (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
    haveI := ModularCurve.isCurveOver_modularFunctionFieldC_of_perfectField (ResidueField ↥A) N₀
    have hd1 : ∀ v : Place (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀), v.deg = 1 :=
      fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
    have key : ∀ (j : Fin 2) (Dv : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)),
        Dv ∈ Divisor.degZero (K := ResidueField ↥A) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) →
        Dv = ∑ i ∈ Finset.univ.filter (fun i => c i = j), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ)) →
        (∑ i ∈ Finset.univ.filter (fun i => c i = j), ((pos i : ℤ) - (neg i : ℤ))) = 0 := by
      intro j Dv hDv hsum
      rw [Divisor.mem_degZero, hsum, map_sum] at hDv
      simp_rw [Divisor.degree_single, hd1, Nat.cast_one, mul_one] at hDv
      exact hDv
    intro j
    have hj : j = 0 ∨ j = 1 := by rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;> simp [h]
    rcases hj with rfl | rfl
    · exact key 0 _ hadm.1 hG0
    · exact key 1 _ hadm.2.1 hG1

  have PRINC : ∀ j : Fin 2,
      ((j = 0 ∧ (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
          (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g)).1 = 0) ∨
       (j = 1 ∧ (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
          (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g)).2 = 0)) →
      ∃ (Dz : ↥(Divisor.degZero (K := ResidueField ↥A) (F := ↥(modularFunctionFieldC (ResidueField ↥A) N₀)))),
        ((Dz : Divisor (ResidueField ↥A) ↥(modularFunctionFieldC (ResidueField ↥A) N₀)) =
          ∑ i ∈ Finset.univ.filter (fun i => c i = j), Finsupp.single (w i) ((pos i : ℤ) - (neg i : ℤ))) ∧
        Pic0.mk Dz = 0 := by
    intro j hj
    rcases hj with ⟨rfl, hj0⟩ | ⟨rfl, hj1⟩
    · exact ⟨⟨_, hadm.1⟩, hG0, hj0⟩
    · exact ⟨⟨_, hadm.2.1⟩, hG1, hj1⟩

  have hsmS : ∀ i, Set.range (ss i).1.base ⊆ (𝔓.smoothLocus : Set (X N₀ p)) := by
    intro i
    have hpt : (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base
        ((y i).base (IsLocalRing.closedPoint (ResidueField ↥A))) ∈ (𝔓.smoothLocus : Set (X N₀ p)) := by
      refine _hsm _ fun ⟨h0, h1⟩ => ?_
      have hi : c i = 0 ∨ c i = 1 := by
        rcases Fin.exists_fin_two.mp ⟨c i, rfl⟩ with h | h <;> simp [h]
      rcases hi with hci | hci
      · exact hnot i (by rw [hci]; exact h1)
      · exact hnot i (by rw [hci]; exact h0)
    have hcl : (ss i).1.base (IsLocalRing.closedPoint ↥A) ∈ (𝔓.smoothLocus : Set (X N₀ p)) := by
      have e : (pullback.fst (toBase N₀ p) (Spec.map (CommRingCat.ofHom (algebraMap (R p) (ResidueField ↥A))))).base
          ((y i).base (IsLocalRing.closedPoint (ResidueField ↥A))) =
          (ss i).1.base ((Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A))) := by
        show ((y i) ≫ pullback.fst _ _).base _ = (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A)) ≫ (ss i).1).base _
        rw [hy₁ i]
      have e2 : (Spec.map (CommRingCat.ofHom (IsLocalRing.residue ↥A))).base (IsLocalRing.closedPoint (ResidueField ↥A)) =
          IsLocalRing.closedPoint ↥A := IsLocalRing.comap_closedPoint (IsLocalRing.residue ↥A)
      rw [e, e2] at hpt
      exact hpt
    rintro _ ⟨𝔭, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint 𝔭).map (ss i).1.base.hom.continuous).mem_open 𝔓.smoothLocus.isOpen hcl

  obtain ⟨a, ha⟩ := ModularCurve.DRModelPackageLevel.exists_schemeHomOver_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_sum_eq_zero
      N₀ p hpN₀ 𝔓 D hD A hA ρ hρ ss hsmS c y hy₁ hy₂ hc pos neg hdeg

  have hgen := ModularCurve.DRModelPackageLevel.pts_pic0Mk_eq_comp_of_poincare_pullbackAlong_iso_rigidify_sectionTwist_of_range_subset_smoothLocus
      N₀ p hpN₀ 𝔓 D hD hDQ hPQ ajQ hajQε hajQ kQ hkQ₁ hkQ₂ ajbar hajbar hajbar_over εbar hεbar hεbar_aj pts hpts_add _hgal hpts_aj
      A ρ hρ ss hsmS qq hqs pos neg hn E hDx a ha

  have hsa : s = a := by
    apply Subtype.ext
    have h1 : barPt A ≫ s.1 = barPt A ≫ a.1 := by
      rw [← hs, ← hx, hgen]
    haveI : IsDominant (barPt A) := by
      rw [isDominant_iff]
      change DenseRange (PrimeSpectrum.comap (A.subtype : ↥A →+* AlgebraicClosure ℚ))
      refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mpr ?_
      rw [(RingHom.injective_iff_ker_eq_bot _).mp (fun x y h => Subtype.ext h)]
      exact bot_le
    exact ext_of_isDominant_of_isSeparated D.toBase (s.2.trans a.2.symm) (barPt A) h1

  have G34 : Nonempty (N.L ≅ ((hD.poincare.pullbackAlong a).pullbackAlong ψred).L) := by
    refine ⟨?_ ≪≫ (hD.poincare.pullbackAlongPullbackAlongIso' a ψred).symm⟩
    show (hD.poincare.pullbackAlong sbar).L ≅ (hD.poincare.pullbackAlong (postComp a ψred)).L
    rw [hsbar', hsa]
    rfl

  let SWmod : (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules :=
    (List.finRange n).foldr
      (fun i M => ((RelEffCartierDiv.ofPoint (toBase N₀ p) (ss i).1 (ss i).2).I ^ (pos i)).invModule ⊗
        ((RelEffCartierDiv.ofPoint (toBase N₀ p) (ss i).1 (ss i).2).I ^ (neg i)).module ⊗ M)
      (𝟙_ (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules)
  let SW : (pullback (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))).Modules :=
    Scheme.Modules.rigidify (rigSection (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ)) 𝔓.εinf)
      (pullback.snd (toBase N₀ p) (Spec.map (CommRingCat.ofHom ρ))) SWmod

  let SWκ : (pullback (baseChange (R p) (toBase N₀ p) (ResidueField ↥A)) (𝟙 _)).Modules :=
    (Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).obj
      ((Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).obj SW)

  let LB : Fin 2 → (pullback (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)).Modules := fun j =>
    (List.finRange n).foldr
      (fun i M => if c i = j then
        ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (pos i)).invModule ⊗
          ((RelEffCartierDiv.ofPoint (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (z i) (hz i)).I ^ (neg i)).module ⊗ M
        else M)
      (𝟙_ _)

  have G7₀ : Nonempty ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
      (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝟙 _))).obj SWκ ≅ LB 0) := by
    exact ModularCurve.DRModelPackageLevel.nonempty_pullbackCurve_comp0_sectionTwist_iso N₀ p hpN₀ 𝔓 A hA ρ hρ
      ss hsmS c y hy₁ hy₂ z hz hzy hnot ψred rfl pos neg
  have G7₁ : Nonempty (Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)
        (sectionBaseChange (ResidueField ↥A) ε₀)) (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _))
      ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1)
        (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝟙 _))).obj SWκ) ≅
      Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)
        (sectionBaseChange (ResidueField ↥A) ε₀)) (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) (LB 1)) := by
    exact ModularCurve.DRModelPackageLevel.nonempty_rigidify_pullbackCurve_comp1_sectionTwist_iso N₀ p hpN₀ 𝔓 A hA ρ hρ
      ε₀ ss hsmS c y hy₁ hy₂ z hz hzy hnot ψred rfl pos neg

  have G8₀ : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
        (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g)).1 = 0 →
      Nonempty (LB 0 ≅ (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
        (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by
    intro h00
    obtain ⟨Dz, hDz, hDz0⟩ := PRINC 0 (Or.inl ⟨rfl, h00⟩)
    exact ModularCurve.DRModelPackageLevel.nonempty_pointTwist_comp0_iso_unit_of_pic0Mk_eq_zero N₀ p hpN₀ 𝔓 A hA ρ hρ
      ε₀ c z hz w hw pos neg Dz hDz hDz0
  have G8₁ : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W)
        (GluedPic0.mk (nodePairsOfPlaces (arithFrobC p (ResidueField ↥A) N₀) W) g)).2 = 0 →
      Nonempty (Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)
        (sectionBaseChange (ResidueField ↥A) ε₀)) (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _)) (LB 1) ≅
        (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A))
          (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) := by
    intro h01
    obtain ⟨Dz, hDz, hDz0⟩ := PRINC 1 (Or.inr ⟨rfl, h01⟩)
    exact ModularCurve.DRModelPackageLevel.nonempty_rigidify_pointTwist_comp1_iso_unit_of_pic0Mk_eq_zero N₀ p hpN₀ 𝔓 A hA ρ hρ
      ε₀ c z hz w hw pos neg Dz hDz hDz0

  have hNSW : Nonempty ((BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) N).L ≅ SWκ) :=
    ⟨(Scheme.Modules.pullback (BaseChange.κ (toBase N₀ p) (ResidueField ↥A) (𝟙 _)).hom).mapIso
      (G34.some ≪≫ (Scheme.Modules.pullback (baseChangeSnd (toBase N₀ p) ψred)).mapIso ha.some)⟩
  have G7G8₀ : Nonempty (((BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) N).pullbackCurve
        (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁').L ≅
      (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) :=
    ⟨(Scheme.Modules.pullback _).mapIso hNSW.some ≪≫ G7₀.some ≪≫ (G8₀ (congrArg Prod.fst h0)).some⟩
  have G7G8₁ : Nonempty (Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
        (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _))
        ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝟙 _))).obj
          (BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) N).L) ≅
      (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) :=
    ⟨Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso hNSW.some) ≪≫ G7₁.some ≪≫
      (G8₁ (congrArg Prod.snd h0)).some⟩

  have TRIV₀ : Nonempty ((Mκ.pullbackCurve (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁').L ≅
      (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) :=
    ⟨(RigidifiedLineBundle.pullbackCurve_congr (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁'
      (M := Mκ) (M' := BaseChange.ofR (toBase N₀ p) 𝔓.εinf (ResidueField ↥A) N) KEYISO).some ≪≫ G7G8₀.some⟩
  have TRIV₁ : Nonempty (Scheme.Modules.rigidify (rigSection (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _) (sectionBaseChange (ResidueField ↥A) ε₀))
        (pullback.snd (baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (𝟙 _))
        ((Scheme.Modules.pullback (curveChange (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 1) (𝟙 _))).obj Mκ.L) ≅
      (RigidifiedLineBundle.unit (c := baseChange (R p) (toBase0 N₀ p) (ResidueField ↥A)) (ε := sectionBaseChange (ResidueField ↥A) ε₀) (𝟙 _)).L) :=
    ⟨Scheme.Modules.rigidifyMapIso _ _ ((Scheme.Modules.pullback _).mapIso KEYISO.some) ≪≫ G7G8₁.some⟩

  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  ·
    have hcomp : NeronModelInfra.schemeHomOverComp sκ (abq 0) =
        hD₀κ.classify (𝟙 _) (Mκ.pullbackCurve (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁')
          (FibrewiseAlgEquivZero.pullbackCurve (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁' hMκ) := by
      refine (congrArg (NeronModelInfra.schemeHomOverComp · (abq 0)) hsκ_cls).trans ?_
      rw [M3Sol.schemeHomOverComp_eq_postComp, habq0]
      exact RepresentsRelSubPic.postComp_pullbackHom_classify (𝔓.comp (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0)
        (𝔓.comp_over (ResidueField ↥A) (algebraMap (R p) (ResidueField ↥A)) 0) hε₁' hDκ hD₀κ (𝟙 _) Mκ hMκ
    apply hD₀κ.ext_of_iso (𝟙 _)
    rw [hcomp]
    exact ⟨(hD₀κ.classify_spec (𝟙 _) _ _).some ≪≫ TRIV₀.some ≪≫ hone_unit.some.symm⟩
  ·
    apply hD₀κ.ext_of_iso (𝟙 _)
    exact ⟨(habq1 (𝟙 _) sκ).some ≪≫ TRIV₁.some ≪≫ hone_unit.some.symm⟩

#print axioms solution

end S_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField
end P2MW
export P2MW.S_ModularCurve_DRModelPackageLevel_abq_reduction_eq_one_of_toPic0Pair_glueData_eq_zero_residueField (solution)
