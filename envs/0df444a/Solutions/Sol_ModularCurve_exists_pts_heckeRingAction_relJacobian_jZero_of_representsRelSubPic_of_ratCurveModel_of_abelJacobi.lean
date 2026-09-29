-- Prove2me | solution 1 for ModularCurve.exists_pts_heckeRingAction_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel_of_abelJacobi
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0c0e4c68-f2ad-5367-97b5-5fc4e94d0562

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_ReductionOfPointsAgreesModL
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModel
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_ModularCurve_isCurveOver_laurentBaseChange_modularFunctionFieldFull
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_IsPlaceReductionModL_coordinate_clauses
import Theorems.Thm_ModularCurve_transcendental_coeffEmb_jq
import Theorems.Thm_P2M_Dup_ModularCurve_transcendental_jqNModC
import Theorems.Thm_ModularCurve_ord_cuspInftyBar
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_ModularCurve_AtkinLehner
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroGroupCut
import Definitions.Def_AlgebraicGeometry_RelSubPicGroup
import Definitions.Def_SheafOfModules_Monoidal
import Definitions.Def_AlgebraicGeometry_IdealSheafModule
import Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import Definitions.Def_AlgebraicGeometry_RelEffCartierDivOfPoint
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_abelJacobi_of_representsRelSubPic
import Theorems.Thm_AlgebraicGeometry_RelPicard_exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
import Theorems.Thm_ModularCurve_exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_AlgebraicGeometry_RelPicard_schemeHomOver_ext_of_forall_algebraicClosure_point
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_pts_heckeRingAction_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel_of_abelJacobi
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite"
p2m_attr_erase "instance" "ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper PresheafOfModules.ExteriorPower.instModulePresheafAb AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instNeg AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulInt AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAddCommGroup AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instAdd AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSub AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instModuleCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulCarrierObjOppositeOpensCarrierCarrierCommRingCatPresheafOpOpensTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instSMulNat"
p2m_attr_erase "instance" "AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.instZero AlgebraicGeometry.SmoothOfRelativeDimension.fiberToSpecResidueField AlgebraicGeometry.SmoothOfRelativeDimension.pullback_snd AlgebraicGeometry.SmoothOfRelativeDimension.pullback_fst AlgebraicGeometry.SmoothOfRelativeDimension.smooth_one AlgebraicGeometry.SmoothProperCurve.isIntegral_pullback_Spec_field AlgebraicGeometry.IsProper.fiberToSpecResidueField SheafOfModules.isIso_ihomModelToIhom AlgebraicGeometry.RelEffCartierDiv.subsingleton_of_degree_zero AlgebraicGeometry.OModulePresheaf.isScalarTower AlgebraicGeometry.Scheme.OrderedAffineCover.instLinearOrder AlgebraicGeometry.OModulePresheaf.module AlgebraicGeometry.Scheme.OrderedAffineCover.instFintype AlgebraicGeometry.Scheme.OrderedAffineCover.instFintypeIdx AlgebraicGeometry.OModulePresheaf.addCommGroup AlgebraicGeometry.Scheme.OrderedAffineCover.instDecidableEqIdx AlgebraicGeometry.OModulePresheaf.moduleSections AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instDecidableEqIdx AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintype AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instLinearOrder AlgebraicGeometry.Scheme.OrderedAffineCoverOf.instFintypeIdx AlgebraicGeometry.OModulePresheaf.instSubsingletonObjZero AlgebraicGeometry.OModulePresheaf.Leray.relAltC_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_modΓ AlgebraicGeometry.OModulePresheaf.Leray.relAltC_modΓ AlgebraicGeometry.OModulePresheaf.Leray.biC_abGrp AlgebraicGeometry.OModulePresheaf.Leray.relAltH_modΓ AlgebraicGeometry.OModulePresheaf.Leray.ker_relAltd_smul AlgebraicGeometry.OModulePresheaf.Leray.relAltH_scalarTower AlgebraicGeometry.OModulePresheaf.Leray.relAltH_smul AlgebraicGeometry.OModulePresheaf.Leray.biC_module DoubleComplex.instModuleE₂I DoubleComplex.Bounded.modR DoubleComplex.instModuleE₂II DoubleComplex.instAddCommGroupE₂II DoubleComplex.Bounded.abGrp DoubleComplex.instAddCommGroupE₂I AlgebraicGeometry.ChowDatum.hι_closed AlgebraicGeometry.ChowDatumProj.hιN_closed AlgebraicGeometry.ChowDatumProj.hp_proper"
p2m_attr_erase "instance" "AlgebraicGeometry.ChowDatum.hp_isoU AlgebraicGeometry.ChowDatum.hp_proper AlgebraicGeometry.ProjSpace.algebraAway AlgebraicGeometry.ProjSpace.instIsProperProdOverπ AlgebraicGeometry.ChowDatumProj.hp_isoU AlgebraicGeometry.ProjSpace.isProper_π AlgebraicGeometry.ProjSpace.finiteType_mvPolynomial ProjSpaceCech.GradedModule.H.module ProjSpaceCech.GradedModule.H.addCommGroup ProjSpaceCech.GradedModule.sec.instAdd ProjSpaceCech.GradedModule.sec.instNeg ProjSpaceCech.GradedModule.acg ProjSpaceCech.GradedModule.Frac.setoid ProjSpaceCech.GradedModule.modR ProjSpaceCech.GradedModule.sec.instModule ProjSpaceCech.GradedModule.sec.instAddCommGroup ProjSpaceCech.GradedModule.sec.instZero ProjSpaceCech.GradedModule.Presentation.fJ ProjSpaceCech.GradedModule.sec.instSMul ProjSpaceCech.Twist.H.module ProjSpaceCech.Idx.instFintype ProjSpaceCech.Twist.H.addCommGroup ProjSpaceCech.Idx.instDecidableEq ProjSpaceCech.Twist.Mon.instDecidableEq ProjSpaceCech.Twist.cochain.instAddCommGroup ProjSpaceCech.Twist.cochain.instModule AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X"
p2m_attr_erase "simp" "ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.eisensteinNumerator_nineteen"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_cuspidalDivisor₀ ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL"
p2m_attr_erase "simp" "HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.coe_jGeomGen ModularCurve.coe_jNGeomGen ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring ModularCurve.charLGeomModuliDictionary_single ModularCurve.specializeModuli_single ModularCurve.specializePlace_def AlgebraicGeometry.RelPicard.thetaBundle_def AlgebraicGeometry.RelPicard.picardBundle_def AlgebraicGeometry.Scheme.Modules.exteriorPower_obj PresheafOfModules.exteriorPower_map_ιMulti PresheafOfModules.ExteriorPower.appₗ_apply AlgebraicGeometry.RelPicard.fst_toProdSpec AlgebraicGeometry.RelPicard.toProdSpec_fst_assoc"
p2m_attr_erase "simp" "AlgebraicGeometry.RelPicard.pointsSubBasepointModule_cons AlgebraicGeometry.RelPicard.pointsSubBasepointModule_nil AlgebraicGeometry.RelPicard.fst_toProdSpec_assoc AlgebraicGeometry.RelPicard.toProdSpec_fst AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.sub_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sresTop AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.add_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.sizeOf_spec AlgebraicGeometry.Scheme.IdealSheafData.coe_resLE AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.smul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_ofLE_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.ideal_range AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zero_app AlgebraicGeometry.Scheme.IdealSheafData.sres_sres AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.comp_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.neg_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.id_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.coe_mulRight_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.nsmul_app AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.mk.injEq AlgebraicGeometry.Scheme.IdealSheafData.IdealHom.zsmul_app AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_snd AlgebraicGeometry.SmoothProperCurve.sectionBaseChange_coe_fst AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_hom_app_coe AlgebraicGeometry.RelPicard.BaseChange.relSubPicPresheafRestrictIso_inv_app_coe AlgebraicGeometry.RelPicard.BaseChange.restrict_P AlgebraicGeometry.Scheme.Modules.toUnitSection_ofUnitSection AlgebraicGeometry.Scheme.Modules.pullbackSection_def AlgebraicGeometry.Scheme.Modules.ofUnitSection_toUnitSection AlgebraicCurve.coe_cechH0Equiv_apply AlgebraicCurve.cechH1ToH1_mk AlgebraicCurve.lSpaceOn_univ AlgebraicCurve.lSpaceOn_empty AlgebraicGeometry.Scheme.Modules.tensorPow_zero AlgebraicGeometry.Scheme.Modules.tensorPow_succ AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right AlgebraicGeometry.Scheme.Modules.map_unitSection AlgebraicGeometry.Scheme.Modules.tensorSectionsBilin_apply AlgebraicGeometry.Scheme.Modules.tensorPowSection_zero AlgebraicGeometry.Scheme.Modules.tensorSections_zero_left"
p2m_attr_erase "simp" "PresheafOfModules.InternalHom.IsSheafAux.appAt_toPresheafHom SheafOfModules.ihomSectionsEquivFamily_unit AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_apply SheafOfModules.ihomEval_unit_app AlgebraicGeometry.Scheme.Modules.ihomEval_zero_right AlgebraicGeometry.Scheme.Modules.ihomEval_zero_left AlgebraicGeometry.Scheme.Modules.homOfFamily_app_apply SheafOfModules.unit_ihomSectionsEquivFamily AlgebraicGeometry.Scheme.Modules.familyOfHom_app AlgebraicGeometry.Scheme.Modules.restrictUnitIso_hom_app_apply AlgebraicGeometry.Scheme.Modules.restrictUnitIso_inv_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomOfFamily_app_apply AlgebraicGeometry.Scheme.Modules.restrictHomEquivFamily_symm_apply AlgebraicGeometry.prodKerGraph_one AlgebraicGeometry.fibrePowOver.proj_comp AlgebraicGeometry.prodKerGraph_zero AlgebraicGeometry.RelEffCartierDiv.empty_I AlgebraicGeometry.fibrePowOver.proj_comp_assoc AlgebraicCurve.SymmetricPowerPackage.mk.sizeOf_spec AlgebraicCurve.SymmetricPowerPackage.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.mk.injEq AlgebraicGeometry.OModulePresheaf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.mk.injEq AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_neg AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_zero AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_sub AlgebraicGeometry.Scheme.Modules.pullbackLocalSection_add AlgebraicGeometry.Scheme.OrderedAffineCover.toCoverOf_U AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCoverOf.mk.injEq AlgebraicGeometry.Scheme.OrderedAffineCover.restrict_U AlgebraicGeometry.OModulePresheaf.Hom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.id_app AlgebraicGeometry.OModulePresheaf.AffHom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffHom.comp_app AlgebraicGeometry.OModulePresheaf.AffSES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.kerMap_coe AlgebraicGeometry.OModulePresheaf.AffHom.id_app AlgebraicGeometry.OModulePresheaf.Hom.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicGeometry.OModulePresheaf.Hom.toAffHom_app AlgebraicGeometry.OModulePresheaf.SES.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.AffHom.mk.sizeOf_spec AlgebraicGeometry.OModulePresheaf.Hom.comp_app AlgebraicGeometry.OModulePresheaf.SES.mk.injEq AlgebraicGeometry.OModulePresheaf.AffHom.mk.injEq AlgebraicGeometry.OModulePresheaf.Hom.appSections_apply AlgebraicGeometry.OModulePresheaf.AffSES.mk.injEq AlgebraicGeometry.OModulePresheaf.prod_obj AlgebraicGeometry.OModulePresheaf.restrOpen_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.injEq AlgebraicGeometry.OModulePresheaf.pushforward_obj AlgebraicGeometry.OModulePresheaf.im_obj AlgebraicGeometry.OModulePresheaf.pow_obj AlgebraicGeometry.OModulePresheaf.fstHom_app AlgebraicGeometry.OModulePresheaf.ker_obj AlgebraicGeometry.OModulePresheaf.coker_obj AlgebraicGeometry.OModulePresheaf.DevissageStep.mk.sizeOf_spec AlgebraicGeometry.Scheme.OrderedAffineCover.preimage_U AlgebraicGeometry.OModulePresheaf.sndHom_app AlgebraicGeometry.OModulePresheaf.Leray.restrictToPreimage_U DoubleComplex.Bounded.mk.injEq DoubleComplex.Bounded.mk.sizeOf_spec DoubleComplex.Convergence.mk.injEq DoubleComplex.Convergence.mk.sizeOf_spec DoubleComplex.SubQuot.mk.sizeOf_spec DoubleComplex.SubQuot.mk.injEq AlgebraicGeometry.ChowDatumProj.mk.sizeOf_spec AlgebraicGeometry.ChowDatum.mk.sizeOf_spec AlgebraicGeometry.ChowDatumProj.mk.injEq AlgebraicGeometry.ChowDatum.mk.injEq ProjSpaceCech.GradedModule.mk.injEq ProjSpaceCech.GradedModule.mk.sizeOf_spec ProjSpaceCech.GradedModule.Frac.mk.sizeOf_spec ProjSpaceCech.GradedModule.Presentation.mk.injEq ProjSpaceCech.GradedModule.Frac.mk.injEq ProjSpaceCech.GradedModule.Presentation.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.shift_toLinearMap ProjSpaceCech.GradedModule.Hom.mk.sizeOf_spec ProjSpaceCech.GradedModule.Hom.mk.injEq"
p2m_attr_erase "simp" "TwoChartCech.Mumford.dK_apply TwoChartCech.Mumford.ι0_apply TwoChartCech.Mumford.ι1_apply TwoChartCech.KerCoprod.dK_apply TwoChartCech.KerCoprod.ι1_apply TwoChartCech.KerCoprod.ι0_apply AlgebraicGeometry.tilde.functorCompPullbackSpecIso_app AlgebraicGeometry.RelPicard.rigSection_snd AlgebraicGeometry.RelPicard.RigidifiedLineBundle.ofInvertible_L AlgebraicGeometry.RelPicard.rigSection_snd_assoc AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc AlgebraicGeometry.Scheme.Modules.normModuleFunctor_obj PresheafOfModules.pushforwardCongr_inv_app_app_apply PresheafOfModules.pushforwardNatTrans_app_app_apply PresheafOfModules.pushforwardCongr_hom_app_app_apply RegularLocalRingQuotientAscent.dualNumberFst_apply ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing"

set_option autoImplicit false

p2m_open "CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra GoodReductionJacobian ModularCurve AlgebraicCurve IsLocalRing"

namespace B2Glue

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem mul_val_congr (L : RelativeGroupLaw R f) {T : Scheme.{0}} {t₁ t₂ : T ⟶ Spec (CommRingCat.of R)}
    (h : t₁ = t₂) (x₁ y₁ : SchemeHomOver t₁ f) (x₂ y₂ : SchemeHomOver t₂ f)
    (hx : x₁.1 = x₂.1) (hy : y₁.1 = y₂.1) : (L.mul t₁ x₁ y₁).1 = (L.mul t₂ x₂ y₂).1 := by
  subst h
  have hx' : x₁ = x₂ := Subtype.ext hx
  have hy' : y₁ = y₂ := Subtype.ext hy
  subst hx'; subst hy'; rfl

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem inv_natural (L : RelativeGroupLaw R f) {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  have h1 : L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  calc GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)
      = L.mul t' (L.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (L.inv t x)) (GoodReductionJacobian.schemeHomOverComp ψ hψ x))
          (L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x)) := by
        rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
    _ = L.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by rw [h1, L.one_mul]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pts_neg (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {G : Type} [AddCommGroup G] (pts : G → SchemeHomOver t f)
    (hadd : ∀ u v : G, pts (u + v) = L.mul t (pts u) (pts v)) (h0 : pts 0 = L.one t) (u : G) :
    pts (-u) = L.inv t (pts u) := by
  have h1 : L.mul t (pts (-u)) (pts u) = L.one t := by rw [← hadd, neg_add_cancel, h0]
  calc pts (-u) = L.mul t (L.mul t (pts (-u)) (pts u)) (L.inv t (pts u)) := by
        rw [L.mul_assoc, L.mul_inv_cancel, L.mul_one]
    _ = L.inv t (pts u) := by rw [h1, L.one_mul]

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem pts_zero' (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {G : Type} [AddCommGroup G] (pts : G → SchemeHomOver t f)
    (hadd : ∀ u v : G, pts (u + v) = L.mul t (pts u) (pts v)) : pts 0 = L.one t := by
  have h1 := hadd 0 0
  rw [add_zero] at h1
  have := congrArg (fun z => L.mul t (L.inv t (pts 0)) z) h1
  beta_reduce at this
  rwa [L.inv_mul_cancel, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul, eq_comm] at this

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem pic0_closure_eq_top {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [IsCurveOver K F]
    (w₀ : Place K F) (Δ : Place K F → Divisor.degZero (K := K) (F := F))
    (hΔ : ∀ v, (Δ v : Divisor K F) = Finsupp.single v 1 - Finsupp.single w₀ 1) :
    AddSubgroup.closure (Set.range fun v => Pic0.mk (Δ v)) = ⊤ := by
  have hdeg1 : ∀ v : Place K F, v.deg = 1 := fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  rw [eq_top_iff]
  rintro y -
  obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
  have hdegD : Divisor.degree (D : Divisor K F) = 0 := D.2
  have hdec : (D : Divisor K F) = (D : Divisor K F).sum (fun v n => n • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1)) := by
    have hsum1 : (D : Divisor K F).sum (fun v n => n • Finsupp.single v (1 : ℤ)) = D := by
      conv_rhs => rw [← Finsupp.sum_single (D : Divisor K F)]
      apply Finsupp.sum_congr
      intro v _
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    have hsum2 : (D : Divisor K F).sum (fun v n => n • Finsupp.single w₀ (1 : ℤ)) = 0 := by
      simp only [Finsupp.sum, ← Finset.sum_smul]
      have : (∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v) = Divisor.degree (D : Divisor K F) := by
        conv_rhs => rw [← Finsupp.sum_single (D : Divisor K F), map_finsuppSum]
        simp only [Finsupp.sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
      rw [this, hdegD, zero_smul]
    simp only [smul_sub, Finsupp.sum_sub, hsum1, hsum2, sub_zero]
  let mkHom : Divisor.degZero (K := K) (F := F) →+ Pic0 K F :=
    { toFun := Pic0.mk, map_zero' := Pic0.mk_zero, map_add' := Pic0.mk_add }
  have hD' : D = ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v • Δ v := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finset_sum]
    simp only [AddSubgroupClass.coe_zsmul, hΔ]
    simpa only [Finsupp.sum] using hdec
  have hmk : Pic0.mk D = ∑ v ∈ (D : Divisor K F).support, (D : Divisor K F) v • Pic0.mk (Δ v) := by
    show mkHom D = ∑ v ∈ _, _ • mkHom (Δ v)
    conv_lhs => rw [hD']
    rw [map_sum]
    simp only [map_zsmul]
  rw [hmk]
  exact AddSubgroup.sum_mem _ fun v _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self v)) _

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem gal_equivariance (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))} (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (aj : SchemeHomOver c f) [IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    (pts : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar p) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f)
    (hadd : ∀ x y, pts (x + y) = L.mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 →
      ∃ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk D)).1 = x.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ aj.1)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p) :
    (pts (σ • x)).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1 := by
  have hσfix : Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    show σ (algebraMap _ (AlgebraicClosure ℚ) r) = algebraMap _ (AlgebraicClosure ℚ) r
    have hr : algebraMap (GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ) r =
        algebraMap ℚ (AlgebraicClosure ℚ) (r : ℚ) := rfl
    rw [hr]; exact σ.commutes (r : ℚ)

  have hinvη : inv eη ≫ Mη.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, heη]
  let toM : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun y => ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]) ≫ inv eη, by
      rw [Category.assoc, hinvη, pullback.lift_snd]⟩
  have htoM : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c) {Z : Scheme.{0}} (k : X ⟶ Z),
      (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ k = y.1 ≫ k := by
    intro y Z k
    show (pullback.lift y.1 (𝟙 _) _ ≫ inv eη) ≫ eη ≫ pullback.fst c _ ≫ k = y.1 ≫ k
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  have htoM₀ : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c), (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = y.1 := by
    intro y
    simpa only [Category.comp_id] using htoM y (𝟙 X)

  let sη : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c := ⟨(Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let tw : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c := fun y =>
    ⟨Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ y.1, by rw [Category.assoc, y.2, hσfix]⟩
  have htw_s : tw sη = sη := Subtype.ext (by
    show Spec.map _ ≫ (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1
    rw [← Category.assoc, hσfix])
  have hplace_tw : ∀ y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c,
      Mη.pointEquivPlace (toM (tw y)) =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) σ •
          Mη.pointEquivPlace (toM y) := by
    intro y
    apply hgal σ (toM y) (toM (tw y))
    rw [htoM₀, htoM₀]
  let ofPlace : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c :=
    fun v => ⟨(Mη.pointEquivPlace.symm v).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc,
        (Mη.pointEquivPlace.symm v).2, Category.id_comp]⟩
  have hplace_ofPlace : ∀ v, Mη.pointEquivPlace (toM (ofPlace v)) = v := by
    intro v
    have key : (toM (ofPlace v)).1 ≫ eη = (Mη.pointEquivPlace.symm v).1 ≫ eη := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]; exact htoM₀ (ofPlace v)
      · simp only [Category.assoc, heη, (Mη.pointEquivPlace.symm v).2]
        exact (toM (ofPlace v)).2
    have : toM (ofPlace v) = Mη.pointEquivPlace.symm v :=
      Subtype.ext (by simpa using congrArg (· ≫ inv eη) key)
    rw [this, Equiv.apply_symm_apply]

  set g := arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) σ with hg
  let w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) := Mη.pointEquivPlace (toM sη)
  have hs_cond : (toM sη).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 := htoM₀ sη
  have hw₀ : g • w₀ = w₀ := by
    have := hplace_tw sη
    rw [htw_s] at this
    exact this.symm
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p), v.deg = 1 :=
    fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v

  have hΔmem : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
      Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1 ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) := by
    intro v
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    simp
  let Δ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) :=
    fun v => ⟨_, hΔmem v⟩

  have hgen : ∀ v, (pts (σ • Pic0.mk (Δ v))).1 = Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts (Pic0.mk (Δ v))).1 := by
    intro v
    obtain ⟨D₁, hD₁, hpts₁⟩ := hnorm (toM (ofPlace v)) (toM sη) hs_cond
    rw [hplace_ofPlace] at hD₁
    obtain ⟨D₂, hD₂, hpts₂⟩ := hnorm (toM (tw (ofPlace v))) (toM sη) hs_cond
    rw [hplace_tw, hplace_ofPlace] at hD₂
    have hΔ1 : Δ v = D₁ := Subtype.ext hD₁.symm
    have hsmul : σ • Pic0.mk (Δ v) = Pic0.mk D₂ := by
      rw [galois_smul_pic0_def, SemilinearAut.pic0_smul_mk]
      congr 1
      apply Subtype.ext
      rw [SemilinearAut.coe_degZeroSMulHom, hD₂, ← hg]
      show g • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1) = _
      rw [smul_sub, SemilinearAut.smul_single, SemilinearAut.smul_single, hw₀]
    rw [hsmul, hpts₂, hΔ1, hpts₁, htoM, htoM]
    rfl

  letI := L.pointGroup (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))
  have hmul_def : ∀ a b : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f, a * b = L.mul _ a b := fun _ _ => rfl
  let Φ₁ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (pts (σ • y))) (by
      intro a b
      apply Additive.toMul.injective
      show pts (σ • (a + b)) = pts (σ • a) * pts (σ • b)
      rw [smul_add, hadd, hmul_def])
  let Φ₂ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f) :=
    AddMonoidHom.mk' (fun y => Additive.ofMul (GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ))) hσfix (pts y))) (by
      intro a b
      apply Additive.toMul.injective
      show GoodReductionJacobian.schemeHomOverComp _ hσfix (pts (a + b)) =
        GoodReductionJacobian.schemeHomOverComp _ hσfix (pts a) * GoodReductionJacobian.schemeHomOverComp _ hσfix (pts b)
      rw [hadd, L.mul_natural, hmul_def])
  suffices hΦ : Φ₁ = Φ₂ by
    have := congrArg (fun Φ : JZero p →+ Additive (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f) => (Additive.toMul (Φ x)).1) hΦ
    exact this

  have hclos : AddSubgroup.closure (Set.range fun v => Pic0.mk (Δ v)) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨D, rfl⟩ := Pic0.mk_surjective y
    have hdegD : Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) = 0 := D.2

    have hdec : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1)) := by
      have hsum1 : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • Finsupp.single v (1 : ℤ)) = D := by
        conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p))]
        apply Finsupp.sum_congr
        intro v _
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      have hsum2 : (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).sum
          (fun v n => n • Finsupp.single w₀ (1 : ℤ)) = 0 := by
        simp only [Finsupp.sum, ← Finset.sum_smul]
        have : (∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
            (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v) =
            Divisor.degree (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) := by
          conv_rhs => rw [← Finsupp.sum_single (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)), map_finsuppSum]
          simp only [Finsupp.sum, Divisor.degree_single, hdeg1, Nat.cast_one, mul_one]
        rw [this, hdegD, zero_smul]
      simp only [smul_sub, Finsupp.sum_sub, hsum1, hsum2, sub_zero]
    let mkHom : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) →+ JZero p :=
      { toFun := Pic0.mk, map_zero' := Pic0.mk_zero, map_add' := Pic0.mk_add }
    have hD' : D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v • Δ v := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finset_sum]
      simp only [AddSubgroupClass.coe_zsmul]
      simpa only [Finsupp.sum] using hdec
    have hmk : Pic0.mk D = ∑ v ∈ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)).support,
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) v • Pic0.mk (Δ v) := by
      show mkHom D = ∑ v ∈ _, _ • mkHom (Δ v)
      conv_lhs => rw [hD']
      rw [map_sum]
      simp only [map_zsmul]
    rw [hmk]
    exact AddSubgroup.sum_mem _ fun v _ => AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self v)) _
  apply AddMonoidHom.eq_of_eqOn_dense hclos
  rintro _ ⟨v, rfl⟩
  apply Additive.toMul.injective
  apply Subtype.ext
  exact hgen v

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem r_eq_placeReductionModL (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    [IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar N)]
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) →
      Place (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) N))
    (hr : IsPlaceReductionModL A N r) (hinp : ReductionInputsModL A N) :
    r = placeReductionModL hinp := by
  have hr₀ := isPlaceReductionModL_placeReductionModL hinp

  let jF : modularFunctionFieldBar N :=
    ⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (L := AlgebraicClosure ℚ) (hx := jq_mem_full N)⟩
  have hyeq : coeffMap A.subtype (jqModC ↥A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    show (jqModC ↥A).map A.subtype = (coeffMap (algebraMap ℚ (AlgebraicClosure ℚ))) jq
    rw [map_jqModC, ← jqModC_rat]
    show _ = (jqModC ℚ).map (algebraMap ℚ (AlgebraicClosure ℚ))
    rw [map_jqModC]
  have hy : coeffMap A.subtype (jqModC ↥A) ∈ modularFunctionFieldBar N := by
    rw [hyeq]; exact jF.2
  have hykeq : coeffMap (residue ↥A) (jqModC ↥A) = jqModC (ResidueField ↥A) := by
    show (jqModC ↥A).map (residue ↥A) = _
    rw [map_jqModC]
  have hyk : coeffMap (residue ↥A) (jqModC ↥A) ∈ modularFunctionFieldFullC (ResidueField ↥A) N := by
    rw [hykeq]; exact jqModC_mem_full (ResidueField ↥A) N
  have hy0 : coeffMap (residue ↥A) (jqModC ↥A) ≠ 0 := by
    rw [hykeq]
    intro h0
    have ht := ModularCurve.transcendental_jqNModC (ResidueField ↥A) 1
    rw [jqNModC_one, h0] at ht
    exact ht (isAlgebraic_zero)
  have hjF0 : jF ≠ 0 := by
    intro h0
    have ht := ModularCurve.transcendental_coeffEmb_jq (AlgebraicClosure ℚ) N
    have : (⟨coeffEmb (AlgebraicClosure ℚ) jq, coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) = 0 := h0
    rw [this] at ht
    exact ht (isAlgebraic_zero)
  have hPD : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional N
  obtain ⟨D, hD, hDdeg⟩ := hPD.exists_divisor jF hjF0
  apply IsPlaceReductionAlong.eq_of_agree (A := A) (π := residue ↥A) (N := N) hinp.choose_spec.2
  · rintro D' ⟨y, hy', hyk', hy0', hD'⟩
    ext Q
    rw [hr.2 y hy' hyk' hy0' D' hD' Q, hr₀.2 y hy' hyk' hy0' D' hD' Q]
  · exact fun P => IsCurveOver.deg_eq_one_of_isAlgClosed P
  · rintro D' ⟨g, hg, hDg⟩
    obtain ⟨D'', hD'', hdeg''⟩ := hPD.exists_divisor g hg
    have : D' = D'' := Finsupp.ext fun v => by rw [hDg v, hD'' v]
    rw [this]; exact hdeg''
  · exact JZero.divisible N
  ·
    refine ⟨D, ⟨jF, hjF0, hD⟩, ?_⟩
    have hcl := (ModularCurve.IsPlaceReductionModL.coordinate_clauses N ℓ hℓN A hA r hr).2.1 (cuspInftyBar N) ?_
    · intro hzero
      have hval := hr.2 (jqModC ↥A) hy hyk hy0 D (fun P => by
        rw [hD P]; congr 1; exact Subtype.ext hyeq.symm) (r (cuspInftyBar N))
      rw [hzero, Finsupp.zero_apply] at hval
      have : (r (cuspInftyBar N)).ord (⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
          modularFunctionFieldFullC (ResidueField ↥A) N) =
          (r (cuspInftyBar N)).ord ⟨coeffMap (residue ↥A) (jqModC ↥A), hyk⟩ := by
        congr 1; exact Subtype.ext hykeq.symm
      omega
    · intro a
      rw [ord_cuspInftyBar]
      change (coeffEmb (AlgebraicClosure ℚ) jq -
        algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)).order ≤ 0
      have hc : (coeffEmb (AlgebraicClosure ℚ) jq -
          algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) (a : AlgebraicClosure ℚ)).coeff (-1) ≠ 0 := by
        rw [HahnSeries.coeff_sub', Pi.sub_apply, coeffEmb_coeff, coeff_jq_neg_one, map_one,
          algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num)]
        norm_num
      have := HahnSeries.order_le_of_coeff_ne_zero hc
      omega

set_option maxHeartbeats 12800000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem sp_agreement (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime]
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)
    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (A : ValuationSubring (AlgebraicClosure ℚ)) [IsAlgClosed (ResidueField ↥A)]
    (ρA : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A) (hρA : A.subtype.comp ρA = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : CurveModel (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : Ms.C ⟶ pullback c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA)))) [IsIso es]
    (hes : es ≫ pullback.snd c _ = Ms.toBase)
    (r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
      Place (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p))
    (hr : IsPlaceReductionModL A p r)
    (hpt : ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρA)) c)
      (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
      (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _}),
      x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
      y.1 ≫ es ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
      Ms.pointEquivPlace y = r (Mη.pointEquivPlace x))
    (hinp : ReductionInputsModL A p)
    {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))} (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (aj : SchemeHomOver c f) [IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p)]
    [IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p)]
    (pts : Pic0 (AlgebraicClosure ℚ) (modularFunctionFieldBar p) ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f)
    (hadd : ∀ x y, pts (x + y) = L.mul _ (pts x) (pts y))
    (hnorm : ∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      s.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 →
      ∃ D : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
        (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
          Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
        (pts (Pic0.mk D)).1 = x.1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ aj.1)
    (ptsκ : JZeroC (ResidueField ↥A) p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) f)
    (haddκ : ∀ x y, ptsκ (x + y) = L.mul _ (ptsκ x) (ptsκ y))
    (hnormκ : ∀ (x s : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _}),
      s.1 ≫ es ≫ pullback.fst c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) = (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ ε.1 →
      ∃ D : Divisor.degZero (K := ResidueField ↥A) (F := ↥(modularFunctionFieldFullC (ResidueField ↥A) p)),
        (D : Divisor (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p)) =
          Finsupp.single (Ms.pointEquivPlace x) 1 - Finsupp.single (Ms.pointEquivPlace s) 1 ∧
        (ptsκ (Pic0.mk D)).1 = x.1 ≫ es ≫ pullback.fst c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ aj.1)
    (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρA)) f)
    (hptsA : ∀ x, ptsA x = GoodReductionJacobian.schemeHomOverComp (𝟙 _)
      (by rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hρA]) (pts x))
    (ptsSp : JZeroC (ResidueField ↥A) p ≃
      SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρA)) f)
    (hptsSp : ∀ u, ptsSp u = GoodReductionJacobian.schemeHomOverComp (𝟙 _)
      (by rw [Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) (ptsκ u))
    (hrr : r = placeReductionModL hinp) :
    ReductionOfPointsAgreesModL p A f (Spec.map (CommRingCat.ofHom ρA)) ptsA ptsSp := by
  have hsqA : (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρA) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρA]
  have hsq : (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρA) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

  have hAadd : ∀ x y, ptsA (x + y) = L.mul _ (ptsA x) (ptsA y) := by
    intro x y; rw [hptsA, hptsA, hptsA, hadd, L.mul_natural]
  have hSadd : ∀ u v, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v) := by
    intro u v; rw [hptsSp, hptsSp, hptsSp, haddκ, L.mul_natural]
  have hA0 := pts_zero' L _ ptsA hAadd
  have hS0 := pts_zero' L _ ptsSp hSadd

  let S : AddSubgroup (JZero p) :=
    { carrier := {x | ∃ xA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρA)) f,
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom A.subtype)) rfl xA = ptsA x ∧
        GoodReductionJacobian.schemeHomOverComp (Spec.map (CommRingCat.ofHom (residue ↥A))) rfl xA =
          ptsSp (reductionModL A p x)}
      zero_mem' := ⟨L.one _, by rw [L.one_natural, hA0], by rw [L.one_natural, map_zero, hS0]⟩
      add_mem' := by
        rintro x y ⟨xA, hx1, hx2⟩ ⟨yA, hy1, hy2⟩
        exact ⟨L.mul _ xA yA, by rw [L.mul_natural, hx1, hy1, hAadd],
          by rw [L.mul_natural, hx2, hy2, map_add, hSadd]⟩
      neg_mem' := by
        rintro x ⟨xA, hx1, hx2⟩
        exact ⟨L.inv _ xA, by rw [inv_natural, hx1, pts_neg L _ ptsA hAadd hA0],
          by rw [inv_natural, hx2, map_neg, pts_neg L _ ptsSp hSadd hS0]⟩ }
  suffices hS : S = ⊤ by
    intro x
    have hx : x ∈ S := by rw [hS]; trivial
    exact hx

  have hinvη : inv eη ≫ Mη.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) := by
    rw [IsIso.inv_comp_eq, heη]
  let toM : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c →
      {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _} :=
    fun y => ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]) ≫ inv eη, by
      rw [Category.assoc, hinvη, pullback.lift_snd]⟩
  have htoM : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c) {Z : Scheme.{0}} (k : X ⟶ Z),
      (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ k = y.1 ≫ k := by
    intro y Z k
    show (pullback.lift y.1 (𝟙 _) _ ≫ inv eη) ≫ eη ≫ pullback.fst c _ ≫ k = y.1 ≫ k
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  have htoM₀ : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c), (toM y).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = y.1 := by
    intro y
    simpa only [Category.comp_id] using htoM y (𝟙 X)
  let sη : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c := ⟨(Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let ofPlace : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) → SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) c :=
    fun v => ⟨(Mη.pointEquivPlace.symm v).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))), by
      rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc eη, heη, ← Category.assoc,
        (Mη.pointEquivPlace.symm v).2, Category.id_comp]⟩
  have hplace_ofPlace : ∀ v, Mη.pointEquivPlace (toM (ofPlace v)) = v := by
    intro v
    have key : (toM (ofPlace v)).1 ≫ eη = (Mη.pointEquivPlace.symm v).1 ≫ eη := by
      apply pullback.hom_ext
      · rw [Category.assoc, Category.assoc]; exact htoM₀ (ofPlace v)
      · simp only [Category.assoc, heη, (Mη.pointEquivPlace.symm v).2]
        exact (toM (ofPlace v)).2
    have : toM (ofPlace v) = Mη.pointEquivPlace.symm v :=
      Subtype.ext (by simpa using congrArg (· ≫ inv eη) key)
    rw [this, Equiv.apply_symm_apply]

  have hinvs : inv es ≫ Ms.toBase = pullback.snd c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) := by
    rw [IsIso.inv_comp_eq, hes]
  let toMs : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) c →
      {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ Ms.C // q ≫ Ms.toBase = 𝟙 _} :=
    fun y => ⟨pullback.lift y.1 (𝟙 _) (by rw [y.2, Category.id_comp]) ≫ inv es, by
      rw [Category.assoc, hinvs, pullback.lift_snd]⟩
  have htoMs : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) c) {Z : Scheme.{0}} (k : X ⟶ Z),
      (toMs y).1 ≫ es ≫ pullback.fst c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ k = y.1 ≫ k := by
    intro y Z k
    show (pullback.lift y.1 (𝟙 _) _ ≫ inv es) ≫ es ≫ pullback.fst c _ ≫ k = y.1 ≫ k
    rw [Category.assoc, IsIso.inv_hom_id_assoc, pullback.lift_fst_assoc]
  have htoMs₀ : ∀ (y : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) c), (toMs y).1 ≫ es ≫ pullback.fst c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) = y.1 := by
    intro y
    simpa only [Category.comp_id] using htoMs y (𝟙 X)

  let w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) := Mη.pointEquivPlace (toM sη)
  have hs_cond : (toM sη).1 ≫ eη ≫ pullback.fst c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) = (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 := htoM₀ sη
  have hdeg1 : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p), v.deg = 1 :=
    fun v => IsCurveOver.deg_eq_one_of_isAlgClosed v
  have hΔmem : ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
      Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1 ∈
        Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) := by
    intro v
    rw [Divisor.mem_degZero, map_sub, Divisor.degree_single, Divisor.degree_single, hdeg1, hdeg1]
    simp
  let Δ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
      Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p) := fun v => ⟨_, hΔmem v⟩

  have hex : ValuativeCriterion.Existence c := by
    have h := (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed c) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) c)
    exact h.1

  let sA : SchemeHomOver (Spec.map (CommRingCat.ofHom ρA)) c :=
    ⟨Spec.map (CommRingCat.ofHom ρA) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  let sκX : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) c := ⟨(Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ ε.1, by rw [Category.assoc, ε.2, Category.comp_id]⟩
  have hsκ_cond : (toMs sκX).1 ≫ es ≫ pullback.fst c (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) = (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ ε.1 := htoMs₀ sκX
  have hw₀r : Ms.pointEquivPlace (toMs sκX) = r w₀ := by
    apply hpt sA (toM sη) (toMs sκX)
    · rw [htoM₀]
      show (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) ≫ ε.1 = Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom ρA) ≫ ε.1
      rw [← Category.assoc, ← hsqA]
    · rw [htoMs₀]
      show (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) ≫ ε.1 = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom ρA) ≫ ε.1
      rw [← Category.assoc, ← hsq]
  have hgen : ∀ v, Pic0.mk (Δ v) ∈ S := by
    intro v

    have hcomm : CommSq (ofPlace v).1 (Spec.map (CommRingCat.ofHom (algebraMap ↥A (AlgebraicClosure ℚ)))) c
        (Spec.map (CommRingCat.ofHom ρA)) := ⟨by
      rw [(ofPlace v).2, hsqA]; rfl⟩
    have hlift := hex (ValuativeCommSq.mk ↥A (AlgebraicClosure ℚ) (ofPlace v).1 (Spec.map (CommRingCat.ofHom ρA)) hcomm)
    let xt : SchemeHomOver (Spec.map (CommRingCat.ofHom ρA)) c := ⟨hcomm.lift, hcomm.fac_right⟩
    have hxt : Spec.map (CommRingCat.ofHom A.subtype) ≫ xt.1 = (ofPlace v).1 := hcomm.fac_left
    refine ⟨⟨xt.1 ≫ aj.1, by rw [Category.assoc, aj.2]; exact xt.2⟩, ?_, ?_⟩
    ·
      apply Subtype.ext
      show Spec.map (CommRingCat.ofHom A.subtype) ≫ xt.1 ≫ aj.1 = (ptsA (Pic0.mk (Δ v))).1
      rw [hptsA]
      show _ = 𝟙 _ ≫ (pts (Pic0.mk (Δ v))).1
      obtain ⟨D₁, hD₁, hpts₁⟩ := hnorm (toM (ofPlace v)) (toM sη) hs_cond
      rw [hplace_ofPlace] at hD₁
      have hΔ1 : Δ v = D₁ := Subtype.ext hD₁.symm
      rw [Category.id_comp, hΔ1, hpts₁, htoM, ← hxt, Category.assoc]
    ·
      apply Subtype.ext
      show Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xt.1 ≫ aj.1 = (ptsSp (reductionModL A p (Pic0.mk (Δ v)))).1
      rw [hptsSp]
      show _ = 𝟙 _ ≫ (ptsκ (reductionModL A p (Pic0.mk (Δ v)))).1
      rw [Category.id_comp, reductionModL_mk hinp]
      let yX : SchemeHomOver (Spec.map (CommRingCat.ofHom ((residue ↥A).comp ρA))) c := ⟨Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xt.1, by
        rw [Category.assoc, xt.2, ← hsq]⟩
      obtain ⟨D', hD', hpts'⟩ := hnormκ (toMs yX) (toMs sκX) hsκ_cond
      have hy : Ms.pointEquivPlace (toMs yX) = r v := by
        have := hpt xt (toM (ofPlace v)) (toMs yX) (by rw [htoM₀, hxt]) (by rw [htoMs₀])
        rw [this, hplace_ofPlace]
      have hD'eq : D' = reductionDegZeroAlong (placeReductionModL hinp)
          (isPlaceReductionModL_placeReductionModL hinp).1 (Δ v) := by
        apply Subtype.ext
        rw [hD', coe_reductionDegZeroAlong, hy, hw₀r, hrr]
        show _ = Finsupp.mapDomain _ (Finsupp.single v (1 : ℤ) - Finsupp.single w₀ 1)
        rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
      rw [← hD'eq, hpts', htoMs, Category.assoc]

  rw [eq_top_iff, ← pic0_closure_eq_top w₀ Δ (fun v => rfl)]
  exact (AddSubgroup.closure_le S).mpr (by rintro _ ⟨v, rfl⟩; exact hgen v)

end B2Glue

namespace B2Hecke

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}
  (L : RelativeGroupLaw R f)

def IsHom (φ : SchemeHomOver f f) : Prop :=
  ∀ (T : Scheme.{0}) (s : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver s f),
    NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)

variable {L}

theorem IsHom.apply {φ : SchemeHomOver f f} (h : IsHom L φ) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R))
    (x y : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ) :=
  h T s x y

theorem comp_eq {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s f)
    (φ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x φ = GoodReductionJacobian.schemeHomOverComp x.1 x.2 φ := rfl

private theorem _root_.B2Hecke.comp_mul {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f)
    (φ ψ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x (L.mul f φ ψ) =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp x ψ) := by
  rw [comp_eq, L.mul_natural f s x.1 x.2]
  rfl

p2m_export "B2Hecke" "comp_mul"
private theorem _root_.B2Hecke.comp_one {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp x (L.one f) = L.one s := by
  rw [comp_eq, L.one_natural f s x.1 x.2]

p2m_export "B2Hecke" "comp_one"

noncomputable def evalHom {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f) :
    letI := L.pointGroup f; letI := L.pointGroup s
    SchemeHomOver f f →* SchemeHomOver s f :=
  letI := L.pointGroup f; letI := L.pointGroup s
  { toFun := fun φ => NeronModelInfra.schemeHomOverComp x φ
    map_one' := comp_one s x
    map_mul' := fun φ ψ => comp_mul s x φ ψ }

theorem comp_inv {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f)
    (φ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x (L.inv f φ) = L.inv s (NeronModelInfra.schemeHomOverComp x φ) := by
  letI := L.pointGroup f; letI := L.pointGroup s
  exact map_inv (evalHom (L := L) s x) φ

theorem comp_zpow {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver s f)
    (φ : SchemeHomOver f f) (n : ℤ) :
    letI := L.pointGroup f; letI := L.pointGroup s
    NeronModelInfra.schemeHomOverComp x (φ ^ n) = (NeronModelInfra.schemeHomOverComp x φ) ^ n := by
  letI := L.pointGroup f; letI := L.pointGroup s
  exact map_zpow (evalHom (L := L) s x) φ n

def idE (f : J ⟶ Spec (CommRingCat.of R)) : SchemeHomOver f f := ⟨𝟙 J, Category.id_comp f⟩

theorem comp_idE {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp x (idE f) = x :=
  Subtype.ext (Category.comp_id _)

theorem isHom_idE : IsHom L (idE f) := by
  intro T s x y
  rw [comp_idE, comp_idE, comp_idE]

theorem isHom_one : IsHom L (L.one f) := by
  intro T s x y
  rw [comp_one, comp_one, comp_one, L.one_mul]

theorem isHom_mul (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {φ ψ : SchemeHomOver f f} (hφ : IsHom L φ) (hψ : IsHom L ψ) : IsHom L (L.mul f φ ψ) := by
  intro T s x y
  rw [comp_mul, comp_mul, comp_mul, hφ, hψ]
  letI := L.pointGroup s
  show (NeronModelInfra.schemeHomOverComp x φ * NeronModelInfra.schemeHomOverComp y φ) *
      (NeronModelInfra.schemeHomOverComp x ψ * NeronModelInfra.schemeHomOverComp y ψ) =
    (NeronModelInfra.schemeHomOverComp x φ * NeronModelInfra.schemeHomOverComp x ψ) *
      (NeronModelInfra.schemeHomOverComp y φ * NeronModelInfra.schemeHomOverComp y ψ)
  have hc : ∀ a b : SchemeHomOver s f, a * b = b * a := fun a b => hC s a b
  rw [mul_assoc, mul_assoc, ← mul_assoc (NeronModelInfra.schemeHomOverComp y φ),
    hc (NeronModelInfra.schemeHomOverComp y φ), mul_assoc]

theorem isHom_inv (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {φ : SchemeHomOver f f} (hφ : IsHom L φ) : IsHom L (L.inv f φ) := by
  intro T s x y
  rw [comp_inv, comp_inv, comp_inv, hφ]
  letI := L.pointGroup s
  show (NeronModelInfra.schemeHomOverComp x φ * NeronModelInfra.schemeHomOverComp y φ)⁻¹ =
    (NeronModelInfra.schemeHomOverComp x φ)⁻¹ * (NeronModelInfra.schemeHomOverComp y φ)⁻¹
  rw [mul_inv_rev]
  exact hC s _ _

theorem isHom_comp {φ ψ : SchemeHomOver f f} (hφ : IsHom L φ) (hψ : IsHom L ψ) :
    IsHom L (NeronModelInfra.schemeHomOverComp φ ψ) := by
  intro T s x y
  have hassoc : ∀ z : SchemeHomOver s f, NeronModelInfra.schemeHomOverComp z (NeronModelInfra.schemeHomOverComp φ ψ) =
      NeronModelInfra.schemeHomOverComp (NeronModelInfra.schemeHomOverComp z φ) ψ :=
    fun z => Subtype.ext (Category.assoc _ _ _).symm
  rw [hassoc, hassoc, hassoc, hφ, hψ]

theorem isHom_zpow (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {φ : SchemeHomOver f f} (hφ : IsHom L φ) (n : ℤ) :
    letI := L.pointGroup f
    IsHom L (φ ^ n) := by
  letI := L.pointGroup f
  induction n using Int.induction_on with
  | zero => rw [zpow_zero]; exact isHom_one
  | succ n ih => rw [zpow_add_one]; exact isHom_mul hC ih hφ
  | pred n ih => rw [zpow_sub_one]; exact isHom_mul hC ih (isHom_inv hC hφ)

theorem hecke_closure (p : ℕ) [NeZero p]
    (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    {S : Scheme.{0}} {s : S ⟶ Spec (CommRingCat.of R)} (pts : JZero p → SchemeHomOver s f)
    (hadd : ∀ x y : JZero p, pts (x + y) = L.mul s (pts x) (pts y))
    (hgen : ∀ q : Nat.Primes, ∃ φ : SchemeHomOver f f, IsHom L φ ∧
      ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar p
    ∀ t : HeckeAlg, ∃ φ : SchemeHomOver f f, IsHom L φ ∧ ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by
  letI := heckeModuleBar p
  letI := L.pointGroup f
  letI := L.pointGroup s

  let Φ : JZero p →+ Additive (SchemeHomOver s f) :=
    { toFun := fun x => Additive.ofMul (pts x)
      map_zero' := by
        have h1 := hadd 0 0
        rw [add_zero] at h1
        apply Additive.toMul.injective
        show pts 0 = 1
        have h2 : pts 0 * pts 0 = pts 0 * 1 := by rw [mul_one]; exact h1.symm
        exact mul_left_cancel h2
      map_add' := fun x y => by
        apply Additive.toMul.injective
        exact hadd x y }
  have hΦ : ∀ x, Additive.toMul (Φ x) = pts x := fun x => rfl
  intro t
  induction t using MvPolynomial.induction_on with
  | C a =>
    refine ⟨idE f ^ a, isHom_zpow hC isHom_idE a, fun x => ?_⟩
    have h1 : pts ((MvPolynomial.C a : HeckeAlg) • x) = pts x ^ a := by
      rw [heckeModuleBar_C_smul, ← hΦ, map_zsmul]
      rfl
    rw [h1, ← comp_idE (f := f) (pts x), ← comp_zpow, comp_idE]
    rfl
  | add t₁ t₂ h₁ h₂ =>
    obtain ⟨φ₁, hφ₁, e₁⟩ := h₁
    obtain ⟨φ₂, hφ₂, e₂⟩ := h₂
    refine ⟨L.mul f φ₁ φ₂, isHom_mul hC hφ₁ hφ₂, fun x => ?_⟩
    have h1 : pts ((t₁ + t₂) • x) = L.mul s (pts (t₁ • x)) (pts (t₂ • x)) := by rw [add_smul, hadd]
    have e₁' : pts (t₁ • x) = NeronModelInfra.schemeHomOverComp (pts x) φ₁ := Subtype.ext (e₁ x)
    have e₂' : pts (t₂ • x) = NeronModelInfra.schemeHomOverComp (pts x) φ₂ := Subtype.ext (e₂ x)
    rw [h1, e₁', e₂', ← comp_mul]
    rfl
  | mul_X t q ht =>
    obtain ⟨φ, hφ, e⟩ := ht
    obtain ⟨ψ, hψ, eψ⟩ := hgen q
    refine ⟨NeronModelInfra.schemeHomOverComp ψ φ, isHom_comp hψ hφ, fun x => ?_⟩
    have h1 : (t * MvPolynomial.X q) • x = t • (heckeOperatorBar p q x) := by
      rw [mul_smul]
      congr 1
      exact heckeModuleBar_heckeGen_smul (ModularCurve.heckeOperatorsCommuteBar p) q x
    rw [h1, e, eψ, Category.assoc]
    rfl

end B2Hecke

namespace B2Glue

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem assemble
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)

    (h𝔉 : ∀ m₀ : ℕ, ∃ 𝔉 : SmoothProperCurve.FiniteMapData c ε, m₀ ≤ 𝔉.m ∧ 𝔉.LevelSetsGenericallyEtale)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p),
        IsPlaceReductionModL A p r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (aj : SchemeHomOver c f) (hB : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hPTS : ∀ (K : Type) [Field K] [IsAlgClosed K] (i : ↥(GaloisRep.ratLocalizedAt ℓ) →+* K)
        (F : Type) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) f,
          (∀ x y : Pic0 K F, pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 = x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1)
    (hHG : ∀ q : Nat.Primes, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f),
        (∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)) →
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
          s.1 ≫ eη ≫ pullback.fst c _ =
            Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
              Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1) →
        ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar p
    ∃ (J : Scheme.{0})
      (f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
      (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
      (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) ∧
      (∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) f)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A p → ReductionOfPointsAgreesModL p A f σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg, ∃ φ : SchemeHomOver f f,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
            L.mul s (NeronModelInfra.schemeHomOverComp x φ)
              (NeronModelInfra.schemeHomOverComp y φ)) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1)  := by

  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
    ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) p
  obtain ⟨pts, hadd, hnorm⟩ := hPTS (AlgebraicClosure ℚ) (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (modularFunctionFieldBar p) Mη eη heη
  refine ⟨J, f, L, pts, hB, (fun t x y => hC t x y), hadd, ?_, ?_, ?_⟩
  ·
    intro σ x
    exact B2Glue.gal_equivariance p ℓ c ε Mη eη heη hgal L aj pts hadd hnorm σ x
  ·
    intro A hA
    haveI : IsAlgClosed (ResidueField ↥A) := A.isAlgClosed_residueField_algebraicClosure_rat
    haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) :=
      ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) p
    haveI := hes_iso A hA
    obtain ⟨ptsκ, haddκ, hnormκ⟩ := hPTS (ResidueField ↥A) ((residue ↥A).comp (ρ A hA))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (Ms A hA) (es A hA) (hes A hA)
    have hsq : Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hsqA : Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) =
        Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ A hA]
    have hψ : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [Category.id_comp, hsq]
    have hψ' : 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) =
        Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) := by
      rw [Category.id_comp, hsq]
    let ptsSp : JZeroC (ResidueField ↥A) p ≃
        SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) f :=
      { toFun := fun u => GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u)
        invFun := fun z => ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ' z)
        left_inv := fun u => by
          show ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ'
            (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u))) = u
          apply ptsκ.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp])
        right_inv := fun z => by
          show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ
            (ptsκ (ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ' z))) = z
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp]) }
    have hptsSp : ∀ u, (ptsSp u).1 = (ptsκ u).1 := fun u => Category.id_comp _
    have hψA : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) =
        Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [Category.id_comp, hsqA]
    have hψA' : 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) := by
      rw [Category.id_comp, hsqA]
    let ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) f :=
      { toFun := fun x => GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA (pts x)
        invFun := fun z => pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA' z)
        left_inv := fun x => by
          show pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA'
            (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA (pts x))) = x
          apply pts.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp])
        right_inv := fun z => by
          show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA
            (pts (pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA' z))) = z
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp]) }
    refine ⟨Spec.map (CommRingCat.ofHom (ρ A hA)), ptsA, ptsSp, fun x => Category.id_comp _, ?_, ?_⟩
    · intro u v
      show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ (u + v)) =
        L.mul _ (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u)) (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ v))
      rw [haddκ, L.mul_natural]
    ·
      intro hinp
      obtain ⟨r, hr, hpt⟩ := hsp A hA
      haveI : CharP (ResidueField ↥A) ℓ := A.residueField_charP_of_liesOverPrime Fact.out hA
      have hrr : r = placeReductionModL hinp :=
        B2Glue.r_eq_placeReductionModL p ℓ hℓp A hA r hr hinp
      exact B2Glue.sp_agreement p ℓ c ε Mη eη heη A (ρ A hA) (hρ A hA) (Ms A hA) (es A hA) (hes A hA)
        r hr hpt hinp L aj pts hadd hnorm ptsκ haddκ hnormκ ptsA (fun x => rfl) ptsSp (fun u => rfl) hrr
  ·

    have hgen : ∀ q : Nat.Primes, ∃ φ : SchemeHomOver f f, B2Hecke.IsHom L φ ∧
        ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1 := by
      intro q
      obtain ⟨φ, hφ, hφp⟩ := hHG q
      exact ⟨φ, fun T s x y => hφ s x y, hφp pts hadd hnorm⟩
    intro t
    obtain ⟨φ, hφ, hφx⟩ := B2Hecke.hecke_closure (L := L) p (fun t x y => hC t x y) pts hadd hgen t
    exact ⟨φ, fun s x y => hφ.apply s x y, hφx⟩

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem assembleExport
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p),
        IsPlaceReductionModL A p r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    {J : Scheme.{0}} (f : J ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (L : RelativeGroupLaw ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (aj : SchemeHomOver c f) (hB : AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f)
    (hC : ∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (hPTS : ∀ (K : Type) [Field K] [IsAlgClosed K] (i : ↥(GaloisRep.ratLocalizedAt ℓ) →+* K)
        (F : Type) [Field F] [Algebra K F] [IsCurveOver K F] (M : CurveModel K F)
        (e : M.C ⟶ pullback c (Spec.map (CommRingCat.ofHom i))) [IsIso e],
        e ≫ pullback.snd c (Spec.map (CommRingCat.ofHom i)) = M.toBase →
        ∃ pts : Pic0 K F ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom i)) f,
          (∀ x y : Pic0 K F, pts (x + y) = L.mul (Spec.map (CommRingCat.ofHom i)) (pts x) (pts y)) ∧
          ∀ (x s : {q : Spec (CommRingCat.of K) ⟶ M.C // q ≫ M.toBase = 𝟙 _}),
            s.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) = Spec.map (CommRingCat.ofHom i) ≫ ε.1 →
            ∃ Dv : Divisor.degZero (K := K) (F := F),
              (Dv : Divisor K F) = Finsupp.single (M.pointEquivPlace x) 1 - Finsupp.single (M.pointEquivPlace s) 1 ∧
              (pts (Pic0.mk Dv)).1 = x.1 ≫ e ≫ pullback.fst c (Spec.map (CommRingCat.ofHom i)) ≫ aj.1)
    (hHG : ∀ q : Nat.Primes, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f),
        (∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)) →
        (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
          s.1 ≫ eη ≫ pullback.fst c _ =
            Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
              Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1) →
        ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1) :
    letI := heckeModuleBar p
    ∃ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) f)
      (φ : HeckeAlg → SchemeHomOver f f),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) f ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t f), L.mul t x y = L.mul t y x) ∧
      (∀ x y : JZero p, pts (x + y) = L.mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) f)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) f),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = L.mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A p → ReductionOfPointsAgreesModL p A f σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
          NeronModelInfra.schemeHomOverComp (L.mul s x y) (φ t) =
            L.mul s (NeronModelInfra.schemeHomOverComp x (φ t))
              (NeronModelInfra.schemeHomOverComp y (φ t))) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ (φ t).1) ∧
      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
          s.1 ≫ eη ≫ pullback.fst c _ =
            Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
              Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1) := by
  letI := heckeModuleBar p

  haveI : IsCurveOver (AlgebraicClosure ℚ) (modularFunctionFieldBar p) :=
    ModularCurve.isCurveOver_laurentBaseChange_modularFunctionFieldFull (AlgebraicClosure ℚ) p
  obtain ⟨pts, hadd, hnorm⟩ := hPTS (AlgebraicClosure ℚ) (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (modularFunctionFieldBar p) Mη eη heη

  have hhecke : ∀ t : HeckeAlg, ∃ φ : SchemeHomOver f f,
      (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s f),
        NeronModelInfra.schemeHomOverComp (L.mul s x y) φ =
          L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp y φ)) ∧
      ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ φ.1 := by
    have hgen : ∀ q : Nat.Primes, ∃ φ : SchemeHomOver f f, B2Hecke.IsHom L φ ∧
        ∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ φ.1 := by
      intro q
      obtain ⟨φ, hφ, hφp⟩ := hHG q
      exact ⟨φ, fun T s x y => hφ s x y, hφp pts hadd hnorm⟩
    intro t
    obtain ⟨φ, hφ, hφx⟩ := B2Hecke.hecke_closure (L := L) p (fun t x y => hC t x y) pts hadd hgen t
    exact ⟨φ, fun s x y => hφ.apply s x y, hφx⟩
  refine ⟨pts, fun t => (hhecke t).choose, hB, (fun t x y => hC t x y), hadd, ?_, ?_, fun t => (hhecke t).choose_spec, hnorm⟩
  ·
    intro σ x
    exact B2Glue.gal_equivariance p ℓ c ε Mη eη heη hgal L aj pts hadd hnorm σ x
  ·
    intro A hA
    haveI : IsAlgClosed (ResidueField ↥A) := A.isAlgClosed_residueField_algebraicClosure_rat
    haveI : IsCurveOver (ResidueField ↥A) ↥(modularFunctionFieldFullC (ResidueField ↥A) p) :=
      ModularCurve.isCurveOver_modularFunctionFieldFullC (ResidueField ↥A) p
    haveI := hes_iso A hA
    obtain ⟨ptsκ, haddκ, hnormκ⟩ := hPTS (ResidueField ↥A) ((residue ↥A).comp (ρ A hA))
      ↥(modularFunctionFieldFullC (ResidueField ↥A) p) (Ms A hA) (es A hA) (hes A hA)
    have hsq : Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    have hsqA : Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) =
        Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hρ A hA]
    have hψ : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [Category.id_comp, hsq]
    have hψ' : 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) =
        Spec.map (CommRingCat.ofHom ((residue ↥A).comp (ρ A hA))) := by
      rw [Category.id_comp, hsq]
    let ptsSp : JZeroC (ResidueField ↥A) p ≃
        SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) f :=
      { toFun := fun u => GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u)
        invFun := fun z => ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ' z)
        left_inv := fun u => by
          show ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ'
            (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u))) = u
          apply ptsκ.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp])
        right_inv := fun z => by
          show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ
            (ptsκ (ptsκ.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ' z))) = z
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp]) }
    have hptsSp : ∀ u, (ptsSp u).1 = (ptsκ u).1 := fun u => Category.id_comp _
    have hψA : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) =
        Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA)) := by
      rw [Category.id_comp, hsqA]
    have hψA' : 𝟙 _ ≫ (Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) =
        Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) := by
      rw [Category.id_comp, hsqA]
    let ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ Spec.map (CommRingCat.ofHom (ρ A hA))) f :=
      { toFun := fun x => GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA (pts x)
        invFun := fun z => pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA' z)
        left_inv := fun x => by
          show pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA'
            (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA (pts x))) = x
          apply pts.injective
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp])
        right_inv := fun z => by
          show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA
            (pts (pts.symm (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψA' z))) = z
          rw [Equiv.apply_symm_apply]
          exact Subtype.ext (by simp [GoodReductionJacobian.schemeHomOverComp]) }
    refine ⟨Spec.map (CommRingCat.ofHom (ρ A hA)), ptsA, ptsSp, fun x => Category.id_comp _, ?_, ?_⟩
    · intro u v
      show GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ (u + v)) =
        L.mul _ (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ u)) (GoodReductionJacobian.schemeHomOverComp (𝟙 _) hψ (ptsκ v))
      rw [haddκ, L.mul_natural]
    ·
      intro hinp
      obtain ⟨r, hr, hpt⟩ := hsp A hA
      haveI : CharP (ResidueField ↥A) ℓ := A.residueField_charP_of_liesOverPrime Fact.out hA
      have hrr : r = placeReductionModL hinp :=
        B2Glue.r_eq_placeReductionModL p ℓ hℓp A hA r hr hinp
      exact B2Glue.sp_agreement p ℓ c ε Mη eη heη A (ρ A hA) (hρ A hA) (Ms A hA) (es A hA) (hes A hA)
        r hr hpt hinp L aj pts hadd hnorm ptsκ haddκ hnormκ ptsA (fun x => rfl) ptsSp (fun u => rfl) hrr

end B2Glue

namespace RingPhi

variable {R : Type} [CommRing R] {J : Scheme.{0}} {f : J ⟶ Spec (CommRingCat.of R)}

theorem comp_eq {T : Scheme.{0}} {s : T ⟶ Spec (CommRingCat.of R)} (x : SchemeHomOver s f)
    (φ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x φ = GoodReductionJacobian.schemeHomOverComp x.1 x.2 φ := rfl

theorem comp_mul (L : RelativeGroupLaw R f) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver s f) (φ ψ : SchemeHomOver f f) :
    NeronModelInfra.schemeHomOverComp x (L.mul f φ ψ) =
      L.mul s (NeronModelInfra.schemeHomOverComp x φ) (NeronModelInfra.schemeHomOverComp x ψ) := by
  rw [comp_eq, L.mul_natural f s x.1 x.2]
  rfl

theorem comp_one (L : RelativeGroupLaw R f) {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of R))
    (x : SchemeHomOver s f) :
    NeronModelInfra.schemeHomOverComp x (L.one f) = L.one s := by
  rw [comp_eq, L.one_natural f s x.1 x.2]

theorem pts_zero (L : RelativeGroupLaw R f) {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of R))
    {G : Type} [AddCommGroup G] (pts : G → SchemeHomOver t f)
    (hadd : ∀ u v : G, pts (u + v) = L.mul t (pts u) (pts v)) : pts 0 = L.one t := by
  have h1 := hadd 0 0
  rw [add_zero] at h1
  have := congrArg (fun z => L.mul t (L.inv t (pts 0)) z) h1
  beta_reduce at this
  rwa [L.inv_mul_cancel, ← L.mul_assoc, L.inv_mul_cancel, L.one_mul, eq_comm] at this

end RingPhi

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (p : ℕ) [NeZero p] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    {X : Scheme.{0}} (c : X ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) [IsProper c]
    [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))) c)

    (Mη : CurveModel (AlgebraicClosure ℚ) (modularFunctionFieldBar p))
    (eη : Mη.C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))))) [IsIso eη]
    (heη : eη ≫ pullback.snd c _ = Mη.toBase)
    (hgal : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
      (x x' : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
      x'.1 ≫ eη ≫ pullback.fst c _ =
        Spec.map (CommRingCat.ofHom (g : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫
          x.1 ≫ eη ≫ pullback.fst c _ →
      Mη.pointEquivPlace x' =
        arithmeticGalois (L := AlgebraicClosure ℚ) (modularFunctionFieldFull p) g • Mη.pointEquivPlace x)

    (ρ : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ → (↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A))
    (hρ : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      A.subtype.comp (ρ A hA) = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (Ms : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
      CurveModel (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p))
    (es : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), (Ms A hA).C ⟶ pullback c (Spec.map (CommRingCat.ofHom
      ((residue ↥A).comp (ρ A hA)))))
    (hes_iso : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ), IsIso (es A hA))
    (hes : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ),
      es A hA ≫ pullback.snd c _ = (Ms A hA).toBase)

    (hsp : ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
      [IsAlgClosed (ResidueField ↥A)],
      ∃ r : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p) →
          Place (ResidueField ↥A) (modularFunctionFieldFullC (ResidueField ↥A) p),
        IsPlaceReductionModL A p r ∧
        ∀ (xA : SchemeHomOver (Spec.map (CommRingCat.ofHom (ρ A hA))) c)
          (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
          (y : {q : Spec (CommRingCat.of (ResidueField ↥A)) ⟶ (Ms A hA).C //
            q ≫ (Ms A hA).toBase = 𝟙 _}),
          x.1 ≫ eη ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom A.subtype) ≫ xA.1 →
          y.1 ≫ es A hA ≫ pullback.fst c _ = Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ xA.1 →
          (Ms A hA).pointEquivPlace y = r (Mη.pointEquivPlace x))

    (M₀ : CurveModel ℚ ↥(modularFunctionFieldFull p))
    (e₀ : M₀.C ⟶ pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ)))) [IsIso e₀]
    (he₀ : e₀ ≫ pullback.snd c _ = M₀.toBase)
    (hcompat : ∀ (x : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _})
        (y : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶
          pullback c (Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) ℚ))))
        (x₀ : closedPoints M₀.C),
      y ≫ pullback.fst c _ = x.1 ≫ eη ≫ pullback.fst c _ →
      (y ≫ inv e₀).base (IsLocalRing.closedPoint (AlgebraicClosure ℚ)) = x₀.1 →
      ((Mη.pointEquivPlace x).toValuationSubring.toSubring.comap
          ((baseChangeEquiv (AlgebraicClosure ℚ) (modularFunctionFieldFull p)).toAlgHom.toRingHom.comp
            (Algebra.TensorProduct.includeRight (R := ℚ) (A := AlgebraicClosure ℚ)
              (B := ↥(modularFunctionFieldFull p))).toRingHom) =
        (M₀.placeOfPoint x₀).toValuationSubring.toSubring))

    (D : RelativePic0Designation ↥(GaloisRep.ratLocalizedAt ℓ) c)
    (hD : RepresentsRelSubPic c ε (algEquivZeroCut c ε) D)
    (hsm : Smooth D.toBase) (hpr : IsProper D.toBase) (hgc : GeometricallyConnected D.toBase)

    (aj : SchemeHomOver c D.toBase) (hajε : ε.1 ≫ aj.1 = D.zeroSection)
    (haj : ∀ (K : Type) [Field K] (t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x : SchemeHomOver t c),
        Nonempty ((hD.poincare.pullbackAlong
            ⟨x.1 ≫ aj.1, (Category.assoc _ _ _).trans ((congrArg (x.1 ≫ ·) aj.2).trans x.2)⟩).L ≅
          (RelEffCartierDiv.ofPoint c x.1 x.2).lineBundle ⊗
            (RelEffCartierDiv.ofPoint c (t ≫ ε.1)
              ((Category.assoc _ _ _).trans ((congrArg (t ≫ ·) ε.2).trans (Category.comp_id t)))).idealModule))
    :
    letI := heckeModuleBar p
    ∃ (pts : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)))) D.toBase)
      (φ : HeckeAlg → SchemeHomOver D.toBase D.toBase),
      AbelianSchemePropertyBundle ↥(GaloisRep.ratLocalizedAt ℓ) D.toBase ∧
      (∀ {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
        (x y : SchemeHomOver t D.toBase), (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t x y = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul t y x) ∧
      (∀ x y : JZero p, pts (x + y) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (pts x) (pts y)) ∧
      (∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : JZero p),
        (pts (σ • x)).1 =
          Spec.map (CommRingCat.ofHom (σ : AlgebraicClosure ℚ →+* AlgebraicClosure ℚ)) ≫ (pts x).1) ∧
      (∀ (A : ValuationSubring (AlgebraicClosure ℚ)), A.LiesOverPrime ℓ →
        ∃ (σA : Spec (CommRingCat.of ↥A) ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ)))
          (ptsA : JZero p ≃ SchemeHomOver (Spec.map (CommRingCat.ofHom A.subtype) ≫ σA) D.toBase)
          (ptsSp : JZeroC (ResidueField ↥A) p ≃
            SchemeHomOver (Spec.map (CommRingCat.ofHom (residue ↥A)) ≫ σA) D.toBase),
          (∀ x : JZero p, (ptsA x).1 = (pts x).1) ∧
          (∀ u v : JZeroC (ResidueField ↥A) p, ptsSp (u + v) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul _ (ptsSp u) (ptsSp v)) ∧
          (ReductionInputsModL A p → ReductionOfPointsAgreesModL p A D.toBase σA ptsA ptsSp)) ∧
      (∀ t : HeckeAlg,
        (∀ {T : Scheme.{0}} (s : T ⟶ Spec (CommRingCat.of ↥(GaloisRep.ratLocalizedAt ℓ))) (x y : SchemeHomOver s D.toBase),
          NeronModelInfra.schemeHomOverComp ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s x y) (φ t) =
            (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul s (NeronModelInfra.schemeHomOverComp x (φ t))
              (NeronModelInfra.schemeHomOverComp y (φ t))) ∧
        ∀ x : JZero p, (pts (t • x)).1 = (pts x).1 ≫ (φ t).1) ∧

      (∀ s t : HeckeAlg, φ (s * t) = NeronModelInfra.schemeHomOverComp (φ t) (φ s)) ∧
      (∀ s t : HeckeAlg, φ (s + t) = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul D.toBase (φ s) (φ t)) ∧
      φ 1 = NeronModelInfra.schemeHomOverId D.toBase ∧
      φ 0 = (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one D.toBase ∧

      (∀ (x s : {q : Spec (CommRingCat.of (AlgebraicClosure ℚ)) ⟶ Mη.C // q ≫ Mη.toBase = 𝟙 _}),
          s.1 ≫ eη ≫ pullback.fst c _ =
            Spec.map (CommRingCat.ofHom (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))) ≫ ε.1 →
          ∃ Dv : Divisor.degZero (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar p),
            (Dv : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar p)) =
              Finsupp.single (Mη.pointEquivPlace x) 1 - Finsupp.single (Mη.pointEquivPlace s) 1 ∧
            (pts (Pic0.mk Dv)).1 = x.1 ≫ eη ≫ pullback.fst c _ ≫ aj.1) ∧

      (∀ (q : Nat.Primes) (ψ : SchemeHomOver D.toBase D.toBase),
        (∀ x : JZero p, (pts (heckeOperatorBar p q x)).1 = (pts x).1 ≫ ψ.1) → φ (heckeGen q) = ψ) := by
  letI := heckeModuleBar p
  haveI : IsDiscreteValuationRing ↥(GaloisRep.ratLocalizedAt ℓ) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt ℓ Fact.out

  obtain ⟨hB, hPTS⟩ :=
    AlgebraicGeometry.RelPicard.exists_pic0_equiv_points_of_representsRelSubPic_of_abelJacobi
      _ c ε D hD hsm hpr hgc aj hajε haj

  obtain ⟨pts, φ, h1, h2, h3, h4, h5, h6, h7⟩ := B2Glue.assembleExport p ℓ hℓp c ε Mη eη heη hgal ρ hρ Ms es hes_iso hes hsp D.toBase
    (RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD) aj hB
    (fun t x y => RepresentsRelSubPic.relativeGroupLaw_isCommutative (P := algEquivZeroGroupCut c ε) hD t x y) hPTS
    (fun q => ModularCurve.exists_heckeEndomorphism_relJacobian_of_representsRelSubPic_of_ratCurveModel p ℓ hℓp c ε D hD
      hsm hpr hgc aj hajε haj Mη eη heη hgal M₀ e₀ he₀ hcompat q)

  have RIG : ∀ (a b : SchemeHomOver D.toBase D.toBase),
      (∀ y : JZero p, (pts y).1 ≫ a.1 = (pts y).1 ≫ b.1) → a = b := fun a b hab =>
    AlgebraicGeometry.RelPicard.schemeHomOver_ext_of_forall_algebraicClosure_point ℓ c ε D hD hsm hpr hgc a b
      (fun x => by obtain ⟨y, rfl⟩ := pts.surjective x; exact hab y)

  have hφ : ∀ (t : HeckeAlg) (y : JZero p), (pts y).1 ≫ (φ t).1 = (pts (t • y)).1 :=
    fun t y => ((h6 t).2 y).symm
  have hφ' : ∀ (t : HeckeAlg) (y : JZero p),
      pts (t • y) = NeronModelInfra.schemeHomOverComp (pts y) (φ t) :=
    fun t y => Subtype.ext ((h6 t).2 y)
  refine ⟨pts, φ, h1, h2, h3, h4, h5, h6, ?_, ?_, ?_, ?_, h7, ?_⟩
  ·
    intro s t
    refine RIG _ _ fun y => ?_
    rw [hφ, mul_smul, (h6 s).2, (h6 t).2, Category.assoc]
    rfl
  ·
    intro s t
    refine RIG _ _ fun y => ?_
    have e : pts ((s + t) • y) = NeronModelInfra.schemeHomOverComp (pts y)
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).mul D.toBase (φ s) (φ t)) := by
      rw [add_smul, h3, hφ' s y, hφ' t y, RingPhi.comp_mul]
    rw [hφ, e]
    rfl
  ·
    refine RIG _ _ fun y => ?_
    rw [hφ, one_smul, NeronModelInfra.schemeHomOverId_coe, Category.comp_id]
  ·
    refine RIG _ _ fun y => ?_
    have e : pts ((0 : HeckeAlg) • y) = NeronModelInfra.schemeHomOverComp (pts y)
        ((RepresentsRelSubPic.relativeGroupLaw (P := algEquivZeroGroupCut c ε) hD).one D.toBase) := by
      rw [show ((0 : HeckeAlg) • y) = 0 from zero_smul HeckeAlg y, RingPhi.comp_one, RingPhi.pts_zero _ _ pts h3]
    rw [hφ, e]
    rfl
  ·
    intro q ψ hψ
    refine RIG _ _ fun y => ?_
    rw [hφ, heckeModuleBar_heckeGen_smul (ModularCurve.heckeOperatorsCommuteBar p) q y, hψ]

end S_ModularCurve_exists_pts_heckeRingAction_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel_of_abelJacobi
end P2MW
export P2MW.S_ModularCurve_exists_pts_heckeRingAction_relJacobian_jZero_of_representsRelSubPic_of_ratCurveModel_of_abelJacobi (solution)
