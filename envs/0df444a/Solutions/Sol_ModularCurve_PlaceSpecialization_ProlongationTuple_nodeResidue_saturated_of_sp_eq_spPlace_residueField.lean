-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_sp_eq_spPlace_residueField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/cee7a591-16bf-542c-afa1-ac22708f56c3

import Definitions.Def_ModularCurve_NodeLocalizedPlaces
import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ValuationSubring_ReduceAt
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_prolongationTuple_isModel_and_orderLawFixed
import Theorems.Thm_ModularCurve_ssPlaces_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_orderLawFixed
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_spPlace_of_isModel_of_orderLawFixed
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_eq_of_surjective
import Theorems.Thm_ModularCurve_CharPModel_exists_fibreModel_cuspChart_of_not_dvd
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel
import Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField
p2m_attr_erase "instance" "ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth AlgebraicCurve.CurveModel.locallyOfFiniteType_gluedToBase AlgebraicCurve.CurveModel.isFractionRing_overlap AlgebraicCurve.CurveModel.isLocallyNoetherian_glued AlgebraicCurve.CurveModel.jacobsonSpace_glued AlgebraicCurve.CurveModel.isOpenImmersion_ι₀ AlgebraicCurve.CurveModel.isIntegral_glued AlgebraicCurve.CurveModel.quasiSeparated_gluedToBase AlgebraicCurve.CurveModel.compactSpace_glued AlgebraicCurve.CurveModel.isIntegral_adjoin_chartRing AlgebraicCurve.CurveModel.isFractionRing_overlap_functionField AlgebraicCurve.CurveModel.isProper_gluedToBase AlgebraicCurve.CurveModel.isOpenImmersion_ιU AlgebraicCurve.CurveModel.isOpenImmersion_f₀ AlgebraicCurve.CurveModel.isOpenImmersion_fInf AlgebraicCurve.CurveModel.isOpenImmersion_ιInf AlgebraicCurve.CurveModel.algebra_overlap_functionField AlgebraicCurve.CurveModel.quasiCompact_gluedToBase AlgebraicCurve.CurveModel.algebraAdjoin AlgebraicCurve.CurveModel.isDedekindDomain_chartRing AlgebraicCurve.CurveModel.isIntegralClosure AlgebraicCurve.CurveModel.finite_chartRing AlgebraicCurve.CurveModel.centre_isPrime AlgebraicCurve.CurveModel.isFractionRing_chartRing AlgebraicCurve.CurveModel.finiteType_chartRing"
p2m_attr_erase "instance" "AlgebraicCurve.CurveModel.isNoetherianRing_chartRing AlgebraicCurve.CurveModel.isScalarTower_base_adjoin AlgebraicCurve.CurveModel.isScalarTower_adjoin AlgebraicCurve.CurveModel.chartRing_finitePresentation ModularCurve.numberField_of_finiteDimensional AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper instFieldLaurentSeriesAlgClosureRat instAlgebraModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algGaussBase instAlgebraModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResOne ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraSubtypeMemValuationSubringGaussBaseResTwo instFieldModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resOne instFieldLaurentSeries'"
p2m_attr_erase "instance" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_resTwo instModuleModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₁ instAlgebraModularFunctionFieldC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResOne instFieldModularFunctionFieldBar ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instAlgebraResidueFieldSubtypeMemValuationSubringGaussBaseResTwo ModularCurve.PlaceSpecialization.LevelOneProlongationPair.instFieldResTwo instFieldModularFunctionFieldFullC ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isScalarTower_gaussBase instAlgebraLaurentSeriesAlgClosureRat ModularCurve.PlaceSpecialization.LevelOneProlongationPair.isLocalHom_resBase₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.algResidueConst instCommRingModularFunctionFieldBar ModularCurve.instIsElliptic_tateBase ModularCurve.NodeLocalized.isLocalization_nodeDenominators ModularCurve.NodeLocalized.algebraEvalRange ModularCurve.NodeLocalized.isLocalRing_modularLocalizedAtPoint ModularCurve.NodeLocalized.isScalarTower_K_fieldOver_bar ModularCurve.NodeLocalized.algebraFieldOverBar ModularCurve.NodeLocalized.algebra_isIntegral_fieldOver_bar ModularCurve.NodeLocalized.isScalarTower_fieldOver_bar_laurent ModularCurve.NodeLocalized.charZero_fieldOver ModularCurve.NodeLocalized.algebraFieldOver ModularCurve.NodeLocalized.charZero_laurentSeries_algClosure instTopologicallyFGOfFiniteType AdicCompletion.instIsLocalRingMaximalIdeal"
p2m_attr_erase "simp" "ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom"
p2m_attr_erase "simp" "NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec AlgebraicCurve.CurveModel.coe_gInf AlgebraicCurve.CurveModel.coe_tInvChart AlgebraicCurve.CurveModel.ιInf_gluedToBase_assoc AlgebraicCurve.CurveModel.ιInf_gluedToBase AlgebraicCurve.CurveModel.primeOfι₀_asIdeal AlgebraicCurve.CurveModel.coe_tChart AlgebraicCurve.CurveModel.ι₀_gluedToBase_assoc AlgebraicCurve.CurveModel.primeOfιInf_asIdeal AlgebraicCurve.CurveModel.ι₀_gluedToBase AlgebraicCurve.CurveModel.coe_tma AlgebraicCurve.CurveModel.coe_primeEquivChartPlaces ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.symPoly_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe"
p2m_attr_erase "simp" "AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.cuspCount_one ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.specialise_zero ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_levelPolynomialEquiv_apply ModularCurve.coe_levelBaseRingDescent_apply ModularCurve.levelConst_apply ModularCurve.coe_laurentDescent_apply ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply"
p2m_attr_erase "simp" "ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₂ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_gaussOrderToIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₁ ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_constToGaussBase ModularCurve.PlaceSpecialization.LevelOneProlongationPair.coe_toIntegers₂ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst ModularCurve.NodeLocalized.coe_modularEvalAt ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq AlgebraicCurve.Pic.baseChange_mk AlgebraicCurve.Place.forgetConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_symm_apply AlgebraicCurve.Place.ord_forgetConstants AlgebraicCurve.Place.extendConstants_toValuationSubring AlgebraicCurve.Place.constantFieldEquiv_apply_toValuationSubring AlgebraicCurve.Place.mem_fiberConstants AlgebraicCurve.Place.restrictConstants_toValuationSubring ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap"
p2m_attr_erase "simp" "ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AdicCompletion.evalₐ_mapₐ AdicCompletion.mapAlgEquivOfBijective_apply AdicCompletion.levelMapₐ_mk AdicCompletion.mapₐ_of AdicCompletion.mapAlgEquiv_symm_apply AdicCompletion.mapAlgEquiv_apply AdicCompletion.evalₐ_ofLevelwiseEquiv AdicCompletion.evalₐ_levelwiseHom AdicCompletion.localizationEquiv_of AdicCompletion.evalₐ_ofLevelwiseEquiv_symm Localization.AtPrime.quotientPowEquiv_mk AdicCompletion.transportOf_of AdicCompletion.selfCompletion_smul_of AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul AdicCompletion.stabilizerToCompletionAut_of ModularCurve.crossingCoord_apply"

set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "AlgebraicCurve ModularCurve~jBar"
open ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.ProlongationTuple

namespace SatAux

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]

private noncomputable def hybrid
    (fm fm' : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A)) :
    CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) :=
  { fm with
    BInf := fm'.BInf
    constInf_mem := fm'.constInf_mem
    jInvBar_mem := fm'.jInvBar_mem
    integralInf := fm'.integralInf
    piInf := fm'.piInf
    piInf_const := fm'.piInf_const
    piInf_jInv := fm'.piInf_jInv
    ker_piInf := fm'.ker_piInf
    intClosed_piInf := fm'.intClosed_piInf
    frac_piInf := fm'.frac_piInf }

private theorem hybrid_cuspChart
    (fm fm' : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (hc : fm'.CuspChart) : (hybrid fm fm').CuspChart :=
  ⟨hc.tBar_mem, hc.piInf_t⟩

private theorem hybrid_spPlace_eq
    (fm fm' : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hV : ∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
        ∈ V.toValuationSubring.nonunits) :
    (hybrid fm fm').spPlace IsLocalRing.residue_surjective dataAll hsep V
      = fm.spPlace IsLocalRing.residue_surjective dataAll hsep V := by
  unfold CharPModel.FibreModel.spPlace
  show @dite _ (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits)
      (Classical.propDecidable _) _ _ =
    @dite _ (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits)
      (Classical.propDecidable _) _ _
  simp only [dif_pos hV]
  rfl

private theorem sp_eq_sp_of_finiteBranch
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace IsLocalRing.residue_surjective dataAll hsep)
    (P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (R₀ : ProlongationTuple P₀) (hmodel : R₀.IsModel) (hO₀ : R₀.OrderLawFixed)
    (fm' : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A)) (hc : fm'.CuspChart)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N))
    (hV : ∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
        ∈ V.toValuationSubring.nonunits) :
    P₀.sp V = P.sp V := by
  have h₀ : P₀.sp = fm'.spPlace IsLocalRing.residue_surjective dataAll hsep :=
    sp_eq_spPlace_of_isModel_of_orderLawFixed R₀ hqN hmodel hO₀ fm' hc IsLocalRing.residue_surjective dataAll hsep
  have h₁ : fm'.spPlace IsLocalRing.residue_surjective dataAll hsep
      = (hybrid fm fm').spPlace IsLocalRing.residue_surjective dataAll hsep :=
    CharPModel.FibreModel.spPlace_eq_of_surjective N q hqN A (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A)
      IsLocalRing.residue_surjective fm' (hybrid fm fm') hc (hybrid_cuspChart fm fm' hc) dataAll hsep
  have h₂ := hybrid_spPlace_eq fm fm' dataAll hsep V hV
  exact (congrFun h₀ V).trans ((congrFun h₁ V).trans (h₂.trans (congrFun hP V).symm))

end SatAux

namespace SatAux

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]

omit [Fact q.Prime] in

private theorem liesOverPrime_of_charP_residueField : A.LiesOverPrime q := by
  have hq : ((q : ℕ) : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_natCast]
    exact CharP.cast_eq_zero (IsLocalRing.ResidueField ↥A) q
  exact A.coe_mem_nonunits_iff.mpr hq

private theorem exists_fibreModel_cuspChart_residueField (hqN : ¬ q ∣ N) :
    ∃ fm' : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A), fm'.CuspChart :=
  CharPModel.exists_fibreModel_cuspChart_of_not_dvd N q hqN A liesOverPrime_of_charP_residueField

end SatAux

namespace SatAux

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem finiteBranch_restrictAlong_of_reduceFst_eq
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) (hV : P.reduceFst V = w) :
    ∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
        ∈ (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).toValuationSubring.nonunits := by
  set U : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) :=
    V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα with hUdef
  have hU : P.sp U = w := hV
  have hss : w.IsRational ∧ IsAffineGeomPlace (IsLocalRing.ResidueField ↥A) N w ∧
      w.evalAt (jGeomGen (IsLocalRing.ResidueField ↥A) N) ∈ ssJSet q (IsLocalRing.ResidueField ↥A) := hw
  have haff : 0 ≤ w.ord (jGeomGen (IsLocalRing.ResidueField ↥A) N) := Place.ord_nonneg_of_mem w hss.2.1.1
  by_cases hall : ∀ a : A, U.ord ((CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
      algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)) ≤ 0
  · have hpole := P.d0_j_pole U hall
    rw [hU] at hpole
    exact absurd hpole (not_lt.mpr haff)
  · push Not at hall
    obtain ⟨a, ha⟩ := hall
    refine ⟨a, ?_⟩
    by_cases hzero : (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ) = 0
    · rw [hzero, ValuationSubring.mem_nonunits_iff]
      simp
    · have hmem := Place.mem_of_ord_nonneg U hzero ha.le
      exact ValuationSubring.coe_mem_nonunits_iff.mpr ((U.mem_maximalIdeal_iff_ord_pos hzero hmem).mpr ha)

private theorem reduceFst_eq_iff_of_forall_finiteBranch
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (N * q))) :
    P.reduceFst V = w ↔ P₀.reduceFst V = w := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := finiteBranch_restrictAlong_of_reduceFst_eq P w hw V h
    show P₀.sp (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w
    rw [hsp _ ⟨a, ha⟩]
    exact h
  · intro h
    obtain ⟨a, ha⟩ := finiteBranch_restrictAlong_of_reduceFst_eq P₀ w hw V h
    show P.sp (V.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα) = w
    rw [← hsp _ ⟨a, ha⟩]
    exact h

private theorem mem_integersFst_iff_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.R₁.integers ↔ f ∈ R₀.R₁.integers := by
  rw [R.mem_integersFst_iff f, R₀.mem_integersFst_iff f]

private theorem mem_integersSnd_iff_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀) (f : ↥(modularFunctionFieldBar (N * q))) :
    f ∈ R.R₂.integers ↔ f ∈ R₀.R₂.integers := by
  rw [R.mem_integersSnd_iff f, R₀.mem_integersSnd_iff f]

private theorem residue₁_eq_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀) (f : ↥(modularFunctionFieldBar (N * q)))
    (h : f ∈ R.R₁.integers) (h₀ : f ∈ R₀.R₁.integers) :
    R.residue₁ ⟨f, h⟩ = R₀.residue₁ ⟨f, h₀⟩ := by
  have hf := (R.mem_integersFst_iff f).mp h
  obtain ⟨h', e⟩ := R.residue₁_eq_modularRedLocHom f hf
  obtain ⟨h₀', e₀⟩ := R₀.residue₁_eq_modularRedLocHom f hf
  apply Subtype.ext
  exact e.trans e₀.symm

private theorem residue₂_eq_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀) (f : ↥(modularFunctionFieldBar (N * q)))
    (h : f ∈ R.R₂.integers) (h₀ : f ∈ R₀.R₂.integers) :
    R.residue₂ ⟨f, h⟩ = R₀.residue₂ ⟨f, h₀⟩ := by
  rw [residue₂_apply, residue₂_apply, R.residue₂_eq f h, R₀.residue₂_eq f h₀]
  exact residue₁_eq_of_tuples R R₀ (ProlongationTuple.atkinLehnerBar N q f) _ _

private theorem mem_nodeIntegersOver_iff_of_tuples
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (g : ↥(modularFunctionFieldBar (N * q))) :
    g ∈ R.nodeIntegersOver K w ↔ g ∈ R₀.nodeIntegersOver K w := by
  rw [R.mem_nodeIntegersOver_iff K w g, R₀.mem_nodeIntegersOver_iff K w g, R.mem_nodeIntegers_iff w g,
    R₀.mem_nodeIntegers_iff w g, mem_integersFst_iff_of_tuples R R₀ g, mem_integersSnd_iff_of_tuples R R₀ g]
  simp only [reduceFst_eq_iff_of_forall_finiteBranch P P₀ hsp w hw]

private theorem nodeResidue₁_eq_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.nodeIntegers w) (hg₀ : g ∈ R₀.nodeIntegers w) :
    R.nodeResidue₁ w ⟨g, hg⟩ = R₀.nodeResidue₁ w ⟨g, hg₀⟩ :=
  residue₁_eq_of_tuples R R₀ g hg.1 hg₀.1

private theorem nodeResidue₂_eq_of_tuples
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (g : ↥(modularFunctionFieldBar (N * q))) (hg : g ∈ R.nodeIntegers w) (hg₀ : g ∈ R₀.nodeIntegers w) :
    R.nodeResidue₂ w ⟨g, hg⟩ = R₀.nodeResidue₂ w ⟨g, hg₀⟩ :=
  residue₂_eq_of_tuples R R₀ g hg.2.1 hg₀.2.1

private theorem nodeIntegersOver_eq_of_tuples
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    R.nodeIntegersOver K w = R₀.nodeIntegersOver K w :=
  SetLike.ext fun g => mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K g

private theorem hres_of_tuples
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) :
    ∀ g : ↥(R₀.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R₀.nodeConst K w o) := by
  intro g₀
  have hg : (g₀ : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver K w :=
    (mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K g₀).mpr g₀.2
  obtain ⟨o, ho⟩ := hres ⟨g₀, hg⟩
  refine ⟨o, fun hu => ho ?_⟩
  obtain ⟨b₀, hb₀⟩ := hu.exists_right_inv
  have hb : (b₀ : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver K w :=
    (mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K b₀).mpr b₀.2
  refine isUnit_iff_exists_inv.mpr ⟨⟨b₀, hb⟩, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hb₀
  push_cast at h ⊢
  exact h

private theorem exists_eq_nodeConst_mul_of_tuples
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (h₀ : ∀ g : ↥(R₀.nodeIntegersOver K w),
      (R₀.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∧ R₀.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) ↔
        g ∈ Ideal.span {R₀.nodeConst K w ϖ})
    (g : ↥(R.nodeIntegersOver K w)) (h1 : R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0) (h2 : R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) :
    ∃ b : ↥(R.nodeIntegersOver K w), g = R.nodeConst K w ϖ * b := by
  have hg₀ : (g : ↥(modularFunctionFieldBar (N * q))) ∈ R₀.nodeIntegersOver K w :=
    (mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K g).mp g.2
  have hz₁ : R₀.nodeResidue₁ w ⟨g, hg₀.1⟩ = 0 := (nodeResidue₁_eq_of_tuples R R₀ w g g.2.1 hg₀.1).symm.trans h1
  have hz₂ : R₀.nodeResidue₂ w ⟨g, hg₀.1⟩ = 0 := (nodeResidue₂_eq_of_tuples R R₀ w g g.2.1 hg₀.1).symm.trans h2
  have hmem : (⟨g, hg₀⟩ : ↥(R₀.nodeIntegersOver K w)) ∈ Ideal.span {R₀.nodeConst K w ϖ} :=
    (h₀ ⟨g, hg₀⟩).mp ⟨hz₁, hz₂⟩
  obtain ⟨b₀, hb₀⟩ := Ideal.mem_span_singleton.mp hmem
  have hb : (b₀ : ↥(modularFunctionFieldBar (N * q))) ∈ R.nodeIntegersOver K w :=
    (mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K b₀).mpr b₀.2
  refine ⟨⟨b₀, hb⟩, Subtype.ext ?_⟩
  have h := congrArg Subtype.val hb₀
  push_cast at h ⊢
  exact h

private theorem nodeResidue₁_eq_of_tuples'
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(R.nodeIntegersOver K w)) (x₀ : ↥(R₀.nodeIntegersOver K w))
    (hx : (x : ↥(modularFunctionFieldBar (N * q))) = x₀) :
    R.nodeResidue₁ w ⟨x, x.2.1⟩ = R₀.nodeResidue₁ w ⟨x₀, x₀.2.1⟩ := by
  obtain ⟨a, ha⟩ := x
  obtain ⟨a₀, ha₀⟩ := x₀
  cases hx
  exact nodeResidue₁_eq_of_tuples R R₀ w a ha.1 ha₀.1

private theorem nodeResidue₂_eq_of_tuples'
    {P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ}
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (x : ↥(R.nodeIntegersOver K w)) (x₀ : ↥(R₀.nodeIntegersOver K w))
    (hx : (x : ↥(modularFunctionFieldBar (N * q))) = x₀) :
    R.nodeResidue₂ w ⟨x, x.2.1⟩ = R₀.nodeResidue₂ w ⟨x₀, x₀.2.1⟩ := by
  obtain ⟨a, ha⟩ := x
  obtain ⟨a₀, ha₀⟩ := x₀
  cases hx
  exact nodeResidue₂_eq_of_tuples R R₀ w a ha.1 ha₀.1

private theorem saturated_of_tuples
    [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (P P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A)
      (IsLocalRing.residue ↥A) hα hβ)
    (hsp : ∀ V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N),
      (∃ a : A, (CharPModel.jBar N : ↥(modularFunctionFieldBar N)) -
        algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar N) (a : AlgebraicClosure ℚ)
          ∈ V.toValuationSubring.nonunits) → P₀.sp V = P.sp V)
    (R : ProlongationTuple P) (R₀ : ProlongationTuple P₀)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (sat₀ :
      (∀ g g' : ↥(R₀.nodeIntegersOver K w),
        0 < w.ord (R₀.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R₀.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R₀.nodeIntegersOver K w),
          R₀.nodeResidue₁ w ⟨g, g.2.1⟩ = R₀.nodeResidue₁ w ⟨g', g'.2.1⟩ * R₀.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
      (∀ g g' : ↥(R₀.nodeIntegersOver K w),
        0 < (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R₀.nodeResidue₂ w ⟨g, g.2.1⟩) →
        (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R₀.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
        ∃ b : ↥(R₀.nodeIntegersOver K w),
          R₀.nodeResidue₂ w ⟨g, g.2.1⟩ = R₀.nodeResidue₂ w ⟨g', g'.2.1⟩ * R₀.nodeResidue₂ w ⟨b, b.2.1⟩))
    :
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) := by
  have hiff := mem_nodeIntegersOver_iff_of_tuples P P₀ hsp R R₀ w hw K
  refine ⟨fun g g' hg hg' => ?_, fun g g' hg hg' => ?_⟩
  · have e := nodeResidue₁_eq_of_tuples' R R₀ w K g ⟨g, (hiff g).mp g.2⟩ rfl
    have e' := nodeResidue₁_eq_of_tuples' R R₀ w K g' ⟨g', (hiff g').mp g'.2⟩ rfl
    obtain ⟨b₀, hb₀⟩ := sat₀.1 ⟨g, (hiff g).mp g.2⟩ ⟨g', (hiff g').mp g'.2⟩
      (hg.trans_eq (congrArg w.ord e)) ((congrArg w.ord e').symm.trans hg')
    have eb := nodeResidue₁_eq_of_tuples' R R₀ w K ⟨b₀, (hiff b₀).mpr b₀.2⟩ b₀ rfl
    exact ⟨⟨b₀, (hiff b₀).mpr b₀.2⟩, e.trans (hb₀.trans (by rw [e', eb]))⟩
  · have e := nodeResidue₂_eq_of_tuples' R R₀ w K g ⟨g, (hiff g).mp g.2⟩ rfl
    have e' := nodeResidue₂_eq_of_tuples' R R₀ w K g' ⟨g', (hiff g').mp g'.2⟩ rfl
    obtain ⟨b₀, hb₀⟩ := sat₀.2 ⟨g, (hiff g).mp g.2⟩ ⟨g', (hiff g').mp g'.2⟩
      (hg.trans_eq (congrArg _ e)) ((congrArg _ e').symm.trans hg')
    have eb := nodeResidue₂_eq_of_tuples' R R₀ w K ⟨b₀, (hiff b₀).mpr b₀.2⟩ b₀ rfl
    exact ⟨⟨b₀, (hiff b₀).mpr b₀.2⟩, e.trans (hb₀.trans (by rw [e', eb]))⟩

end SatAux

namespace SatAux

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}

private theorem nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_laws [DecidableEq (IsLocalRing.ResidueField ↥A)]
    (hqN : ¬ q ∣ N)
    (P₀ : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (R₀ : ProlongationTuple P₀) (hmodel : R₀.IsModel) (hO₀ : R₀.OrderLawFixed)
    (W : Finset (Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)))
    (hW : ∀ v ∈ W, v ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (hreg : R₀.RegularityLaw W) (hval : R₀.NodeValueLaw W)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N)) (hw : w ∈ W)
    (hres₀ : ∀ g : ↥(R₀.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R₀.nodeConst K w o))
    (ϖ : ↥(NodeLocalized.coeffSubring A K))
    (hϖ : ∀ d : ↥(NodeLocalized.coeffSubring A K),
      NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d') :
    ∀ g : ↥(R₀.nodeIntegersOver K w),
      (R₀.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 ∧ R₀.nodeResidue₂ w ⟨g, g.2.1⟩ = 0) ↔
        g ∈ Ideal.span {R₀.nodeConst K w ϖ} := by
  obtain ⟨hL, hN, -⟩ := R₀.nodeIntegersOver_isLocalRing_exists_isMaximal_of_regularityLaw hqN hO₀ W hW hreg K w hw
  have hker : ∀ c : ↥A, IsLocalRing.residue ↥A c = 0 ↔ c ∈ IsLocalRing.maximalIdeal ↥A :=
    fun c => IsLocalRing.residue_eq_zero_iff c
  obtain ⟨W', _, _, _, _, π, hπ, σ, hσπ, hσ⟩ :=
    R₀.exists_completeDVR_ringHom_adicCompletion_nodeIntegersOver hqN hker K w hres₀ ϖ hϖ
  obtain ⟨_, -, c, -⟩ :=
    R₀.exists_exponent_ringEquiv_adicCompletion_nodeIntegersOver_uvCrossingModel hqN hmodel W hW hreg hval hO₀ K w hw
      ϖ hϖ π hπ σ hσπ hσ
  exact R₀.nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_orderLawFixed hqN hmodel hO₀ W hW hreg hval K w hw c ϖ hϖ

end SatAux

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N]
    [CharP (IsLocalRing.ResidueField ↥A) q]
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    [DecidableEq (IsLocalRing.ResidueField ↥A)] (hqN : ¬ q ∣ N)
    (fm : CharPModel.FibreModel N A q (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A))
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (IsLocalRing.ResidueField ↥A)))).map
      (algebraMap (Polynomial (IsLocalRing.ResidueField ↥A)) (RatFunc (IsLocalRing.ResidueField ↥A)))).Separable)
    (P : PlaceSpecialization A q N data hKr (IsLocalRing.ResidueField ↥A) (IsLocalRing.residue ↥A) hα hβ)
    (hP : P.sp = fm.spPlace IsLocalRing.residue_surjective dataAll hsep)
    (R : ProlongationTuple P) (hO : R.OrderLawFixed)
    (w : Place (IsLocalRing.ResidueField ↥A) (modularFunctionFieldC (IsLocalRing.ResidueField ↥A) N))
    (hw : w ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A))
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (hres : ∀ g : ↥(R.nodeIntegersOver K w),
      ∃ o : ↥(NodeLocalized.coeffSubring A K), ¬ IsUnit (g - R.nodeConst K w o)) :
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < w.ord (R.nodeResidue₁ w ⟨g, g.2.1⟩) → w.ord (R.nodeResidue₁ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₁ w ⟨g, g.2.1⟩ = R.nodeResidue₁ w ⟨g', g'.2.1⟩ * R.nodeResidue₁ w ⟨b, b.2.1⟩) ∧
    (∀ g g' : ↥(R.nodeIntegersOver K w),
      0 < (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g, g.2.1⟩) →
      (arithFrobC q (IsLocalRing.ResidueField ↥A) N • w).ord (R.nodeResidue₂ w ⟨g', g'.2.1⟩) = 1 →
      ∃ b : ↥(R.nodeIntegersOver K w),
        R.nodeResidue₂ w ⟨g, g.2.1⟩ = R.nodeResidue₂ w ⟨g', g'.2.1⟩ * R.nodeResidue₂ w ⟨b, b.2.1⟩) ∧
    (∀ ϖ : ↥(NodeLocalized.coeffSubring A K),
      (∀ d : ↥(NodeLocalized.coeffSubring A K),
        NodeLocalized.redRestrict (IsLocalRing.residue ↥A) K d = 0 ↔ ∃ d', d = ϖ * d') →
      ∀ g : ↥(R.nodeIntegersOver K w), R.nodeResidue₁ w ⟨g, g.2.1⟩ = 0 → R.nodeResidue₂ w ⟨g, g.2.1⟩ = 0 →
        ∃ b : ↥(R.nodeIntegersOver K w), g = R.nodeConst K w ϖ * b) := by
  have _ := hO
  have hfm := SatAux.exists_fibreModel_cuspChart_residueField (A := A) (N := N) hqN
  obtain ⟨fm', hc⟩ := hfm
  have hfin := ModularCurve.ssPlaces_finite q N (IsLocalRing.ResidueField ↥A)
  have hex :=
    ModularCurve.PlaceSpecialization.exists_prolongationTuple_isModel_and_orderLawFixed
      (data := data) (hKr := hKr) (hα := hα) (hβ := hβ) hqN IsLocalRing.residue_surjective
      hfin.toFinset (fun v => by
        rw [Set.Finite.mem_toFinset]
        constructor <;> intro h <;> convert h using 2)
  obtain ⟨P₀, R₀, hmodel₀, hreg₀, hval₀, hO₀⟩ := hex
  have hW₀ : ∀ v ∈ hfin.toFinset, v ∈ ssPlaces q N (IsLocalRing.ResidueField ↥A) :=
    fun v hv => hfin.mem_toFinset.mp hv
  have hsp := fun V hV =>
    SatAux.sp_eq_sp_of_finiteBranch hqN fm dataAll hsep P hP P₀ R₀ hmodel₀ hO₀ fm' hc V hV
  have sat₀ :=
    ModularCurve.PlaceSpecialization.ProlongationTuple.nodeResidue_saturated_of_orderLawFixed
      R₀ hqN hmodel₀ hO₀ hfin.toFinset hW₀ hreg₀ hval₀ K w (hfin.mem_toFinset.mpr hw)
  have h12 := SatAux.saturated_of_tuples P P₀ hsp R R₀ w hw K sat₀
  have hres₀ := SatAux.hres_of_tuples P P₀ hsp R R₀ w hw K hres
  have h₀ := fun ϖ hϖ =>
    SatAux.nodeResidue_eq_zero_and_eq_zero_iff_mem_span_of_laws hqN P₀ R₀ hmodel₀ hO₀ hfin.toFinset hW₀
      hreg₀ hval₀ K w (hfin.mem_toFinset.mpr hw) hres₀ ϖ hϖ
  exact ⟨h12.1, h12.2, fun ϖ hϖ g h1 h2 =>
    SatAux.exists_eq_nodeConst_mul_of_tuples P P₀ hsp R R₀ w hw K ϖ (h₀ ϖ hϖ) g h1 h2⟩

end S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_ProlongationTuple_nodeResidue_saturated_of_sp_eq_spPlace_residueField (solution)
