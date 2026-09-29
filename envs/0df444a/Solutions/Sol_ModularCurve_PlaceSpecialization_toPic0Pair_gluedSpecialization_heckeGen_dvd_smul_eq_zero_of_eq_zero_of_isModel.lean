-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/14518e55-2aa3-5f03-9973-0b994c706b92

import Definitions.Def_ModularCurve_JZeroSemistableSpecialization
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_HeckeOperatorTotal
import Definitions.Def_AlgebraicCurve_Correspondence
import Definitions.Def_ModularCurve_DegeneracyTower
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_heckeInputsAlong_of_prime
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel
import Theorems.Thm_ModularCurve_mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne
import Theorems.Thm_ModularCurve_deg_eq_one_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_ModularCurve_SpecializationWitness
import Definitions.Def_ModularCurve_ProlongationTuple
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldC_of_good
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_heckeDescent_family_qne_ell
import Theorems.Thm_ModularCurve_PlaceSpecialization_spPic0_heckeGen_ell_eq_heckeFibreGeom
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent ModularCurve.B3.instIsElliptic_goodModel WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.numberField_of_finiteDimensional GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup WeierstrassCurve.Affine.Point.instFinite ModularCurve.IgusaScheme.isOpenImmersion_fInf ModularCurve.IgusaScheme.isOpenImmersion_ιInf ModularCurve.IgusaScheme.fact_jFull_ne_zero ModularCurve.IgusaScheme.isOpenImmersion_ιFin ModularCurve.IgusaScheme.isOpenImmersion_fFin AlgebraicCurve.CurveModel.isProper AlgebraicCurve.CurveModel.isIntegral AlgebraicCurve.CurveModel.smooth CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions"
p2m_attr_erase "instance" "FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.Gamma0Pair.map_toCurve WeierstrassCurve.mapPoint_eq_ratPointMap ModularCurve.Gamma0Pair.map_gen ModularCurve.Gamma0Pair.map_eq_gamma0PairMap ModularCurve.ModuliPoint.map_eq_moduliPointMapRingHom ModularCurve.ModuliPoint.map_mk WeierstrassCurve.mapPointHom_apply"
p2m_attr_erase "simp" "WeierstrassCurve.mapPoint_zero AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.ProjectiveLine.map_mk ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.vcInvEmbedding_apply ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU"
p2m_attr_erase "simp" "ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ"
p2m_attr_erase "simp" "TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero ModularCurve.cuspCount_one WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero HahnSeries.ramScale_apply"
p2m_attr_erase "simp" "AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.reductionDivAlong_apply"
p2m_attr_erase "simp" "ModularCurve.coe_reductionDegZeroAlong WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ ModularCurve.symPoly_zero GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.CharPModel.FibreModel.mk.injEq ModularCurve.CharPModel.FibreModel.mk.sizeOf_spec ModularCurve.IgusaScheme.ιInf_igusaTo_assoc ModularCurve.IgusaScheme.coe_jFull ModularCurve.IgusaScheme.coe_jInvChartInf ModularCurve.IgusaScheme.coe_jChartFin ModularCurve.IgusaScheme.ιFin_igusaTo ModularCurve.IgusaScheme.ιInf_igusaTo ModularCurve.IgusaScheme.ιFin_igusaTo_assoc GoodReductionJacobian.RelativePic0Designation.mk.sizeOf_spec GoodReductionJacobian.AvatarSchemeBridge.mk.injEq MilneJVScheme.JacobianSchemeData.mk.injEq GoodReductionJacobian.AvatarSchemeBridge.mk.sizeOf_spec MilneJVScheme.JacobianSchemeData.mk.sizeOf_spec GoodReductionJacobian.RelativePic0Designation.mk.injEq NeronModelInfra.specGenericFibreInclusion_eq NeronModelInfra.genericFibreRestrict_coe_comp_snd NeronModelInfra.genericFibreRestrict_coe_comp_fst GoodReductionJacobian.schemeHomOverComp_coe NeronModelInfra.schemeHomOverEquivOverHom_apply GoodReductionJacobian.RelativeGroupLaw.mk.sizeOf_spec NeronModelInfra.schemeHomOverEquivOverHom_symm_apply NeronModelInfra.overHomToSchemeHomOver_coe GoodReductionJacobian.RelativeGroupLaw.mk.injEq"
p2m_attr_erase "simp" "NeronModelInfra.overHomToSchemeHomOver_schemeHomOverToOverHom NeronModelInfra.schemeHomOverToOverHom_left NeronModelInfra.schemeHomOverToOverHom_overHomToSchemeHomOver NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_symm_restrict NeronModelInfra.schemeHomOverComp_id_left NeronModelInfra.schemeHomOverComp_id_right NeronModelInfra.schemeHomOverId_coe NeronModelInfra.NeronModelPropertyBundle.endExtensionEquiv_apply NeronModelInfra.NeronModelPropertyBundle.restrict_endExtensionEquiv_symm NeronModelInfra.schemeHomOverComp_coe AlgebraicCurve.CurveModel.mk.injEq AlgebraicCurve.CurveModel.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.sizeOf_spec ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₂_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply ModularCurve.PlaceSpecialization.LevelOneProlongationPair.mk.injEq ModularCurve.coe_nodeEquiv_symm_apply ModularCurve.frobNodePair_jOfNode ModularCurve.jOfNode_mk ModularCurve.widthOf_mk ModularCurve.frobNodePairEmb_apply ModularCurve.card_nodePairsOf ModularCurve.frobNodePair_snd ModularCurve.coe_nodeEquiv_apply ModularCurve.frobNodePair_fst ModularCurve.coe_heckeBetaC AlgebraicCurve.Divisor.coe_degZeroEnd ModularCurve.coe_heckeAlphaC AlgebraicCurve.Divisor.congr_single AlgebraicCurve.Pic0.coe_degZeroCongr_symm AlgebraicCurve.Divisor.degree_congr AlgebraicCurve.Divisor.degree_congr_symm AlgebraicCurve.Pic0.coe_degZeroCongr ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply"
p2m_attr_erase "simp" "CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~degree_mapDomain_of_deg_eq ModularCurve.PlaceSpecialization"

private theorem d35m_endHom_C {J : Type*} [AddCommGroup J] (g : HeckeAlg →+* Module.End ℤ J)
    (a : ℤ) : g (MvPolynomial.C a) = (a : Module.End ℤ J) := by
  rw [← MvPolynomial.algebraMap_eq, eq_intCast, map_intCast]

private theorem d35m_family_commute {J J' : Type*} [AddCommGroup J] [AddCommGroup J']
    (f : J →+ J') (hsurj : Function.Surjective f) (T' : Nat.Primes → Module.End ℤ J')
    (ev : HeckeAlg →+* Module.End ℤ J)
    (hgen : ∀ (p : Nat.Primes) (x : J), T' p (f x) = f (ev (heckeGen p) x))
    (p p' : Nat.Primes) : Commute (T' p) (T' p') := by
  refine LinearMap.ext fun z => ?_
  obtain ⟨x, rfl⟩ := hsurj z
  have emul : ∀ a b : Nat.Primes,
      (T' a * T' b) (f x) = f (ev (heckeGen a * heckeGen b) x) := by
    intro a b
    calc (T' a * T' b) (f x)
        = T' a (T' b (f x)) := rfl
      _ = T' a (f (ev (heckeGen b) x)) := DFunLike.congr_arg (T' a) (hgen b x)
      _ = f (ev (heckeGen a) (ev (heckeGen b) x)) := hgen a _
      _ = f ((ev (heckeGen a) * ev (heckeGen b)) x) := rfl
      _ = f (ev (heckeGen a * heckeGen b) x) := by rw [map_mul]
  show (T' p * T' p') (f x) = (T' p' * T' p) (f x)
  rw [emul p p', emul p' p, mul_comm (heckeGen p) (heckeGen p')]

private theorem d35m_intertwine {J J' : Type*} [AddCommGroup J] [AddCommGroup J']
    (f : J →+ J') (fam : CommutingHeckeFamily J') (ev : HeckeAlg →+* Module.End ℤ J)
    (hgen : ∀ (p : Nat.Primes) (x : J), fam.T p (f x) = f (ev (heckeGen p) x)) :
    ∀ (T : HeckeAlg) (y : J), f (ev T y) = fam.endHom T (f y) := by
  intro T
  induction T using MvPolynomial.induction_on with
  | C a =>
    intro y
    rw [d35m_endHom_C ev a, Module.End.intCast_apply, map_zsmul, d35m_endHom_C fam.endHom a,
      Module.End.intCast_apply]
  | add p r ihp ihr =>
    intro y
    rw [map_add, LinearMap.add_apply, map_add, ihp y, ihr y, map_add, LinearMap.add_apply]
  | mul_X p n ih =>
    intro y
    show f (ev (p * heckeGen n) y) = fam.endHom (p * heckeGen n) (f y)
    calc f (ev (p * heckeGen n) y)
        = f ((ev p * ev (heckeGen n)) y) := by rw [map_mul]
      _ = f (ev p (ev (heckeGen n) y)) := rfl
      _ = fam.endHom p (f (ev (heckeGen n) y)) := ih _
      _ = fam.endHom p (fam.T n (f y)) := DFunLike.congr_arg _ (hgen n y).symm
      _ = fam.endHom p (fam.endHom (heckeGen n) (f y)) := by
          rw [CommutingHeckeFamily.endHom_heckeGen]
      _ = (fam.endHom p * fam.endHom (heckeGen n)) (f y) := rfl
      _ = fam.endHom (p * heckeGen n) (f y) := by rw [map_mul]

private theorem GluedHecke.heckeModule_spPic0 (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
      ∃ (_ : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N))),
                (∀ (T : HeckeAlg) (y : JZero N), P.spPic0 (T • y) = T • P.spPic0 y) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  haveI : IsCurveOver (ResidueField A) (modularFunctionFieldC (ResidueField A) N) :=
    isCurveOver_modularFunctionFieldC_of_good (ResidueField A) N q hqN
  intro data hKr hα hβ P
  have hcomm : HeckeOperatorsCommuteBar N := heckeOperatorsCommuteBar N
  obtain ⟨T', hne, hchar⟩ :=
    P.exists_heckeDescent_family_qne_ell N hcomm q hqN A hA data hKr hα hβ
  have hsurj : Function.Surjective P.spPic0 := P.spPic0_surjective

  have key2 : ∀ (p : Nat.Primes) (x : JZero N),
      T' p (P.spPic0 x) = P.spPic0 (heckeEvalBar hcomm (heckeGen p) x) := by
    intro p x
    by_cases hp : (p : ℕ) = q
    · have hpq : p = (⟨q, Fact.out⟩ : Nat.Primes) := Subtype.ext hp
      subst hpq
      exact (DFunLike.congr_fun hchar (P.spPic0 x)).trans
        ((P.spPic0_heckeGen_ell_eq_heckeFibreGeom N hcomm q hqN A hA data hKr hα hβ x).trans
          (congrArg P.spPic0 (heckeModuleBar_smul_def hcomm _ x)))
    · exact (hne p hp x).trans (congrArg P.spPic0 (heckeModuleBar_smul_def hcomm _ x))

  have hT'comm : ∀ p p' : Nat.Primes, Commute (T' p) (T' p') :=
    d35m_family_commute P.spPic0 hsurj T' (heckeEvalBar hcomm) key2
  have key' := d35m_intertwine P.spPic0 (CommutingHeckeFamily.mk T' hT'comm)
    (heckeEvalBar hcomm) key2
  refine ⟨(CommutingHeckeFamily.mk T' hT'comm).module, fun T y => ?_⟩
  exact (congrArg P.spPic0 (heckeModuleBar_smul_def hcomm T y)).trans (key' T y)

private theorem GluedHecke.degree_mapDomain_of_deg_eq {K₁ F₁ K₂ F₂ : Type*}
    [Field K₁] [Field F₁] [Algebra K₁ F₁] [Field K₂] [Field F₂] [Algebra K₂ F₂]
    (r : Place K₁ F₁ → Place K₂ F₂) (hdeg : ∀ P, (r P).deg = P.deg)
    (D : Divisor K₁ F₁) :
    Divisor.degree (Finsupp.mapDomain r D) = Divisor.degree D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add P n D _ _ ih =>
    rw [Finsupp.mapDomain_add, map_add, map_add, ih, Finsupp.mapDomain_single,
      Divisor.degree_single, Divisor.degree_single, hdeg]

private theorem GluedHecke.heckeGen_smul_mk (M : ℕ) [NeZero M]
    (hcomm : HeckeOperatorsCommuteBar M) (ℓ : Nat.Primes) :
    haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
    ∀ (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) M ℓ)
      [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (M * ℓ))]
      (hFI : FundamentalIdentityAlong (AlgebraicClosure ℚ)
        (heckeBetaBar (AlgebraicClosure ℚ) M ℓ) hβ)
      (hfin : FiniteAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ))
      (hN : NormFormulaAlong (AlgebraicClosure ℚ) (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ) hfin)
      (E : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar M)))),
        (letI := heckeModuleBar M; heckeGen ℓ • Pic0.mk E)
          = Pic0.mk (Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) M ℓ)
              (heckeAlphaBar (AlgebraicClosure ℚ) M ℓ) hβ hα hFI E) := by
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  intro hα hβ _ hFI hfin hN E
  letI := heckeModuleBar M
  rw [heckeModuleBar_heckeGen_smul hcomm ℓ, heckeOperatorBar_apply]
  have hOA := heckeOperatorAlong_eq hα hβ hFI hfin hN
  rw [hOA]
  rfl

private theorem GluedHecke.comp_fst (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (modP : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hmod :         (∀ (T : HeckeAlg) (y : JZero N), P.spPic0 (T • y) = T • P.spPic0 y))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp)
      (ℓ : Nat.Primes) (hℓN : (ℓ : ℕ) ∣ N) (hℓq : (ℓ : ℕ) ≠ q)
      (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q))
      (hcomp : comp x = 0),
        letI := modP
        (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).1 =
          (heckeGen ℓ •
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
              (sp x)).1 := by

  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp modP hmod hsurj hker hsp ℓ hℓN hℓq x hx hcomp
  have _ := hℓN
  letI := modP
  have _ := hstab; have _ := hsurj; have _ := e; have _ := hW

  have hcommNq := ModularCurve.heckeOperatorsCommuteBar (N * q)
  have hcommN := ModularCurve.heckeOperatorsCommuteBar N
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hin_up := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) (N * q) (ℓ : ℕ)
  have hin_down := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) N (ℓ : ℕ)
  obtain ⟨hαℓ, hβℓ, _, hfin_up, hFI_up, hN_up⟩ := hin_up
  obtain ⟨hαℓN, hβℓN, _, hfin_dn, hFI_dn, hN_dn⟩ := hin_down
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * (ℓ : ℕ))
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * (ℓ : ℕ))

  have hgood_x : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (x : JZero (N * q)) := (hker x).1 hcomp
  have hMplus := ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hNV hO ℓ hℓq hαℓ hβℓ
    (x : JZero (N * q)) hgood_x
  obtain ⟨D, hgoodD, hadmD, hmkD, hgoodD', hadmD', hfst, hsnd⟩ := hMplus
  have _ := hsnd

  have hH : Pic0.mk D ∈ inertiaInvariants A (N * q) := hmkD ▸ x.2
  have hx_eq : x = ⟨Pic0.mk D, hH⟩ := Subtype.ext hmkD.symm
  have hspD : sp ⟨Pic0.mk D, hH⟩
        = GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D, hadmD⟩ :=
    hsp D hH ⟨P.glueData _ D, hadmD⟩ hgoodD rfl

  let D_Tℓ := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ hαℓ hFI_up D
  have hD_Tℓ_coe : (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = heckeDivBar hαℓ hβℓ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ D
  have hmk_Tℓ : Pic0.mk D_Tℓ = heckeGen ℓ • (x : JZero (N * q)) :=
    (GluedHecke.heckeGen_smul_mk (N * q) hcommNq ℓ hαℓ hβℓ hFI_up hfin_up hN_up D).symm.trans
      (congrArg (heckeGen ℓ • ·) hmkD)
  have hH' : Pic0.mk D_Tℓ ∈ inertiaInvariants A (N * q) := hmk_Tℓ ▸ hx
  have hx'_eq : (⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ : ↥(inertiaInvariants A (N * q)))
      = ⟨Pic0.mk D_Tℓ, hH'⟩ := Subtype.ext hmk_Tℓ.symm

  have hgood_Tℓ : P.IsGoodDiv
      (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    hD_Tℓ_coe ▸ hgoodD'
  have hadm_Tℓ : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tℓ
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [show P.glueData _ (D_Tℓ : Divisor _ _) = P.glueData _ (heckeDivBar hαℓ hβℓ ↑D) from
      congrArg (P.glueData _) hD_Tℓ_coe]
    exact hadmD'
  have hspD' : sp ⟨Pic0.mk D_Tℓ, hH'⟩
        = GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tℓ, hadm_Tℓ⟩ :=
    hsp D_Tℓ hH' ⟨P.glueData _ D_Tℓ, hadm_Tℓ⟩ hgood_Tℓ rfl

  have hdeg_rF : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (w.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα).deg = w.deg :=
    fun w => (ModularCurve.deg_eq_one_modularFunctionFieldBar N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) w).symm
  have hdeg_sp : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (P.sp w).deg = w.deg :=
    fun w => (ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar N w).symm

  have hfstD_degZ : P.fstDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))) := by

    have h1 : Divisor.degree (Finsupp.mapDomain P.reduceFst
        (P.fstDiv (D : Divisor _ _))) = 0 := hadmD.1
    rw [Divisor.mem_degZero]
    have hdeg_rFst : ∀ w, (P.reduceFst w).deg = w.deg := fun w =>
      (ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) w).symm
    rwa [GluedHecke.degree_mapDomain_of_deg_eq P.reduceFst hdeg_rFst] at h1

  let rF : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (·.restrictAlong (heckeAlphaBar (AlgebraicClosure ℚ) N q) hα)
  let E_N : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))) :=
    ⟨Finsupp.mapDomain rF (P.fstDiv ↑D),
      (GluedHecke.degree_mapDomain_of_deg_eq rF hdeg_rF (P.fstDiv ↑D)).trans hfstD_degZ⟩

  have hcompat_EN := P.spPic0_compat E_N
  obtain ⟨D₀, hD₀_coe, hD₀_sp⟩ := hcompat_EN

  let E'_N := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hβℓN hαℓN hFI_dn E_N
  have hE'_N_coe : (E'_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = heckeDivBar hαℓN hβℓN
          (E_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ E_N
  have hmkE' : Pic0.mk E'_N = heckeGen ℓ • Pic0.mk E_N :=
    (GluedHecke.heckeGen_smul_mk N hcommN ℓ hαℓN hβℓN hFI_dn hfin_dn hN_dn E_N).symm
  have hcompat_E'N := P.spPic0_compat E'_N
  obtain ⟨D'', hD''_coe, hD''_sp⟩ := hcompat_E'N

  have hG1 := (ModularCurve.mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne N q hq ℓ hℓq hα hβ hαℓ hβℓ hαℓN hβℓN (P.fstDiv ↑D)).1

  have hreduce_comp : ∀ (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      Finsupp.mapDomain P.reduceFst X = Finsupp.mapDomain P.sp (Finsupp.mapDomain rF X) :=
    fun X => (congrArg (Finsupp.mapDomain · X) (rfl : P.reduceFst = P.sp ∘ rF)).trans
      Finsupp.mapDomain_comp

  have hA1 : P.fstDiv (↑D_Tℓ : Divisor _ _) = heckeDivBar hαℓ hβℓ (P.fstDiv ↑D) :=
    (congrArg P.fstDiv hD_Tℓ_coe).trans hfst
  have hA2 : Finsupp.mapDomain rF (P.fstDiv ↑D_Tℓ)
      = heckeDivBar hαℓN hβℓN (E_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    (congrArg (Finsupp.mapDomain rF) hA1).trans hG1
  have hA3 : Finsupp.mapDomain P.sp (Finsupp.mapDomain rF (P.fstDiv ↑D_Tℓ))
      = (D'' : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (congrArg (Finsupp.mapDomain P.sp) (hA2.trans hE'_N_coe.symm)).trans hD''_coe.symm
  have hdivA : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (↑D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).1
      = (D'' : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (hreduce_comp (P.fstDiv ↑D_Tℓ)).trans hA3

  have hdivB : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (↑D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).1
      = (D₀ : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (hreduce_comp (P.fstDiv ↑D)).trans hD₀_coe.symm

  have hC1 : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).1
      = Pic0.mk
          ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D_Tℓ).1,
            hadm_Tℓ.1⟩ :=
    congrArg (Prod.fst ∘ GluedPic0.toPic0Pair _)
      ((congrArg sp hx'_eq).trans hspD')
  have hC2 : Pic0.mk
        ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D_Tℓ).1,
          hadm_Tℓ.1⟩
      = Pic0.mk D'' :=
    congrArg Pic0.mk (Subtype.ext hdivA)
  have hC3 : P.spPic0 (Pic0.mk E'_N)
      = heckeGen ℓ • Pic0.mk D₀ :=
    ((congrArg P.spPic0 hmkE').trans (hmod (heckeGen ℓ) (Pic0.mk E_N))).trans
      (congrArg (heckeGen ℓ • ·) hD₀_sp)
  have hC : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).1
      = heckeGen ℓ • Pic0.mk D₀ :=
    ((hC1.trans hC2).trans hD''_sp.symm).trans hC3

  have hD1 : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp x)).1
      = Pic0.mk
          ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D).1,
            hadmD.1⟩ :=
    congrArg (Prod.fst ∘ GluedPic0.toPic0Pair _)
      ((congrArg sp hx_eq).trans hspD)
  have hD2 : Pic0.mk
        ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D).1,
          hadmD.1⟩
      = Pic0.mk D₀ :=
    congrArg Pic0.mk (Subtype.ext hdivB)
  have hD_eq : (heckeGen ℓ •
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          (sp x)).1
      = heckeGen ℓ • Pic0.mk D₀ :=
    (Prod.smul_fst (heckeGen ℓ)
        (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          (sp x))).trans
      (congrArg (heckeGen ℓ • ·) (hD1.trans hD2))
  exact hC.trans hD_eq.symm

private theorem GluedHecke.comp_snd (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (modP : Module HeckeAlg (Pic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hmod :         (∀ (T : HeckeAlg) (y : JZero N), P.spPic0 (T • y) = T • P.spPic0 y))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp)
      (ℓ : Nat.Primes) (hℓN : (ℓ : ℕ) ∣ N) (hℓq : (ℓ : ℕ) ≠ q)
      (x : ↥(inertiaInvariants A (N * q)))
      (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q))
      (hcomp : comp x = 0),
        letI := modP
        (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).2 =
          (heckeGen ℓ •
            GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
              (sp x)).2 := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp modP hmod hsurj hker hsp ℓ hℓN hℓq x hx hcomp
  have _ := hℓN
  letI := modP
  have _ := hstab; have _ := hsurj; have _ := e; have _ := hW

  have hcommNq := ModularCurve.heckeOperatorsCommuteBar (N * q)
  have hcommN := ModularCurve.heckeOperatorsCommuteBar N
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  haveI : Fact (ℓ : ℕ).Prime := ⟨ℓ.2⟩
  have hin_up := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) (N * q) (ℓ : ℕ)
  have hin_down := ModularCurve.heckeInputsAlong_of_prime (AlgebraicClosure ℚ) N (ℓ : ℕ)
  obtain ⟨hαℓ, hβℓ, _, hfin_up, hFI_up, hN_up⟩ := hin_up
  obtain ⟨hαℓN, hβℓN, _, hfin_dn, hFI_dn, hN_dn⟩ := hin_down
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional ((N * q) * (ℓ : ℕ))
  haveI : HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (N * (ℓ : ℕ))

  have hgood_x : P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
      (x : JZero (N * q)) := (hker x).1 hcomp
  have hMplus := ModularCurve.PlaceSpecialization.exists_good_admissible_rep_heckeDivBar_good_admissible_kindResp_of_isModel N q hq hqN A hA W hW data hKr hα hβ P R hR hRL hNV hO ℓ hℓq hαℓ hβℓ
    (x : JZero (N * q)) hgood_x
  obtain ⟨D, hgoodD, hadmD, hmkD, hgoodD', hadmD', hfst, hsnd⟩ := hMplus
  have _ := hfst

  have hH : Pic0.mk D ∈ inertiaInvariants A (N * q) := hmkD ▸ x.2
  have hx_eq : x = ⟨Pic0.mk D, hH⟩ := Subtype.ext hmkD.symm
  have hspD : sp ⟨Pic0.mk D, hH⟩
        = GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D, hadmD⟩ :=
    hsp D hH ⟨P.glueData _ D, hadmD⟩ hgoodD rfl

  let D_Tℓ := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) (N * q) ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) (N * q) ℓ) hβℓ hαℓ hFI_up D
  have hD_Tℓ_coe : (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      = heckeDivBar hαℓ hβℓ (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ D
  have hmk_Tℓ : Pic0.mk D_Tℓ = heckeGen ℓ • (x : JZero (N * q)) :=
    (GluedHecke.heckeGen_smul_mk (N * q) hcommNq ℓ hαℓ hβℓ hFI_up hfin_up hN_up D).symm.trans
      (congrArg (heckeGen ℓ • ·) hmkD)
  have hH' : Pic0.mk D_Tℓ ∈ inertiaInvariants A (N * q) := hmk_Tℓ ▸ hx
  have hx'_eq : (⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩ : ↥(inertiaInvariants A (N * q)))
      = ⟨Pic0.mk D_Tℓ, hH'⟩ := Subtype.ext hmk_Tℓ.symm

  have hgood_Tℓ : P.IsGoodDiv
      (D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))) :=
    hD_Tℓ_coe ▸ hgoodD'
  have hadm_Tℓ : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tℓ
      ∈ GluingData.admissible (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) := by
    rw [show P.glueData _ (D_Tℓ : Divisor _ _) = P.glueData _ (heckeDivBar hαℓ hβℓ ↑D) from
      congrArg (P.glueData _) hD_Tℓ_coe]
    exact hadmD'
  have hspD' : sp ⟨Pic0.mk D_Tℓ, hH'⟩
        = GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
            ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) D_Tℓ, hadm_Tℓ⟩ :=
    hsp D_Tℓ hH' ⟨P.glueData _ D_Tℓ, hadm_Tℓ⟩ hgood_Tℓ rfl

  have hdeg_rS : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
      (w.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ).deg = w.deg :=
    fun w => (ModularCurve.deg_eq_one_modularFunctionFieldBar N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) w).symm
  have hdeg_sp : ∀ w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      (P.sp w).deg = w.deg :=
    fun w => (ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar N w).symm

  have hsndD_degZ : P.sndDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
      ∈ Divisor.degZero (K := AlgebraicClosure ℚ)
        (F := ↥(modularFunctionFieldBar (N * q))) := by

    have h1 : Divisor.degree (Finsupp.mapDomain P.reduceSnd
        (P.sndDiv (D : Divisor _ _))) = 0 := hadmD.2.1
    rw [Divisor.mem_degZero]
    have hdeg_rSst : ∀ w, (P.reduceSnd w).deg = w.deg := fun w =>
      (ModularCurve.place_deg_eq_one_of_isAlgClosed (ResidueField A) N _).trans (ModularCurve.deg_eq_one_modularFunctionFieldBar (N * q) w).symm
    rwa [GluedHecke.degree_mapDomain_of_deg_eq P.reduceSnd hdeg_rSst] at h1

  let rS : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))
      → Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N) :=
    (·.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
  let E_N : ↥(Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar N))) :=
    ⟨Finsupp.mapDomain rS (P.sndDiv ↑D),
      (GluedHecke.degree_mapDomain_of_deg_eq rS hdeg_rS (P.sndDiv ↑D)).trans hsndD_degZ⟩

  have hcompat_EN := P.spPic0_compat E_N
  obtain ⟨D₀, hD₀_coe, hD₀_sp⟩ := hcompat_EN

  let E'_N := Pic0.degZeroCorrespondence (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
      (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ) hβℓN hαℓN hFI_dn E_N
  have hE'_N_coe : (E'_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
      = heckeDivBar hαℓN hβℓN
          (E_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    Pic0.coe_degZeroCorrespondence _ _ _ _ _ E_N
  have hmkE' : Pic0.mk E'_N = heckeGen ℓ • Pic0.mk E_N :=
    (GluedHecke.heckeGen_smul_mk N hcommN ℓ hαℓN hβℓN hFI_dn hfin_dn hN_dn E_N).symm
  have hcompat_E'N := P.spPic0_compat E'_N
  obtain ⟨D'', hD''_coe, hD''_sp⟩ := hcompat_E'N

  have hG2 := (ModularCurve.mapDomain_restrictAlong_degeneracy_heckeDivBar_comm_of_ne N q hq ℓ hℓq hα hβ hαℓ hβℓ hαℓN hβℓN (P.sndDiv ↑D)).2

  have hreduce_comp : ∀ (X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
      Finsupp.mapDomain P.reduceSnd X = Finsupp.mapDomain P.sp (Finsupp.mapDomain rS X) :=
    fun X => (congrArg (Finsupp.mapDomain · X) (rfl : P.reduceSnd = P.sp ∘ rS)).trans
      Finsupp.mapDomain_comp

  have hA1 : P.sndDiv (↑D_Tℓ : Divisor _ _) = heckeDivBar hαℓ hβℓ (P.sndDiv ↑D) :=
    (congrArg P.sndDiv hD_Tℓ_coe).trans hsnd
  have hA2 : Finsupp.mapDomain rS (P.sndDiv ↑D_Tℓ)
      = heckeDivBar hαℓN hβℓN (E_N : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :=
    (congrArg (Finsupp.mapDomain rS) hA1).trans hG2
  have hA3 : Finsupp.mapDomain P.sp (Finsupp.mapDomain rS (P.sndDiv ↑D_Tℓ))
      = (D'' : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (congrArg (Finsupp.mapDomain P.sp) (hA2.trans hE'_N_coe.symm)).trans hD''_coe.symm
  have hdivA : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (↑D_Tℓ : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.1
      = (D'' : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (hreduce_comp (P.sndDiv ↑D_Tℓ)).trans hA3

  have hdivB : (P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (↑D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))).2.1
      = (D₀ : Divisor (ResidueField A) (modularFunctionFieldC (ResidueField A) N)) :=
    (hreduce_comp (P.sndDiv ↑D)).trans hD₀_coe.symm

  have hC1 : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).2
      = Pic0.mk
          ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D_Tℓ).2.1,
            hadm_Tℓ.2.1⟩ :=
    congrArg (Prod.snd ∘ GluedPic0.toPic0Pair _)
      ((congrArg sp hx'_eq).trans hspD')
  have hC2 : Pic0.mk
        ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D_Tℓ).2.1,
          hadm_Tℓ.2.1⟩
      = Pic0.mk D'' :=
    congrArg Pic0.mk (Subtype.ext hdivA)
  have hC3 : P.spPic0 (Pic0.mk E'_N)
      = heckeGen ℓ • Pic0.mk D₀ :=
    ((congrArg P.spPic0 hmkE').trans (hmod (heckeGen ℓ) (Pic0.mk E_N))).trans
      (congrArg (heckeGen ℓ • ·) hD₀_sp)
  have hC : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩)).2
      = heckeGen ℓ • Pic0.mk D₀ :=
    ((hC1.trans hC2).trans hD''_sp.symm).trans hC3

  have hD1 : (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp x)).2
      = Pic0.mk
          ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D).2.1,
            hadmD.2.1⟩ :=
    congrArg (Prod.snd ∘ GluedPic0.toPic0Pair _)
      ((congrArg sp hx_eq).trans hspD)
  have hD2 : Pic0.mk
        ⟨(P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) ↑D).2.1,
          hadmD.2.1⟩
      = Pic0.mk D₀ :=
    congrArg Pic0.mk (Subtype.ext hdivB)
  have hD_eq : (heckeGen ℓ •
        GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          (sp x)).2
      = heckeGen ℓ • Pic0.mk D₀ :=
    (Prod.smul_snd (heckeGen ℓ)
        (GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
          (sp x))).trans
      (congrArg (heckeGen ℓ • ·) (hD1.trans hD2))
  exact hC.trans hD_eq.symm

private theorem GluedHecke.smul_eq_zero_of_eq_zero {R M : Type} [Zero M] [SMulZeroClass R M]
    (r : R) {m : M} (h : m = 0) : r • m = 0 := by rw [h, smul_zero]

theorem solution (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (e : Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N) → ℕ)
      (comp : ↥(inertiaInvariants A (N * q)) →+
        componentGroup (widthOfPlaces (arithFrobC q (ResidueField A) N) W e))
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsurj : Function.Surjective comp)
      (hker : ∀ x : ↥(inertiaInvariants A (N * q)),
        comp x = 0 ↔ P.IsGoodClass (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (x : JZero (N * q)))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ ℓ : Nat.Primes, (ℓ : ℕ) ∣ N → (ℓ : ℕ) ≠ q →
          ∀ (x : ↥(inertiaInvariants A (N * q)))
            (hx : heckeGen ℓ • (x : JZero (N * q)) ∈ inertiaInvariants A (N * q)),
            comp x = 0 →
              GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp x) = 0 →
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) = 0) := by
  haveI : NeZero q := ⟨hq.ne_zero⟩
  haveI : Fact q.Prime := ⟨hq⟩
  haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  letI := instDecidableEqResidueFieldSemistable A
  letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
  intro W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp hsurj hker hsp ℓ hℓN hℓq x hx hcomp h0
  obtain ⟨modP, hmod⟩ := GluedHecke.heckeModule_spPic0 N q hq hqN A hA data hKr hα hβ P
  have h1 := GluedHecke.comp_fst N q hq hqN A hA W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp modP hmod
    hsurj hker hsp ℓ hℓN hℓq x hx hcomp
  have h2 := GluedHecke.comp_snd N q hq hqN A hA W hW hstab data hKr hα hβ P R hR hRL hNV hO e comp sp modP hmod
    hsurj hker hsp ℓ hℓN hℓq x hx hcomp
  letI := modP
  have hpair : GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
        (sp ⟨heckeGen ℓ • (x : JZero (N * q)), hx⟩) =
      heckeGen ℓ • GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (sp x) :=
    Prod.ext h1 h2
  exact hpair.trans (GluedHecke.smul_eq_zero_of_eq_zero (heckeGen ℓ) h0)

end
end S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_toPic0Pair_gluedSpecialization_heckeGen_dvd_smul_eq_zero_of_eq_zero_of_isModel (solution)
