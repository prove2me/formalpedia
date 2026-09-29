-- Prove2me | solution 1 for ModularCurve.CharPModel.FibreModel.spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/1c286a52-7a33-508e-b6ed-fda479ebe504

import Definitions.Def_ModularCurve_SpecializationMap
import Mathlib.Algebra.Polynomial.Bivariate
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
import Theorems.Thm_ModularCurve_CharPModel_exists_fibreModel_cuspChart_integrallyClosed
import Theorems.Thm_ModularCurve_CharPModel_exists_integral_lift_jChart_and_jInvChart
import Theorems.Thm_ModularCurve_relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi
import Theorems.Thm_ModularCurve_minpoly_jqN_map_eq_prod_slots
import Theorems.Thm_ModularCurve_minpoly_jqN_eq_toAdjoin
import Theorems.Thm_ModularCurve_phiIrreducible_all
import Theorems.Thm_ModularCurve_finrank_adjoin_jqN_eq_dedekindPsi
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_place_eq_of_forall_finChart_mem_nonunits_iff
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j
import Theorems.Thm_ModularCurve_CharPModel_FibreModel_spPlace_d0_j_pole
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Theorems.Thm_ModularCurve_mapDomain_heckeDivBar_single
import Theorems.Thm_ModularCurve_kroneckerCoordinatewiseDichotomy
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
p2m_attr_erase "instance" "ValuationSubring.instIsAlgClosedResidueField ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree WeierstrassCurve.Affine.Point.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent"
p2m_attr_erase "instance" "ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply ModularCurve.toRingAut_coeffSemilinearAut ModularCurve.baseAut_arithFrobC_apply ModularCurve.coe_coeffRingAut_apply ModularCurve.baseAut_coeffSemilinearAut ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow"
p2m_attr_erase "simp" "ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.veluPointMap2_zero FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.frobeniusPullbackGeomLevelUnconditional_single ModularCurve.frobeniusPushforwardGeomLevelUnconditional_single ModularCurve.frobeniusGeomLevelUnconditional_apply_coe ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one"
p2m_attr_erase "simp" "TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false

p2m_open "ModularCurve~jBar ModularCurve.CharPModel AlgebraicCurve Polynomial"

noncomputable section

namespace J6Spine

local notation "ℚbar" => AlgebraicClosure ℚ
namespace DegBound

section Good

variable {K : Type*} [Field K]

private def Good (B : ℤ) (P : Polynomial (LaurentSeries K)) (n : ℕ) : Prop :=
  ∀ i : ℕ, ((((i : ℤ) - n) * B : ℤ) : WithTop ℤ) ≤ (P.coeff i).orderTop

private theorem le_orderTop_sum {ι : Type*} (s : Finset ι) (f : ι → LaurentSeries K) (e : WithTop ℤ)
    (h : ∀ j ∈ s, e ≤ (f j).orderTop) : e ≤ (∑ j ∈ s, f j).orderTop := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine le_trans ?_ HahnSeries.min_orderTop_le_orderTop_add
    exact le_min (h a (Finset.mem_insert_self a s))
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

private theorem good_one (B : ℤ) : Good B (1 : Polynomial (LaurentSeries K)) 0 := by
  intro i
  rw [coeff_one]
  split_ifs with h
  · subst h; simp
  · simp

private theorem good_mul {B : ℤ} {P Q : Polynomial (LaurentSeries K)} {n m : ℕ}
    (hP : Good B P n) (hQ : Good B Q m) : Good B (P * Q) (n + m) := by
  intro i
  rw [coeff_mul]
  refine le_orderTop_sum _ _ _ fun x hx => ?_
  have hx' : x.1 + x.2 = i := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  refine le_trans ?_ HahnSeries.orderTop_add_le_mul
  refine le_trans ?_ (add_le_add (hP x.1) (hQ x.2))
  rw [← WithTop.coe_add, WithTop.coe_le_coe]
  have : ((i : ℤ) - ↑(n + m)) * B = (((x.1 : ℤ) - n) * B) + (((x.2 : ℤ) - m) * B) := by
    push_cast; rw [← hx']; push_cast; ring
  rw [this]

private theorem good_X_sub_C {B : ℤ} (r : LaurentSeries K)
    (hr : ((-B : ℤ) : WithTop ℤ) ≤ r.orderTop) : Good B (X - C r) 1 := by
  intro i
  rw [coeff_sub, coeff_X, coeff_C]
  rcases Nat.lt_trichotomy i 1 with hi | rfl | hi
  · have hi0 : i = 0 := by omega
    subst hi0
    simp only [↓reduceIte, Nat.cast_zero, zero_sub, neg_mul]
    simpa using hr
  · simp
  · have h1 : (1 : ℕ) ≠ i := by omega
    have h0 : i ≠ 0 := by omega
    rw [if_neg h1, if_neg h0, sub_zero, HahnSeries.orderTop_zero]
    exact le_top

private theorem good_prod {B : ℤ} {ι : Type*} (s : Finset ι) (r : ι → LaurentSeries K)
    (hr : ∀ j ∈ s, ((-B : ℤ) : WithTop ℤ) ≤ (r j).orderTop) :
    Good B (∏ j ∈ s, (X - C (r j))) s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using good_one B
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha, Nat.add_comm]
    exact good_mul (good_X_sub_C _ (hr a (Finset.mem_insert_self a s)))
      (ih fun j hj => hr j (Finset.mem_insert_of_mem hj))

end Good

section Orders

variable (K : Type*) [Field K] [Algebra ℚ K]

private theorem coeffEmb_jq_coeff_of_lt {k : ℤ} (hk : k < -1) : (coeffEmb K jq).coeff k = 0 := by
  rw [coeffEmb_coeff, coeff_jq_of_lt hk, map_zero]

omit [Algebra ℚ K] in
private theorem le_orderTop_qExpand {n : ℕ} [NeZero n] (f : LaurentSeries K) (e : ℤ)
    (hf : ∀ k < e, f.coeff k = 0) :
    (((n : ℤ) * e : ℤ) : WithTop ℤ) ≤ (qExpand K n f).orderTop := by
  rw [HahnSeries.le_orderTop_iff_forall]
  intro j hj
  have hj' : j < (n : ℤ) * e := by exact_mod_cast hj
  by_cases hdvd : (n : ℤ) ∣ j
  · obtain ⟨m, rfl⟩ := hdvd
    rw [qExpand_coeff_mul]
    apply hf
    have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    by_contra hme
    push Not at hme
    have := mul_le_mul_of_nonneg_left hme hn.le
    omega
  · exact qExpand_coeff_of_not_dvd n f hdvd

private theorem le_orderTop_slot (N : ℕ) [NeZero N] (ζ : Kˣ) (a b : ℕ) (ha : a ∈ N.divisors) :
    ((-((N : ℤ) * N) : ℤ) : WithTop ℤ) ≤
      (if h : a = 0 then (0 : LaurentSeries K) else
        letI : NeZero a := ⟨h⟩; qExpand K (a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq))).orderTop := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors ha)
  rw [dif_neg ha0]
  letI : NeZero a := ⟨ha0⟩
  haveI : NeZero (a * a) := ⟨mul_ne_zero ha0 ha0⟩
  have hle : a ≤ N := Nat.divisor_le ha
  have h1 := le_orderTop_qExpand K (n := a * a) (qTwist (ζ ^ (b * a)) (coeffEmb K jq)) (-1)
    (fun k hk => by rw [qTwist_coeff, coeffEmb_jq_coeff_of_lt K hk, mul_zero])
  refine le_trans ?_ h1
  have : -((N : ℤ) * N) ≤ ((a * a : ℕ) : ℤ) * (-1) := by
    have : (a : ℤ) * a ≤ (N : ℤ) * N := by
      have := Nat.mul_le_mul hle hle
      exact_mod_cast this
    push_cast; linarith
  exact_mod_cast this

private theorem coeff_evalAtJ (c : Polynomial ℤ) (k : ℤ) :
    (evalAtJ c).coeff k = ∑ i ∈ Finset.range (c.natDegree + 1), (c.coeff i : ℚ) * (jq ^ i).coeff k := by
  rw [evalAtJ_def]
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [aeval_def, eval₂_eq_sum_range, HahnSeries.coeff_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [show algebraMap ℤ (LaurentSeries ℚ) (c.coeff i) = HahnSeries.C ((c.coeff i : ℚ)) by
      rw [eq_intCast, ← map_intCast (HahnSeries.C : ℚ →+* LaurentSeries ℚ)],
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

private theorem coeff_evalAtJ_neg_natDegree (c : Polynomial ℤ) :
    (evalAtJ c).coeff (-(c.natDegree : ℤ)) = (c.leadingCoeff : ℚ) := by
  rw [coeff_evalAtJ, Finset.sum_eq_single c.natDegree]
  · rw [coeff_jq_pow_self, mul_one, leadingCoeff]
  · intro i hi hne
    have hlt : i < c.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hne
    rw [coeff_jq_pow_of_lt (by omega), mul_zero]
  · intro h; exact absurd (Finset.mem_range.mpr (Nat.lt_succ_self _)) h

private theorem coeff_evalAtJ_of_lt (c : Polynomial ℤ) {k : ℤ} (hk : k < -(c.natDegree : ℤ)) :
    (evalAtJ c).coeff k = 0 := by
  rw [coeff_evalAtJ]
  refine Finset.sum_eq_zero fun i hi => ?_
  have hle : i ≤ c.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [coeff_jq_pow_of_lt (by omega), mul_zero]

end Orders

private theorem main (N : ℕ) [NeZero N] (data : ModularPolynomialData N) (i : ℕ) :
    (data.Φ.coeff i).natDegree ≤ N * (dedekindPsi N - i) := by
  classical
  set c := data.Φ.coeff i with hc_def
  by_cases hc : c = 0
  · rw [hc, natDegree_zero]; exact Nat.zero_le _
  have hiψ : i ≤ dedekindPsi N := by
    rw [← data.natDegree_eq]; exact le_natDegree_of_ne_zero hc

  have hN0 : N ≠ 0 := NeZero.ne N
  set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / N) with hζ_def
  have hζ : IsPrimitiveRoot ζ N := Complex.isPrimitiveRoot_exp N hN0
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hN0
  have hζu : IsPrimitiveRoot ((Units.mk0 ζ hζ0 : ℂˣ) : ℂ) N := by simpa using hζ

  have hprod := minpoly_jqN_map_eq_prod_slots (K := ℂ) N (Units.mk0 ζ hζ0) hζu
    (fun d _ _ => ⟨finrank_adjoin_jqN_eq_dedekindPsi d, modularFunctionField_eq_full d⟩)
  rw [minpoly_jqN_eq_toAdjoin data (phiIrreducible_all N data), Finset.prod_sigma'] at hprod
  set φ : (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) →+* LaurentSeries ℂ :=
    ((coeffEmb ℂ).comp (qExpand ℚ N)).comp
      (algebraMap (IntermediateField.adjoin ℚ ({jq} : Set (LaurentSeries ℚ))) (LaurentSeries ℚ))
    with hφ
  set S := N.divisors.sigma fun a =>
    (Finset.range (N / a)).filter (fun b => Nat.gcd (Nat.gcd a b) (N / a) = 1) with hS
  set r : (Σ _ : ℕ, ℕ) → LaurentSeries ℂ := fun x =>
    if h : x.1 = 0 then 0 else
      letI : NeZero x.1 := ⟨h⟩; qExpand ℂ (x.1 * x.1) (qTwist ((Units.mk0 ζ hζ0) ^ (x.2 * x.1))
        (coeffEmb ℂ jq)) with hr
  have hprod' : data.toAdjoin.map φ = ∏ x ∈ S, (X - C (r x)) := hprod

  have hcard : S.card = dedekindPsi N := by
    have h1 := congrArg natDegree hprod'
    rw [natDegree_finsetProd_X_sub_C_eq_card, (data.toAdjoin_monic).natDegree_map,
      ModularPolynomialData.toAdjoin, (data.monic).natDegree_map, data.natDegree_eq] at h1
    exact h1.symm

  set y : LaurentSeries ℂ := coeffEmb ℂ (qExpand ℚ N (evalAtJ c)) with hy
  have hyeq : y = (∏ x ∈ S, (X - C (r x))).coeff i := by
    rw [← hprod', coeff_map, ModularPolynomialData.toAdjoin, coeff_map, hy, hφ]
    simp only [RingHom.coe_comp, Function.comp_apply]
    congr 2
    have := congrArg (fun f : Polynomial ℤ →+* LaurentSeries ℚ => f c) algebraMap_comp_evalAtJGen
    simpa using this.symm

  have hgood := good_prod (K := ℂ) (B := (N : ℤ) * N) S r fun x hx => by
    have hx1 : x.1 ∈ N.divisors := (Finset.mem_sigma.mp hx).1
    exact le_orderTop_slot ℂ N (Units.mk0 ζ hζ0) x.1 x.2 hx1
  have hlow : ((((i : ℤ) - dedekindPsi N) * ((N : ℤ) * N) : ℤ) : WithTop ℤ) ≤ y.orderTop := by
    rw [hyeq, ← hcard]; exact hgood i

  have hcoeff : y.coeff ((N : ℤ) * (-(c.natDegree : ℤ))) ≠ 0 := by
    rw [hy, coeffEmb_coeff, qExpand_coeff_mul, coeff_evalAtJ_neg_natDegree]
    simp only [ne_eq, map_eq_zero, Int.cast_eq_zero, leadingCoeff_eq_zero]
    exact hc
  have hup : y.orderTop ≤ (((N : ℤ) * (-(c.natDegree : ℤ)) : ℤ) : WithTop ℤ) :=
    HahnSeries.orderTop_le_of_coeff_ne_zero hcoeff
  have hineq := WithTop.coe_le_coe.mp (hlow.trans hup)

  have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN0
  have h1 : ((c.natDegree : ℤ)) * N ≤ ((dedekindPsi N : ℤ) - i) * N * N := by nlinarith
  have h2 : (c.natDegree : ℤ) ≤ ((dedekindPsi N : ℤ) - i) * N :=
    le_of_mul_le_mul_right (by nlinarith) hNpos
  have h3 : (c.natDegree : ℤ) ≤ ((N * (dedekindPsi N - i) : ℕ) : ℤ) := by
    push_cast [Nat.cast_sub hiψ]; linarith
  exact_mod_cast h3

end DegBound

section FibreSide

variable (k : Type*) [Field k] (N : ℕ) [NeZero N] {ℓ : ℕ} [Fact ℓ.Prime] [CharP k ℓ]
  (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)

private abbrev jt : modularFunctionFieldC k N := ⟨jqModC k, jqModC_mem k N⟩

omit [Fact ℓ.Prime] [CharP k ℓ] in
private theorem jt_ne_zero : (jt k N : modularFunctionFieldC k N) ≠ 0 := by
  intro h
  have h' : jqModC k = 0 := congrArg Subtype.val h
  exact transcendental_jqModC k (h' ▸ isAlgebraic_zero)

private def IsCuspK (v : Place k (modularFunctionFieldC k N)) : Prop := v.ord (jt k N) < 0

omit [Fact ℓ.Prime] [CharP k ℓ] in
private theorem isCuspK_iff_not_mem (v : Place k (modularFunctionFieldC k N)) :
    IsCuspK k N v ↔ (jt k N : modularFunctionFieldC k N) ∉ v.toValuationSubring := by
  rw [IsCuspK, v.mem_iff_ord_nonneg (jt_ne_zero k N), not_le]

include hKr in
private theorem isCuspK_frob_iff (v : Place k (modularFunctionFieldC k N)) :
    IsCuspK k N (frobOnPlacesGeomLevel k N data hKr v) ↔ IsCuspK k N v := by
  rw [isCuspK_iff_not_mem, isCuspK_iff_not_mem, not_iff_not, mem_frobOnPlacesGeomLevel_iff,
    frobeniusGeomLevel_jq]
  exact (mem_valuationSubring_iff_pow_mem (ℓ := ℓ) v.toValuationSubring _).symm

end FibreSide

section Honest

variable (N : ℕ) [NeZero N] (A : ValuationSubring ℚbar) (ℓ : ℕ) [Fact ℓ.Prime]
  (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)

private theorem exists_honest (hred : Function.Surjective red) (hℓN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData N) :
    ∃ fm₀ : FibreModel N A ℓ k red, fm₀.CuspChart ∧
      IsIntegrallyClosed fm₀.BFin ∧ IsIntegrallyClosed fm₀.BInf := by
  have hlift := exists_integral_lift_jChart_and_jInvChart N A ℓ hℓN k red hred
  exact exists_fibreModel_cuspChart_integrallyClosed N A ℓ k red hred data
    (relfinrank_adjoin_jqModC_modularFunctionFieldC_eq_dedekindPsi k N ℓ hℓN)
    (fun i => DegBound.main N data i)
    hlift.1 hlift.2

end Honest

section Swap

variable {N : ℕ} [NeZero N] {A : ValuationSubring ℚbar} {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

private def swap (fm fm₀ : FibreModel N A ℓ k red) : FibreModel N A ℓ k red where
  BFin := fm.BFin
  BInf := fm₀.BInf
  constFin_mem := fm.constFin_mem
  constInf_mem := fm₀.constInf_mem
  jBar_mem := fm.jBar_mem
  jNBar_mem := fm.jNBar_mem
  jInvBar_mem := fm₀.jInvBar_mem
  integralFin := fm.integralFin
  integralInf := fm₀.integralInf
  piFin := fm.piFin
  piInf := fm₀.piInf
  piFin_const := fm.piFin_const
  piInf_const := fm₀.piInf_const
  piFin_j := fm.piFin_j
  piFin_jN := fm.piFin_jN
  piInf_jInv := fm₀.piInf_jInv
  ker_piFin := fm.ker_piFin
  ker_piInf := fm₀.ker_piInf
  intClosed_piFin := fm.intClosed_piFin
  intClosed_piInf := fm₀.intClosed_piInf
  frac_piFin := fm.frac_piFin
  frac_piInf := fm₀.frac_piInf

private theorem swap_cuspChart (fm fm₀ : FibreModel N A ℓ k red) (cc₀ : fm₀.CuspChart) :
    (swap fm fm₀).CuspChart :=
  ⟨cc₀.tBar_mem, cc₀.piInf_t⟩

end Swap

section Branches

variable {N : ℕ} [NeZero N] {A : ValuationSubring ℚbar} {ℓ : ℕ} [Fact ℓ.Prime]
  {k : Type*} [Field k] [CharP k ℓ] {red : A →+* k}

variable (N A) in

private def FinBr (w : Place ℚbar (modularFunctionFieldBar N)) : Prop :=
  ∃ a : A, 0 < w.ord (jBar N - algebraMap ℚbar (modularFunctionFieldBar N) (a : ℚbar))

variable (N A) in
private theorem not_fin_iff (w : Place ℚbar (modularFunctionFieldBar N)) :
    ¬ FinBr N A w ↔
      ∀ a : A, w.ord (jBar N - algebraMap ℚbar (modularFunctionFieldBar N) (a : ℚbar)) ≤ 0 := by
  simp [FinBr]

omit [Fact ℓ.Prime] [CharP k ℓ] in

private theorem jt_mem_of_ord_pos (v : Place k (modularFunctionFieldC k N)) (c : k)
    (h : 0 < v.ord (jt k N - algebraMap k (modularFunctionFieldC k N) c)) :
    (jt k N : modularFunctionFieldC k N) ∈ v.toValuationSubring := by
  have hne : (jt k N - algebraMap k (modularFunctionFieldC k N) c) ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem := v.mem_of_ord_nonneg hne h.le
  have hc : algebraMap k (modularFunctionFieldC k N) c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have := add_mem hmem hc
  simpa using this

private theorem spPlace_swap_of_fin (fm fm₀ : FibreModel N A ℓ k red)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (w : Place ℚbar (modularFunctionFieldBar N)) (hw : FinBr N A w) :
    (swap fm fm₀).spPlace hred dataAll hsep w = fm.spPlace hred dataAll hsep w := by
  obtain ⟨a₀, ha₀⟩ := hw
  refine FibreModel.place_eq_of_forall_finChart_mem_nonunits_iff N ℓ A k red fm hred dataAll
    hsep _ _ ?_ ?_ ?_
  · exact jt_mem_of_ord_pos _ (red a₀)
      (FibreModel.spPlace_d0_j N A ℓ k red (swap fm fm₀) hred dataAll hsep w a₀ ha₀)
  · exact jt_mem_of_ord_pos _ (red a₀)
      (FibreModel.spPlace_d0_j N A ℓ k red fm hred dataAll hsep w a₀ ha₀)
  · intro b
    exact ((swap fm fm₀).piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀ b).trans
      (fm.piFin_mem_spPlace_nonunits_iff hred dataAll hsep w a₀ ha₀ b).symm

end Branches

end J6Spine

end

p2m_open "ModularCurve~jBar ModularCurve.CharPModel AlgebraicCurve Polynomial"

private theorem j6_finBr_support_heckeDivBar
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
        (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) (hv : J6Spine.FinBr N A v) :
    ∀ w ∈ (heckeDivBar halpha hbeta (Finsupp.single v 1)).support, J6Spine.FinBr N A w := by
  classical
  haveI : NeZero ℓ := ⟨(Fact.out : ℓ.Prime).ne_zero⟩
  intro w hw
  have hexp := ModularCurve.mapDomain_heckeDivBar_single halpha hbeta id v 1
  rw [Finsupp.mapDomain_id] at hexp
  rw [hexp, Finsupp.mem_support_iff, Finsupp.finsetSum_apply] at hw
  obtain ⟨W, hW, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hw
  obtain ⟨rfl, -⟩ := Finsupp.single_apply_ne_zero.mp hne
  by_contra hnf
  have hβ := ((ModularCurve.kroneckerCoordinatewiseDichotomy A ℓ N k red halpha hbeta W).2.1).mp
    ((J6Spine.not_fin_iff N A _).mp hnf)
  rw [Place.mem_fiberAlong.mp hW] at hβ
  exact (J6Spine.not_fin_iff N A v).mpr hβ hv

theorem solution
    (A : ValuationSubring (AlgebraicClosure ℚ)) (ℓ N : ℕ) [Fact ℓ.Prime] [NeZero N]
    (hlN : ¬ ℓ ∣ N)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (red : A →+* k)
    (halpha : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hbeta : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N ℓ)
    (hred : Function.Surjective red)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable)
    (fm : FibreModel N A ℓ k red)
    [HasPrincipalDivisors (AlgebraicClosure ℚ)
      (laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull (N * ℓ)))]
    (v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (s t : k)
    (hs : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqModC k, jqModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) s))
    (ht : 0 < ((fm.spPlace hred dataAll hsep) v).ord (⟨jqNModC k N, jqNModC_mem k N⟩
      - algebraMap k (modularFunctionFieldC k N) t)) :
    fm.spDiv hred dataAll hsep (heckeDivBar halpha hbeta (Finsupp.single v 1))
      = heckeFibreGeomLevel k N data hKr
          (Finsupp.single ((fm.spPlace hred dataAll hsep) v) 1) := by
  classical
  have _ := ht

  obtain ⟨fm₀, cc₀, -, -⟩ := J6Spine.exists_honest N A ℓ k red hred hlN (dataAll N (dvd_refl N))
  have cc' : (J6Spine.swap fm fm₀).CuspChart := J6Spine.swap_cuspChart fm fm₀ cc₀

  have hv : J6Spine.FinBr N A v := by
    by_contra hnf
    have hpole := FibreModel.spPlace_d0_j_pole N A ℓ k red fm hred dataAll hsep v
      ((J6Spine.not_fin_iff N A v).mp hnf)
    have hmem := J6Spine.jt_mem_of_ord_pos (k := k) (N := N) ((fm.spPlace hred dataAll hsep) v) s hs
    have h0 : 0 ≤ ((fm.spPlace hred dataAll hsep) v).ord (J6Spine.jt k N) :=
      (((fm.spPlace hred dataAll hsep) v).mem_iff_ord_nonneg (J6Spine.jt_ne_zero k N)).mp hmem
    exact absurd h0 (not_le.mpr hpole)
  have hfib := j6_finBr_support_heckeDivBar A ℓ N k red halpha hbeta v hv

  have hL1 := ModularCurve.CharPModel.FibreModel.mapDomain_spPlace_heckeDivBar_of_cuspChart_of_level
    A ℓ N hlN data hKr k red halpha hbeta hred dataAll hsym hsep
    (J6Spine.swap fm fm₀) cc' (Finsupp.single v 1)

  show Finsupp.mapDomain (fm.spPlace hred dataAll hsep) _ = _
  rw [Finsupp.mapDomain_congr (fun w hw =>
        (J6Spine.spPlace_swap_of_fin fm fm₀ hred dataAll hsep w (hfib w hw)).symm),
    hL1, Finsupp.mapDomain_single, J6Spine.spPlace_swap_of_fin fm fm₀ hred dataAll hsep v hv]

end S_ModularCurve_CharPModel_FibreModel_spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level
end P2MW
export P2MW.S_ModularCurve_CharPModel_FibreModel_spDiv_heckeDivBar_eq_heckeFibreGeomLevel_of_finiteCentre_of_level (solution)
