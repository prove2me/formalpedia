-- Prove2me | solution 1 for ModularCurve.exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/ab8e7f40-4753-565c-bc43-01d9b2a29e2b

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_HeckeGalois_EichlerShimura
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_ModularCurve_JZeroTateModule
import Theorems.Thm_ModularCurve_exists_galoisRepAdic_charpoly_frobenius_of_heckeChar
import Definitions.Def_GaloisRep_FrobeniusPowerDense
import Theorems.Thm_FrobeniusDensity_frobeniusPowerDense_of_le_ker
import Theorems.Thm_ModularCurve_exists_semisimple_descent_of_trace_det_mem_range_finite
import Theorems.Thm_Representation_span_range_eq_top_of_isIrreducible
import Mathlib.Data.Matrix.Basis
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Theorems.Thm_ModularCurve_moduleFinite_padicInt_tateModule_jZero
import Theorems.Thm_ModularCurve_JZero_divisible
import Theorems.Thm_ModularCurve_moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero
import Theorems.Thm_integralClosure_finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel"
p2m_attr_erase "instance" "AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par"
p2m_attr_erase "instance" "HeckeEis.instAddCommGroupCoeffH1par AlgebraicCurve.CellDissection.fintypeV AlgebraicCurve.CellDissection.fintypeC AlgebraicCurve.CellDissection.fintypeE AlgebraicCurve.CellDissection.decEqV AlgebraicCurve.CellDissection.decEqC AlgebraicCurve.CellDissection.decEqE ValuationSubring.instIsAlgClosedResidueField WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular FrobeniusDensity.isMaximal_ratPrimeIdeal FrobeniusDensity.liesOver_ratBelow"
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff"
p2m_attr_erase "simp" "ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero"
p2m_attr_erase "simp" "HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.DivisorialWeilPairingData.toChar_apply AlgebraicCurve.WeilDatum.coe_classRight AlgebraicCurve.WeilDatum.coe_degZeroRight AlgebraicCurve.DivisorialWeilPairingData.mk.sizeOf_spec AlgebraicCurve.WeilDatum.coe_classLeft AlgebraicCurve.WeilDatum.coe_degZeroLeft AlgebraicCurve.DivisorialWeilPairingData.mk.injEq AlgebraicCurve.DivisorialWeilPairingData.toHom_apply_apply AlgebraicCurve.WeilDatum.mk.sizeOf_spec AlgebraicCurve.WeilDatum.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_zero AlgebraicCurve.PrincipalPolarization.mk.injEq AlgebraicCurve.WeilPairingData.evalAddChar_apply AlgebraicCurve.H1Gm.degree_ofPic0 AlgebraicCurve.WeilPairingData.mk.sizeOf_spec AlgebraicCurve.HomPic0Gm.map_one AlgebraicCurve.PrincipalPolarization.mk.sizeOf_spec AlgebraicCurve.WeilPairingData.autodualityEquiv_apply AlgebraicCurve.WeilPairingData.eval_zero_right AlgebraicCurve.H1Gm.ofPic0_mk AlgebraicCurve.WeilPairingData.eval_neg_left AlgebraicCurve.HomPic0Gm.map_apply AlgebraicCurve.H1Gm.degree_mk AlgebraicCurve.HomPic0Gm.map_id AlgebraicCurve.WeilPairingData.mk.injEq AlgebraicCurve.WeilPairingData.congr_eval AlgebraicCurve.WeilPairingData.eval_neg_right AlgebraicCurve.WeilPairingData.eval_zero_left AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap ModularCurve.tateMap_apply AlgebraicCurve.abelJacobiDiv_single AlgebraicCurve.AnalyticCoord.mk.injEq"
p2m_attr_erase "simp" "AlgebraicCurve.Cell.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.sizeOf_spec AlgebraicCurve.RadialRegion.mk.injEq AlgebraicCurve.CellDissection.mk.sizeOf_spec AlgebraicCurve.Cell.mk.injEq AlgebraicCurve.CellDissection.mk.injEq AlgebraicCurve.AnalyticCoord.mk.sizeOf_spec ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ValuationSubring.reduceAt_coe ValuationSubring.reduceAt_one ValuationSubring.reduceAt_natCast ValuationSubring.reduceAt_intCast ValuationSubring.reduceAt_zero ModularCurve.coe_uniformizerMod ModularCurve.qSeriesBar_jModElt ModularCurve.qInftyPlaceMod_toValuationSubring WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve~baseChangeHom"
open scoped TensorProduct

private theorem finite_int_transfer {G : Type*} [AddCommGroup G] {i₁ i₂ : Module ℤ G}
    (h : @Module.Finite ℤ G _ _ i₁) : @Module.Finite ℤ G _ _ i₂ := by
  obtain rfl : i₁ = i₂ := Subsingleton.elim _ _
  exact h

private theorem exists_point_of_ne_bot (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg)
    (hsupp : letI := heckeModuleBar M; heckeTorsion (JZero M) 𝔪 ≠ ⊥) :
    letI := heckeModuleBar M
    ∃ x : JZero M, x ≠ 0 ∧ ∀ m ∈ 𝔪, m • x = 0 := by
  letI := heckeModuleBar M
  obtain ⟨x, hx𝔪, hx0⟩ := (Submodule.ne_bot_iff _).mp hsupp
  exact ⟨x, hx0, (mem_heckeTorsion_iff (JZero M) 𝔪 x).mp hx𝔪⟩

private theorem exists_prime_natCast_mem (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg) [h𝔪 : 𝔪.IsMaximal]
    (hsupp : letI := heckeModuleBar M; heckeTorsion (JZero M) 𝔪 ≠ ⊥) :
    Finite (HeckeAlg ⧸ 𝔪) ∧ ∃ p : ℕ, p.Prime ∧ ((p : ℕ) : HeckeAlg) ∈ 𝔪 := by
  letI := heckeModuleBar M
  haveI hfin : Module.Finite ℤ (HeckeAlg ⧸ Module.annihilator HeckeAlg (JZero M)) :=
    moduleFinite_int_heckeAlg_quotient_annihilator_jZero_of_neZero M
  obtain ⟨x, hx0, hkill⟩ := exists_point_of_ne_bot M 𝔪 hsupp
  have hle : Module.annihilator HeckeAlg (JZero M) ≤ 𝔪 := by
    intro a ha
    by_contra ha𝔪
    obtain ⟨y, i, hi, hyi⟩ := h𝔪.exists_inv ha𝔪
    apply hx0
    calc x = (y * a + i) • x := by rw [hyi, one_smul]
      _ = 0 := by rw [add_smul, mul_smul, Module.mem_annihilator.mp ha x, smul_zero, hkill i hi, add_zero]
  have hsurj : Function.Surjective (Ideal.Quotient.factor hle).toIntAlgHom.toLinearMap := by
    intro z
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective z
    exact ⟨Ideal.Quotient.mk _ t, Ideal.Quotient.factor_mk hle t⟩
  haveI : @Module.Finite ℤ (HeckeAlg ⧸ Module.annihilator HeckeAlg (JZero M)) _ _
      (@Algebra.toModule ℤ _ _ _ _) := finite_int_transfer hfin
  haveI : @Module.Finite ℤ (HeckeAlg ⧸ 𝔪) _ _ (@Algebra.toModule ℤ _ _ _ _) :=
    Module.Finite.of_surjective _ hsurj
  haveI : Algebra.IsIntegral ℤ (HeckeAlg ⧸ 𝔪) := Algebra.IsIntegral.of_finite ℤ _
  have hchar : ringChar (HeckeAlg ⧸ 𝔪) ≠ 0 := by
    intro h0
    letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    haveI : CharP (HeckeAlg ⧸ 𝔪) 0 := ringChar.of_eq h0
    haveI : CharZero (HeckeAlg ⧸ 𝔪) := CharP.charP_to_charZero _
    exact Int.not_isField
      (isField_of_isIntegral_of_isField (R := ℤ) (S := HeckeAlg ⧸ 𝔪) (algebraMap ℤ (HeckeAlg ⧸ 𝔪)).injective_int
        (Field.toIsField _))

  haveI : Module.Finite ℤ (HeckeAlg ⧸ 𝔪) := finite_int_transfer ‹_›
  haveI : NeZero (ringChar (HeckeAlg ⧸ 𝔪)) := ⟨hchar⟩
  haveI := ringChar.charP (HeckeAlg ⧸ 𝔪)
  letI : Algebra (ZMod (ringChar (HeckeAlg ⧸ 𝔪))) (HeckeAlg ⧸ 𝔪) := ZMod.algebra _ _
  haveI : Module.Finite (ZMod (ringChar (HeckeAlg ⧸ 𝔪))) (HeckeAlg ⧸ 𝔪) :=
    Module.Finite.of_restrictScalars_finite ℤ _ _
  refine ⟨Module.finite_of_finite (ZMod (ringChar (HeckeAlg ⧸ 𝔪))), ringChar (HeckeAlg ⧸ 𝔪),
    (CharP.char_is_prime_or_zero (HeckeAlg ⧸ 𝔪) _).resolve_right hchar, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
  exact CharP.cast_eq_zero _ _

private theorem tateModule_nsmul_eq_zero_imp (p : ℕ) (J : Type) [AddCommGroup J] (v : TateModule p J)
    (hv : p • v = 0) : v = 0 := by
  apply Subtype.ext
  funext n
  have h : p • (v : ℕ → J) (n + 1) = 0 := congrArg (fun w : TateModule p J => (w : ℕ → J) (n + 1)) hv
  have hc := TateModule.compat v n
  rw [natCast_zsmul] at hc
  show (v : ℕ → J) n = 0
  rw [← hc]
  exact h

private theorem exists_tateModule_apply_one_eq (M : ℕ) [NeZero M] (p : ℕ) (hp : p ≠ 0) (x : JZero M)
    (hx : p • x = 0) : ∃ v : TateModule p (JZero M), (v : ℕ → JZero M) 1 = x := by
  have hdiv : ∀ y : JZero M, ∃ z : JZero M, p • z = y := fun y => JZero.divisible M p hp y
  choose next hnext using hdiv
  let s : ℕ → JZero M := fun n => Nat.rec 0 (fun k _ => next^[k] x) n
  have hs_zero : s 0 = 0 := rfl
  have hs_succ : ∀ k, s (k + 1) = next^[k] x := fun k => rfl
  have hcompat : ∀ n, p • s (n + 1) = s n := by
    intro n
    cases n with
    | zero => rw [hs_succ, Function.iterate_zero_apply, hx, hs_zero]
    | succ k => rw [hs_succ, hs_succ, Function.iterate_succ_apply', hnext]
  have htors : ∀ n, p ^ n • s n = 0 := by
    intro n
    induction n with
    | zero => rw [hs_zero, smul_zero]
    | succ k ih => rw [pow_succ, mul_smul, hcompat, ih]
  refine ⟨⟨s, fun n => ⟨?_, ?_⟩⟩, ?_⟩
  · rw [natCast_zsmul, htors]
  · rw [natCast_zsmul, hcompat]
  · exact (hs_succ 0).trans (Function.iterate_zero_apply next x)

private theorem isTorsionFree_of_nsmul (p : ℕ) [Fact p.Prime] (N : Type*) [AddCommGroup N] [Module ℤ_[p] N]
    (h : ∀ x : N, p • x = 0 → x = 0) : Module.IsTorsionFree ℤ_[p] N where
  isSMulRegular r hr := by
    have hpreg : IsSMulRegular N ((p : ℕ) : ℤ_[p]) := by
      intro x y hxy
      have hxy' : ((p : ℕ) : ℤ_[p]) • x = ((p : ℕ) : ℤ_[p]) • y := hxy
      apply sub_eq_zero.mp
      apply h
      rw [← Nat.cast_smul_eq_nsmul ℤ_[p], smul_sub, hxy', sub_self]
    rw [PadicInt.unitCoeff_spec hr.ne_zero]
    exact (Units.isSMulRegular N (PadicInt.unitCoeff hr.ne_zero)).mul (hpreg.pow _)

section IntegralHeckeAlgebra

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

private abbrev heckeAdjoin : Subalgebra ℤ_[p] (Module.End ℤ_[p] (TateModule p J)) :=
  Algebra.adjoin ℤ_[p] (Set.range (tateHeckeRep p J))

private theorem isMulCommutative_heckeAdjoin : IsMulCommutative (heckeAdjoin p J) := by
  refine Algebra.isMulCommutative_adjoin ℤ_[p] ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, mul_comm]

private scoped instance heckeAdjoinCommRing : CommRing (heckeAdjoin p J) :=
  { (inferInstance : Ring (heckeAdjoin p J)) with
    mul_comm := fun a b => (isMulCommutative_heckeAdjoin p J).is_comm.comm a b }

private def heckeToAdjoin : HeckeAlg →+* heckeAdjoin p J :=
  (tateHeckeRep p J).codRestrict _ fun t => Algebra.subset_adjoin (Set.mem_range_self t)

private theorem coe_heckeToAdjoin (t : HeckeAlg) :
    (heckeToAdjoin p J t : Module.End ℤ_[p] (TateModule p J)) = tateHeckeRep p J t :=
  rfl

private theorem apply_one_eq_zero_of_mem :
    ∀ a ∈ heckeAdjoin p J, ∀ v : TateModule p J, (v : ℕ → J) 1 = 0 → ((a v : TateModule p J) : ℕ → J) 1 = 0 := by
  intro a ha
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨t, rfl⟩ := ha
    intro v hv
    rw [coe_tateHeckeRep_apply_apply, hv, smul_zero]
  | algebraMap c =>
    intro v hv
    rw [Module.algebraMap_end_apply, TateModule.smul_apply, hv, smul_zero]
  | add a b _ _ iha ihb =>
    intro v hv
    rw [LinearMap.add_apply, TateModule.coe_add, Pi.add_apply, iha v hv, ihb v hv, add_zero]
  | mul a b _ _ iha ihb =>
    intro v hv
    rw [Module.End.mul_apply]
    exact iha _ (ihb v hv)

private theorem apply_one_eq_zero_of_mem_map (𝔪 : Ideal HeckeAlg) (x : J) (hkill : ∀ m ∈ 𝔪, m • x = 0)
    (v : TateModule p J) (hv : (v : ℕ → J) 1 = x) (a : heckeAdjoin p J) (ha : a ∈ Ideal.map (heckeToAdjoin p J) 𝔪) :
    (((a : Module.End ℤ_[p] (TateModule p J)) v : TateModule p J) : ℕ → J) 1 = 0 := by
  have ha' : a ∈ Submodule.span (heckeAdjoin p J) ((heckeToAdjoin p J) '' 𝔪) := ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem b hb =>
    obtain ⟨m, hm, rfl⟩ := hb
    rw [coe_heckeToAdjoin, coe_tateHeckeRep_apply_apply, hv, hkill m hm]
  | zero => simp
  | add b c _ _ ihb ihc =>
    rw [Subalgebra.coe_add, LinearMap.add_apply, TateModule.coe_add, Pi.add_apply, ihb, ihc, add_zero]
  | smul b c _ ih =>
    rw [smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    exact apply_one_eq_zero_of_mem p J b b.2 _ ih

private theorem map_ne_top (𝔪 : Ideal HeckeAlg) (x : J) (hx0 : x ≠ 0) (hkill : ∀ m ∈ 𝔪, m • x = 0)
    (v : TateModule p J) (hv : (v : ℕ → J) 1 = x) : Ideal.map (heckeToAdjoin p J) 𝔪 ≠ ⊤ := by
  intro htop
  have h1 := apply_one_eq_zero_of_mem_map p J 𝔪 x hkill v hv 1 ((Ideal.eq_top_iff_one _).mp htop)
  apply hx0
  rw [← hv]
  simpa using h1

omit [Module HeckeAlg J] in

private theorem free_tateModule [Module.Finite ℤ_[p] (TateModule p J)] : Module.Free ℤ_[p] (TateModule p J) := by
  haveI : Module.IsTorsionFree ℤ_[p] (TateModule p J) :=
    isTorsionFree_of_nsmul p (TateModule p J) (tateModule_nsmul_eq_zero_imp p J)
  infer_instance

private theorem moduleFinite_heckeAdjoin [Module.Finite ℤ_[p] (TateModule p J)] :
    Module.Finite ℤ_[p] (heckeAdjoin p J) := by
  haveI : Module.Free ℤ_[p] (TateModule p J) := free_tateModule p J
  haveI : Module.Finite ℤ_[p] (Module.End ℤ_[p] (TateModule p J)) := inferInstance
  haveI : IsNoetherian ℤ_[p] (Module.End ℤ_[p] (TateModule p J)) := inferInstance
  haveI : IsNoetherian ℤ_[p] (heckeAdjoin p J) :=
    isNoetherian_of_injective (heckeAdjoin p J).val.toLinearMap Subtype.val_injective
  infer_instance

private theorem natCast_mem_nonZeroDivisors : ((p : ℕ) : heckeAdjoin p J) ∈ nonZeroDivisors (heckeAdjoin p J) := by
  rw [mem_nonZeroDivisors_iff_left]
  intro a ha
  apply Subtype.ext
  apply LinearMap.ext
  intro v
  apply tateModule_nsmul_eq_zero_imp
  have h := congrArg (fun b : heckeAdjoin p J => (b : Module.End ℤ_[p] (TateModule p J)) v) ha
  simpa using h

private theorem natCast_notMem_of_mem_minimalPrimes (𝔭 : Ideal (heckeAdjoin p J))
    (h𝔭 : 𝔭 ∈ minimalPrimes (heckeAdjoin p J)) : ((p : ℕ) : heckeAdjoin p J) ∉ 𝔭 := fun hp𝔭 =>
  Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes h𝔭) hp𝔭
    (natCast_mem_nonZeroDivisors p J)

private theorem exists_isMaximal_isPrime_algHom_injective [Module.Finite ℤ_[p] (TateModule p J)]
    (I : Ideal (heckeAdjoin p J)) (hI : I ≠ ⊤) :
    ∃ 𝔐 𝔭 : Ideal (heckeAdjoin p J), 𝔐.IsMaximal ∧ 𝔭.IsPrime ∧ I ≤ 𝔐 ∧ 𝔭 ≤ 𝔐 ∧ ((p : ℕ) : heckeAdjoin p J) ∉ 𝔭 ∧
      ∃ χ : heckeAdjoin p J ⧸ 𝔭 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p], Function.Injective χ := by
  obtain ⟨𝔐, h𝔐, hI𝔐⟩ := Ideal.exists_le_maximal I hI
  haveI := h𝔐.isPrime
  obtain ⟨𝔭, h𝔭, h𝔭𝔐⟩ := Ideal.exists_minimalPrimes_le (J := 𝔐) bot_le
  haveI h𝔭p : 𝔭.IsPrime := h𝔭.1.1
  have hp𝔭 : ((p : ℕ) : heckeAdjoin p J) ∉ 𝔭 := natCast_notMem_of_mem_minimalPrimes p J 𝔭 h𝔭
  refine ⟨𝔐, 𝔭, h𝔐, h𝔭p, hI𝔐, h𝔭𝔐, hp𝔭, ?_⟩

  haveI : Module.Finite ℤ_[p] (heckeAdjoin p J) := moduleFinite_heckeAdjoin p J
  haveI : Algebra.IsIntegral ℤ_[p] (heckeAdjoin p J) := Algebra.IsIntegral.of_finite ℤ_[p] _
  have hpQ : ((p : ℕ) : heckeAdjoin p J ⧸ 𝔭) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔭), Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact hp𝔭
  haveI : Module.IsTorsionFree ℤ_[p] (heckeAdjoin p J ⧸ 𝔭) :=
    isTorsionFree_of_nsmul p _ fun x hx => by
      rw [← Nat.cast_smul_eq_nsmul (heckeAdjoin p J ⧸ 𝔭), smul_eq_mul] at hx
      exact (mul_eq_zero.mp hx).resolve_left hpQ

  haveI : CharZero (AlgebraicClosure ℚ_[p]) :=
    charZero_of_injective_algebraMap (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
  haveI : Module.IsTorsionFree ℤ_[p] (AlgebraicClosure ℚ_[p]) :=
    isTorsionFree_of_nsmul p _ fun x hx => by
      rw [← Nat.cast_smul_eq_nsmul (AlgebraicClosure ℚ_[p]), smul_eq_mul] at hx
      exact (mul_eq_zero.mp hx).resolve_left (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero)
  let χ : heckeAdjoin p J ⧸ 𝔭 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := IsAlgClosed.lift
  refine ⟨χ, ?_⟩

  rw [injective_iff_map_eq_zero]
  intro x hx
  have hker : RingHom.ker χ.toRingHom = ⊥ := by
    apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
    rw [RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    intro a b hab
    have h : algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) a = algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p]) b := by
      rw [← χ.commutes a, ← χ.commutes b]
      exact hab
    rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]),
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]) b] at h
    exact IsFractionRing.injective ℤ_[p] ℚ_[p] ((algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective h)
  have hxk : x ∈ RingHom.ker χ.toRingHom := hx
  rw [hker] at hxk
  exact (Submodule.mem_bot _).mp hxk

private def heckeToAdjoin' (t : HeckeAlg) : heckeAdjoin p J :=
  ⟨tateHeckeRep p J t, Algebra.subset_adjoin (Set.mem_range_self t)⟩

private abbrev bc : Module.End ℤ_[p] (TateModule p J) →ₐ[ℤ_[p]] Module.End ℚ_[p] (RationalTateModule p J) :=
  Module.End.baseChangeHom ℤ_[p] ℚ_[p] (TateModule p J)

private theorem bc_tateHeckeRep (t : HeckeAlg) : bc p J (tateHeckeRep p J t) = rationalHeckeRep p J t :=
  rfl

private theorem exists_smul_eq_bc :
    ∀ x ∈ rationalHeckeAlgebra p J, ∃ (c : ℤ_[p]) (a : heckeAdjoin p J),
      c ≠ 0 ∧ (c : ℚ_[p]) • x = bc p J (a : Module.End ℤ_[p] (TateModule p J)) := by
  intro x hx
  refine Algebra.adjoin_induction (hx := hx) ?_ ?_ ?_ ?_
  · rintro _ ⟨t, rfl⟩
    exact ⟨1, heckeToAdjoin' p J t, one_ne_zero, by simp [heckeToAdjoin', bc_tateHeckeRep]⟩
  · intro r
    obtain ⟨⟨u, c⟩, hc⟩ := IsLocalization.surj (nonZeroDivisors ℤ_[p]) r
    refine ⟨c, algebraMap ℤ_[p] (heckeAdjoin p J) u, nonZeroDivisors.ne_zero c.2, ?_⟩
    simp only at hc
    rw [Subalgebra.coe_algebraMap, AlgHom.commutes, Algebra.smul_def, ← map_mul,
      IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (Module.End ℚ_[p] (RationalTateModule p J)), ← hc, mul_comm]
    rfl
  · rintro x y - - ⟨c₁, a₁, hc₁, h₁⟩ ⟨c₂, a₂, hc₂, h₂⟩
    refine ⟨c₁ * c₂, c₂ • a₁ + c₁ • a₂, mul_ne_zero hc₁ hc₂, ?_⟩
    rw [Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_smul, map_add, map_smul, map_smul, ← h₁, ← h₂,
      ← algebraMap_smul ℚ_[p] c₂, ← algebraMap_smul ℚ_[p] c₁, PadicInt.algebraMap_apply, PadicInt.algebraMap_apply,
      PadicInt.coe_mul]
    module
  · rintro x y - - ⟨c₁, a₁, hc₁, h₁⟩ ⟨c₂, a₂, hc₂, h₂⟩
    refine ⟨c₁ * c₂, a₁ * a₂, mul_ne_zero hc₁ hc₂, ?_⟩
    rw [Subalgebra.coe_mul, map_mul, ← h₁, ← h₂, PadicInt.coe_mul, smul_mul_smul_comm]

omit [Module HeckeAlg J] in

private theorem bc_injective [Module.Free ℤ_[p] (TateModule p J)] : Function.Injective (bc p J) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  have hinj : Function.Injective (fun y : TateModule p J => ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] y : RationalTateModule p J)) := by
    intro a b hab
    have hflat : Module.Flat ℤ_[p] (TateModule p J) := Module.Flat.of_free
    have h1 : Function.Injective (Algebra.linearMap ℤ_[p] ℚ_[p]) := fun u v huv => Subtype.ext huv
    have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := TateModule p J) _ h1
    have h3 : (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor (TateModule p J) ((1 : ℤ_[p]) ⊗ₜ a) =
        (Algebra.linearMap ℤ_[p] ℚ_[p]).rTensor (TateModule p J) ((1 : ℤ_[p]) ⊗ₜ b) := by
      simpa [LinearMap.rTensor_tmul] using hab
    have h4 := h2 h3
    simpa using congrArg (TensorProduct.lid ℤ_[p] (TateModule p J)) h4
  apply hinj
  have h := LinearMap.congr_fun hfg ((1 : ℚ_[p]) ⊗ₜ[ℤ_[p]] x)
  first | exact h | simpa [bc, LinearMap.baseChange_tmul] using h | simpa +zetaDelta [bc, LinearMap.baseChange_tmul] using h

end IntegralHeckeAlgebra

section Lambda

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]
variable (K : Type) [Field K] [Algebra ℤ_[p] K]

private abbrev EQ := Module.End ℚ_[p] (RationalTateModule p J)

private abbrev EZ := Module.End ℤ_[p] (TateModule p J)

private def satC (b : rationalHeckeAlgebra p J) : ℤ_[p] := (exists_smul_eq_bc p J b.1 b.2).choose

private def satA (b : rationalHeckeAlgebra p J) : heckeAdjoin p J :=
  (exists_smul_eq_bc p J b.1 b.2).choose_spec.choose

private theorem satC_ne_zero (b : rationalHeckeAlgebra p J) : satC p J b ≠ 0 :=
  (exists_smul_eq_bc p J b.1 b.2).choose_spec.choose_spec.1

private theorem sat_spec (b : rationalHeckeAlgebra p J) :
    (satC p J b : ℚ_[p]) • (b : EQ p J) = bc p J (satA p J b : EZ p J) :=
  (exists_smul_eq_bc p J b.1 b.2).choose_spec.choose_spec.2

private def lamFun (χ : heckeAdjoin p J →ₐ[ℤ_[p]] K) (b : rationalHeckeAlgebra p J) : K :=
  χ (satA p J b) / algebraMap ℤ_[p] K (satC p J b)

private theorem lamFun_eq [Module.Free ℤ_[p] (TateModule p J)] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (χ : heckeAdjoin p J →ₐ[ℤ_[p]] K) (b : rationalHeckeAlgebra p J) (c : ℤ_[p]) (a : heckeAdjoin p J)
    (hc : c ≠ 0) (h : (c : ℚ_[p]) • (b : EQ p J) = bc p J (a : EZ p J)) :
    lamFun p J K χ b = χ a / algebraMap ℤ_[p] K c := by
  have hc0 : satC p J b ≠ 0 := satC_ne_zero p J b
  have hspec := sat_spec p J b
  have key : c • satA p J b = satC p J b • a := by
    apply Subtype.ext
    apply bc_injective p J
    rw [Subalgebra.coe_smul, Subalgebra.coe_smul, map_smul, map_smul, ← hspec, ← h, ← algebraMap_smul ℚ_[p] c,
      ← algebraMap_smul ℚ_[p] (satC p J b), PadicInt.algebraMap_apply, PadicInt.algebraMap_apply, smul_comm]
  have hχ := congrArg χ key
  rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def] at hχ
  have h1 : algebraMap ℤ_[p] K c ≠ 0 := fun h0 => hc (hK (by rw [h0, map_zero]))
  have h2 : algebraMap ℤ_[p] K (satC p J b) ≠ 0 := fun h0 => hc0 (hK (by rw [h0, map_zero]))
  unfold lamFun
  rw [div_eq_div_iff h2 h1, mul_comm, hχ, mul_comm]

private def lam [Module.Free ℤ_[p] (TateModule p J)] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (χ : heckeAdjoin p J →ₐ[ℤ_[p]] K) : rationalHeckeAlgebra p J →+* K where
  toFun := lamFun p J K χ
  map_one' := by
    show lamFun p J K χ 1 = 1
    rw [lamFun_eq p J K hK χ 1 1 1 one_ne_zero (by simp), map_one, map_one, div_one]
  map_mul' x y := by
    show lamFun p J K χ (x * y) = lamFun p J K χ x * lamFun p J K χ y
    obtain ⟨c₁, a₁, hc₁, h₁⟩ := exists_smul_eq_bc p J x.1 x.2
    obtain ⟨c₂, a₂, hc₂, h₂⟩ := exists_smul_eq_bc p J y.1 y.2
    have hxy : ((c₁ * c₂ : ℤ_[p]) : ℚ_[p]) • ((x * y : rationalHeckeAlgebra p J) : EQ p J)
        = bc p J ((a₁ * a₂ : heckeAdjoin p J) : EZ p J) := by
      rw [Subalgebra.coe_mul, Subalgebra.coe_mul, map_mul, ← h₁, ← h₂, PadicInt.coe_mul, smul_mul_smul_comm]
    rw [lamFun_eq p J K hK χ _ _ _ (mul_ne_zero hc₁ hc₂) hxy, lamFun_eq p J K hK χ x c₁ a₁ hc₁ h₁,
      lamFun_eq p J K hK χ y c₂ a₂ hc₂ h₂, map_mul, map_mul, div_mul_div_comm]
  map_zero' := by
    show lamFun p J K χ 0 = 0
    rw [lamFun_eq p J K hK χ 0 1 0 one_ne_zero (by simp), map_zero, zero_div]
  map_add' x y := by
    show lamFun p J K χ (x + y) = lamFun p J K χ x + lamFun p J K χ y
    obtain ⟨c₁, a₁, hc₁, h₁⟩ := exists_smul_eq_bc p J x.1 x.2
    obtain ⟨c₂, a₂, hc₂, h₂⟩ := exists_smul_eq_bc p J y.1 y.2
    have hxy : ((c₁ * c₂ : ℤ_[p]) : ℚ_[p]) • ((x + y : rationalHeckeAlgebra p J) : EQ p J)
        = bc p J ((c₂ • a₁ + c₁ • a₂ : heckeAdjoin p J) : EZ p J) := by
      rw [Subalgebra.coe_add, Subalgebra.coe_add, Subalgebra.coe_smul, Subalgebra.coe_smul, map_add, map_smul,
        map_smul, ← h₁, ← h₂, ← algebraMap_smul ℚ_[p] c₂, ← algebraMap_smul ℚ_[p] c₁, PadicInt.algebraMap_apply,
        PadicInt.algebraMap_apply, PadicInt.coe_mul]
      module
    have h1 : algebraMap ℤ_[p] K c₁ ≠ 0 := fun h0 => hc₁ (hK (by rw [h0, map_zero]))
    have h2 : algebraMap ℤ_[p] K c₂ ≠ 0 := fun h0 => hc₂ (hK (by rw [h0, map_zero]))
    rw [lamFun_eq p J K hK χ _ _ _ (mul_ne_zero hc₁ hc₂) hxy, lamFun_eq p J K hK χ x c₁ a₁ hc₁ h₁,
      lamFun_eq p J K hK χ y c₂ a₂ hc₂ h₂, map_add, map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, map_mul,
      div_add_div _ _ h1 h2, div_eq_div_iff (mul_ne_zero h1 h2) (mul_ne_zero h1 h2)]
    ring

private theorem exists_lambda [Module.Free ℤ_[p] (TateModule p J)] (hK : Function.Injective (algebraMap ℤ_[p] K))
    (χ : heckeAdjoin p J →ₐ[ℤ_[p]] K) :
    ∃ Λ : rationalHeckeAlgebra p J →+* K,
      (∀ c : ℤ_[p], Λ (algebraMap ℚ_[p] (rationalHeckeAlgebra p J) (c : ℚ_[p])) = algebraMap ℤ_[p] K c) ∧
      ∀ t : HeckeAlg, Λ ⟨rationalHeckeRep p J t, rationalHeckeRep_mem_rationalHeckeAlgebra p J t⟩
        = χ (heckeToAdjoin' p J t) := by
  refine ⟨lam p J K hK χ, fun c => ?_, fun t => ?_⟩
  · show lamFun p J K χ _ = _
    have hw : ((1 : ℤ_[p]) : ℚ_[p]) • ((algebraMap ℚ_[p] (rationalHeckeAlgebra p J) (c : ℚ_[p])) : EQ p J)
        = bc p J ((algebraMap ℤ_[p] (heckeAdjoin p J) c) : EZ p J) := by
      rw [Subalgebra.coe_algebraMap, Subalgebra.coe_algebraMap, AlgHom.commutes, PadicInt.coe_one, one_smul,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (EQ p J)]
      rfl
    rw [lamFun_eq p J K hK χ _ 1 _ one_ne_zero hw, AlgHom.commutes, map_one, div_one]
  · show lamFun p J K χ _ = _
    rw [lamFun_eq p J K hK χ _ 1 (heckeToAdjoin' p J t) one_ne_zero (by simp [heckeToAdjoin', bc_tateHeckeRep]),
      map_one, div_one]

end Lambda

section LayerThree

variable (p : ℕ) [Fact p.Prime] (J : Type) [AddCommGroup J] [Module HeckeAlg J]

private theorem heckeToAdjoin'_eq (t : HeckeAlg) : heckeToAdjoin' p J t = heckeToAdjoin p J t :=
  rfl

omit [Module HeckeAlg J] in
private theorem algebraMap_closure_injective : Function.Injective (algebraMap ℤ_[p] (AlgebraicClosure ℚ_[p])) := by
  intro a b h
  rw [IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]),
    IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p]) b] at h
  exact IsFractionRing.injective ℤ_[p] ℚ_[p] ((algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective h)

private theorem exists_dvr_of_algHom [Module.Finite ℤ_[p] (TateModule p J)] (𝔭 : Ideal (heckeAdjoin p J)) [𝔭.IsPrime]
    (χ : heckeAdjoin p J ⧸ 𝔭 →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) (hχ : Function.Injective χ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : Algebra ℤ_[p] O),
      Algebra.IsIntegral ℤ_[p] O ∧ ((p : ℕ) : O) ∈ IsLocalRing.maximalIdeal O ∧
      ∃ χ' : heckeAdjoin p J →ₐ[ℤ_[p]] O, RingHom.ker χ'.toRingHom = 𝔭 ∧
        ∃ (K : Type) (_ : Field K) (_ : Algebra O K) (_ : IsFractionRing O K) (Λ : rationalHeckeAlgebra p J →+* K),
          (∀ c : ℤ_[p],
            Λ (algebraMap ℚ_[p] (rationalHeckeAlgebra p J) (c : ℚ_[p])) = algebraMap O K (algebraMap ℤ_[p] O c)) ∧
          ∀ t : HeckeAlg,
            Λ ⟨rationalHeckeRep p J t, rationalHeckeRep_mem_rationalHeckeAlgebra p J t⟩
              = algebraMap O K (χ' (heckeToAdjoin p J t)) := by
  haveI : Module.Finite ℤ_[p] (heckeAdjoin p J) := moduleFinite_heckeAdjoin p J
  haveI : Algebra.IsIntegral ℤ_[p] (heckeAdjoin p J) := Algebra.IsIntegral.of_finite ℤ_[p] _
  haveI : Module.Free ℤ_[p] (TateModule p J) := free_tateModule p J

  let χA : heckeAdjoin p J →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p] := χ.comp (Ideal.Quotient.mkₐ ℤ_[p] 𝔭)
  have hχA : ∀ a, χA a = 0 ↔ a ∈ 𝔭 := fun a => by
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, map_eq_zero_iff χ hχ, Ideal.Quotient.eq_zero_iff_mem]

  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[p]) (M := heckeAdjoin p J)
  let K : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]) := IntermediateField.adjoin ℚ_[p] (χA '' (s : Set _))
  haveI : FiniteDimensional ℚ_[p] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hmemK : ∀ a : heckeAdjoin p J, χA a ∈ K := by
    intro a
    have ha : a ∈ Submodule.span ℤ_[p] (s : Set (heckeAdjoin p J)) := by
      rw [hs]
      exact Submodule.mem_top
    induction ha using Submodule.span_induction with
    | mem b hb => exact IntermediateField.subset_adjoin ℚ_[p] _ (Set.mem_image_of_mem _ hb)
    | zero => rw [map_zero]; exact zero_mem _
    | add b c _ _ hb hc => rw [map_add]; exact add_mem hb hc
    | smul c b _ hb =>
      rw [map_smul, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (AlgebraicClosure ℚ_[p])]
      exact mul_mem (IntermediateField.algebraMap_mem K _) hb
  let χK : heckeAdjoin p J →ₐ[ℤ_[p]] K :=
    { toFun := fun a => ⟨χA a, hmemK a⟩
      map_one' := Subtype.ext (map_one χA)
      map_mul' := fun a b => Subtype.ext (map_mul χA a b)
      map_zero' := Subtype.ext (map_zero χA)
      map_add' := fun a b => Subtype.ext (map_add χA a b)
      commutes' := fun c => Subtype.ext (χA.commutes c) }
  have hK : Function.Injective (algebraMap ℤ_[p] K) := fun a b h =>
    algebraMap_closure_injective p (congrArg Subtype.val h)

  obtain ⟨-, hdvr, -⟩ :=
    integralClosure.finite_and_isDiscreteValuationRing_and_isAdicComplete_maximalIdeal ℤ_[p] ℚ_[p] K
  haveI : IsDiscreteValuationRing (integralClosure ℤ_[p] K) := hdvr
  haveI : IsFractionRing (integralClosure ℤ_[p] K) K :=
    integralClosure.isFractionRing_of_finite_extension (A := ℤ_[p]) (K := ℚ_[p]) (L := K)
  have hpO : ((p : ℕ) : integralClosure ℤ_[p] K) ∈ IsLocalRing.maximalIdeal (integralClosure ℤ_[p] K) := by
    haveI := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := ℤ_[p])
      (IsLocalRing.maximalIdeal (integralClosure ℤ_[p] K))
    have hcomap := IsLocalRing.eq_maximalIdeal this
    have hp : (p : ℤ_[p]) ∈ IsLocalRing.maximalIdeal ℤ_[p] := by
      rw [PadicInt.maximalIdeal_eq_span_p]
      exact Ideal.mem_span_singleton_self _
    rw [← hcomap, Ideal.mem_comap, map_natCast] at hp
    exact hp

  let χ' : heckeAdjoin p J →ₐ[ℤ_[p]] integralClosure ℤ_[p] K :=
    χK.codRestrict (integralClosure ℤ_[p] K) fun a => (Algebra.IsIntegral.isIntegral a).map χK
  have hker : RingHom.ker χ'.toRingHom = 𝔭 := by
    ext a
    rw [RingHom.mem_ker, ← hχA a]
    constructor
    · intro h
      have h1 := congrArg (fun z : integralClosure ℤ_[p] K => ((z : K) : AlgebraicClosure ℚ_[p])) h
      simpa [χ', χK] using h1
    · intro h
      apply Subtype.ext
      apply Subtype.ext
      simpa [χ', χK] using h

  obtain ⟨Λ, hΛ1, hΛ2⟩ := exists_lambda p J K hK χK
  refine ⟨integralClosure ℤ_[p] K, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, hpO,
    χ', hker, K, inferInstance, inferInstance, inferInstance, Λ, fun c => ?_, fun t => ?_⟩
  · rw [hΛ1 c, IsScalarTower.algebraMap_apply ℤ_[p] (integralClosure ℤ_[p] K) K]
  · exact hΛ2 t

private theorem comap_maximalIdeal_eq (𝔪 : Ideal HeckeAlg) [h𝔪 : 𝔪.IsMaximal] (𝔐 𝔭 : Ideal (heckeAdjoin p J))
    (h𝔐 : 𝔐.IsMaximal) (hmap : Ideal.map (heckeToAdjoin p J) 𝔪 ≤ 𝔐) (h𝔭𝔐 : 𝔭 ≤ 𝔐)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Algebra ℤ_[p] O] [Algebra.IsIntegral ℤ_[p] O]
    (χ' : heckeAdjoin p J →ₐ[ℤ_[p]] O) (hker : RingHom.ker χ'.toRingHom = 𝔭) :
    (IsLocalRing.maximalIdeal O).comap (χ'.toRingHom.comp (heckeToAdjoin p J)) = 𝔪 := by
  have hcomp : χ'.toRingHom.comp (algebraMap ℤ_[p] (heckeAdjoin p J)) = algebraMap ℤ_[p] O := RingHom.ext χ'.commutes
  have hcompInt : (χ'.toRingHom.comp (algebraMap ℤ_[p] (heckeAdjoin p J))).IsIntegral := by
    rw [hcomp]
    exact algebraMap_isIntegral_iff.mpr inferInstance
  have hθint : χ'.toRingHom.IsIntegral :=
    RingHom.IsIntegral.tower_top (algebraMap ℤ_[p] (heckeAdjoin p J)) χ'.toRingHom hcompInt
  letI : Algebra (heckeAdjoin p J) O := χ'.toRingHom.toAlgebra
  haveI : Algebra.IsIntegral (heckeAdjoin p J) O := algebraMap_isIntegral_iff.mp hθint
  obtain ⟨Q, hQ, hQ𝔐⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := O) 𝔐 (by
    show RingHom.ker χ'.toRingHom ≤ 𝔐
    rw [hker]
    exact h𝔭𝔐)
  have hQ' : (IsLocalRing.maximalIdeal O).comap χ'.toRingHom = 𝔐 := by
    rw [← IsLocalRing.eq_maximalIdeal hQ]
    exact hQ𝔐
  rw [← Ideal.comap_comap, hQ']
  exact (h𝔪.eq_of_le (Ideal.comap_ne_top _ h𝔐.ne_top) (Ideal.map_le_iff_le_comap.mp hmap)).symm

end LayerThree

private theorem exists_heckeChar_liesOver
    (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (hsupp : letI := heckeModuleBar M; heckeTorsion (JZero M) 𝔪 ≠ ⊥) :
    Finite (HeckeAlg ⧸ 𝔪) ∧
    ∃ (p : ℕ) (_ : Fact p.Prime), ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧
      ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
        (i₀ : ℤ_[p] →+* O), (p : O) ∈ IsLocalRing.maximalIdeal O ∧
        ∃ θ : HeckeAlg →+* O,
          (letI := heckeModuleBar M
            ∃ (K : Type) (_ : Field K) (_ : Algebra O K) (_ : IsFractionRing O K)
              (Λ : ↥(rationalHeckeAlgebra p (JZero M)) →+* K),
              (∀ c : ℤ_[p],
                Λ (algebraMap ℚ_[p] ↥(rationalHeckeAlgebra p (JZero M)) (c : ℚ_[p])) = algebraMap O K (i₀ c)) ∧
              ∀ t : HeckeAlg,
                Λ ⟨rationalHeckeRep p (JZero M) t, rationalHeckeRep_mem_rationalHeckeAlgebra p (JZero M) t⟩
                  = algebraMap O K (θ t)) ∧
          ∃ ι : HeckeAlg ⧸ 𝔪 →+* IsLocalRing.ResidueField O,
            ∀ t : HeckeAlg, IsLocalRing.residue O (θ t) = ι (Ideal.Quotient.mk 𝔪 t) := by
  letI := heckeModuleBar M

  have h1 := exists_prime_natCast_mem M 𝔪 hsupp
  obtain ⟨hfinQ, p, hp, hpm⟩ := h1
  haveI hpF : Fact p.Prime := ⟨hp⟩
  have h2 := exists_point_of_ne_bot M 𝔪 hsupp
  obtain ⟨x, hx0, hkill⟩ := h2
  have hpx : p • x = 0 := by
    have h := hkill _ hpm
    rwa [Nat.cast_smul_eq_nsmul] at h
  have h3 := exists_tateModule_apply_one_eq M p hp.ne_zero x hpx
  obtain ⟨v, hv⟩ := h3
  have hI := map_ne_top p (JZero M) 𝔪 x hx0 hkill v hv
  haveI : Module.Finite ℤ_[p] (TateModule p (JZero M)) := moduleFinite_padicInt_tateModule_jZero M p

  have h6 := exists_isMaximal_isPrime_algHom_injective p (JZero M) _ hI
  obtain ⟨𝔐, 𝔭, h𝔐, h𝔭, hmap, h𝔭𝔐, -, χ, hχ⟩ := h6
  have h7 := exists_dvr_of_algHom p (JZero M) 𝔭 χ hχ
  obtain ⟨O, _, _, _, _, hint, hpO, χ', hker, K, _, _, _, Λ, hΛ, hΛθ⟩ := h7
  haveI := hint

  have hcomap := comap_maximalIdeal_eq p (JZero M) 𝔪 𝔐 𝔭 h𝔐 hmap h𝔭𝔐 O χ' hker
  have hmem : ∀ t : HeckeAlg, t ∈ 𝔪 →
      (IsLocalRing.residue O) ((χ'.toRingHom.comp (heckeToAdjoin p (JZero M))) t) = 0 := fun t ht =>
    (IsLocalRing.residue_eq_zero_iff _).mpr (by rw [← hcomap] at ht; exact ht)
  have hΛθ' : ∀ t : HeckeAlg,
      Λ ⟨rationalHeckeRep p (JZero M) t, rationalHeckeRep_mem_rationalHeckeAlgebra p (JZero M) t⟩
        = algebraMap O K ((χ'.toRingHom.comp (heckeToAdjoin p (JZero M))) t) := hΛθ
  exact ⟨hfinQ, p, hpF, hpm, O, inferInstance, inferInstance, inferInstance, algebraMap ℤ_[p] O,
    hpO, χ'.toRingHom.comp (heckeToAdjoin p (JZero M)), ⟨K, inferInstance, inferInstance, inferInstance, Λ, hΛ, hΛθ'⟩,
    Ideal.Quotient.lift 𝔪 ((IsLocalRing.residue O).comp (χ'.toRingHom.comp (heckeToAdjoin p (JZero M)))) hmem,
    fun _ => rfl⟩

end

p2m_open "ModularCurve~baseChangeHom Polynomial"

private theorem exists_matrixRep_residual
    (O : Type) [CommRing O] [IsLocalRing O] (ρ : GaloisRepAdic O) :
    ∃ ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField O),
      GaloisFactorsThroughFiniteLevel ρ' ∧
      ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a d : O),
        LinearMap.charpoly (ρ.ρ σ) = X ^ 2 - C a * X + C d →
          (ρ' σ).trace = IsLocalRing.residue O a ∧ (ρ' σ).det = IsLocalRing.residue O d := by
  classical

  set κ := IsLocalRing.ResidueField O
  let b : Module.Basis (Fin 2) κ ρ.residual.V := Module.finBasisOfFinrankEq κ ρ.residual.V ρ.residual.finrank_eq
  let ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) κ :=
    { toFun := fun σ => LinearMap.toMatrix b b (ρ.residual.ρ σ)
      map_one' := by rw [map_one, LinearMap.toMatrix_one]
      map_mul' := fun σ τ => by rw [map_mul, LinearMap.toMatrix_mul] }
  have hρ' : ∀ σ, ρ' σ = LinearMap.toMatrix b b (ρ.residual.ρ σ) := fun σ => rfl
  refine ⟨ρ', ?_, ?_⟩
  ·
    obtain ⟨L, hL, h1⟩ := ρ.residual.factorsThroughFiniteLevel
    exact ⟨L, hL, fun σ hσ => by rw [hρ', h1 σ hσ, LinearMap.toMatrix_one]⟩
  · intro σ a d hchar

    have hbc : (ρ.residual.ρ σ).charpoly = ((ρ.ρ σ).baseChange κ).charpoly := rfl
    have hcp : (ρ.residual.ρ σ).charpoly =
        X ^ 2 - C (IsLocalRing.residue O a) * X + C (IsLocalRing.residue O d) := by
      have h := LinearMap.charpoly_baseChange (ρ.ρ σ) κ
      rw [hchar] at h
      rw [hbc, h]
      simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow,
        Polynomial.map_X, Polynomial.map_C]
      rfl
    have hcpM : (LinearMap.toMatrix b b (ρ.residual.ρ σ)).charpoly =
        X ^ 2 - C (IsLocalRing.residue O a) * X + C (IsLocalRing.residue O d) := by
      rw [LinearMap.charpoly_toMatrix, hcp]
    refine ⟨?_, ?_⟩
    · rw [hρ', Matrix.trace_eq_neg_charpoly_coeff, hcpM]
      simp
    · rw [hρ', Matrix.det_eq_sign_charpoly_coeff, hcpM]
      simp

private theorem trace_pow_mem_and_det_pow_mem {k' : Type} [Field k'] (R₀ : Subring k')
    (M : Matrix (Fin 2) (Fin 2) k') (ht : M.trace ∈ R₀) (hd : M.det ∈ R₀) (n : ℕ) :
    (M ^ n).trace ∈ R₀ ∧ (M ^ n).det ∈ R₀ := by
  refine ⟨?_, by rw [Matrix.det_pow]; exact R₀.pow_mem hd n⟩
  have h2 : M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) k') := by
    have h := Matrix.aeval_self_charpoly M
    rw [Matrix.charpoly_fin_two] at h
    simp only [map_add, map_sub, map_mul, map_pow, aeval_X, aeval_C,
      Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] at h
    rw [← sub_eq_zero, ← h]
    abel
  have key : ∀ m : ℕ, ∃ a b : k', a ∈ R₀ ∧ b ∈ R₀ ∧ M ^ m = a • M + b • (1 : Matrix (Fin 2) (Fin 2) k') := by
    intro m
    induction m with
    | zero => exact ⟨0, 1, R₀.zero_mem, R₀.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨a, b, ha, hb, hm⟩ := ih
      refine ⟨a * M.trace + b, -(a * M.det), R₀.add_mem (R₀.mul_mem ha ht) hb, R₀.neg_mem (R₀.mul_mem ha hd), ?_⟩
      rw [pow_succ, hm, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul, ← pow_two, h2]
      simp only [smul_sub, smul_smul, add_smul, neg_smul]
      abel
  obtain ⟨a, b, ha, hb, hn⟩ := key n
  rw [hn, Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, Matrix.trace_one]
  simp only [smul_eq_mul, Fintype.card_fin]
  exact R₀.add_mem (R₀.mul_mem ha ht) (R₀.mul_mem hb (natCast_mem R₀ 2))

private theorem trace_eq_and_det_eq_of_conj_pow_mem_ker {k' : Type} [Field k']
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (g τ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (n : ℕ) (h : g * τ ^ n * g⁻¹ * σ⁻¹ ∈ ρ.ker) :
    (ρ σ).trace = (ρ τ ^ n).trace ∧ (ρ σ).det = (ρ τ ^ n).det := by
  rw [MonoidHom.mem_ker] at h
  have h1 : ρ (g * τ ^ n * g⁻¹) * ρ σ⁻¹ = 1 := by rw [← map_mul, h]
  have h2 : ρ σ⁻¹ * ρ σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  have hσ : ρ σ = ρ g * ρ τ ^ n * ρ g⁻¹ := by
    calc ρ σ = ρ (g * τ ^ n * g⁻¹) * ρ σ⁻¹ * ρ σ := by rw [h1, one_mul]
      _ = ρ (g * τ ^ n * g⁻¹) * (ρ σ⁻¹ * ρ σ) := by rw [mul_assoc]
      _ = ρ (g * τ ^ n * g⁻¹) := by rw [h2, mul_one]
      _ = ρ g * ρ τ ^ n * ρ g⁻¹ := by rw [map_mul, map_mul, map_pow]
  have hgg : ρ g⁻¹ * ρ g = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  constructor
  · rw [hσ, Matrix.trace_mul_cycle, hgg, one_mul]
  · rw [hσ, Matrix.det_mul, Matrix.det_mul, mul_comm, ← mul_assoc, ← Matrix.det_mul, hgg, Matrix.det_one, one_mul]

private theorem frobeniusPowerDense_ker_of_galoisFactorsThroughFiniteLevel {N : Type} [Monoid N]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* N) (hρ : GaloisFactorsThroughFiniteLevel ρ) (S : Finset ℕ) :
    FrobeniusPowerDense S ρ.ker := by
  obtain ⟨L, hL, hfix⟩ := hρ
  haveI : FiniteDimensional ℚ L := hL

  haveI hNbar : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (@AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ)) :=
      inferInstance
    convert h <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _
  haveI hN : Normal ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ L (AlgebraicClosure ℚ)
  haveI hNF : NumberField (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) := ⟨⟩
  haveI hG : IsGalois ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) := ⟨⟩
  have hST : IsScalarTower ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) (AlgebraicClosure ℚ) :=
    inferInstance
  refine @FrobeniusDensity.frobeniusPowerDense_of_le_ker
    (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) _ (by convert hNF) (by convert hG) _
    (by convert hST) _ ?_ S
  intro σ hσ
  rw [MonoidHom.mem_ker] at hσ ⊢
  refine hfix σ (fun x hx => ?_)
  have hxF : x ∈ IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ) :=
    IntermediateField.le_normalClosure L hx
  have h2 : AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) σ = 1 := by
    convert hσ
  have h1 : ((AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) σ) ⟨x, hxF⟩ :
      AlgebraicClosure ℚ) = σ x :=
    AlgEquiv.restrictNormalHom_apply (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) σ ⟨x, hxF⟩
  rw [h2] at h1
  simpa using h1.symm

private theorem trace_mem_range_and_det_mem_range
    (k : Type) [Field k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ) (t d : ∀ ℓ : ℕ, ℓ.Prime → k)
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ' σ).trace = ι (t ℓ hℓ) ∧ (ρ' σ).det = ι (d ℓ hℓ)) :
    ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (ρ' σ).trace ∈ ι.range ∧ (ρ' σ).det ∈ ι.range := by
  intro σ
  obtain ⟨ℓ, A, τ, g, n, hℓ, hℓS, hA, hτ, hmem⟩ :=
    frobeniusPowerDense_ker_of_galoisFactorsThroughFiniteLevel ρ' hρ' S σ
  obtain ⟨ht, hd⟩ := hfrob ℓ hℓ hℓS A hA τ hτ
  obtain ⟨htr, hdet⟩ := trace_eq_and_det_eq_of_conj_pow_mem_ker ρ' g τ σ n hmem
  have hpow := trace_pow_mem_and_det_pow_mem ι.range (ρ' τ) (ht ▸ ι.mem_range_self _) (hd ▸ ι.mem_range_self _) n
  exact ⟨htr ▸ hpow.1, hdet ▸ hpow.2⟩

private theorem glue_exists_linRep (F : Type) [Field F]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F) :
    ∃ ρL : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* ((Fin 2 → F) ≃ₗ[F] (Fin 2 → F)),
      ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (ρL σ).toLinearMap = Matrix.toLin' (ρM σ) := by

  let f : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End F (Fin 2 → F) :=
    { toFun := fun σ => Matrix.toLin' (ρM σ)
      map_one' := by
        show Matrix.toLin' (ρM 1) = 1
        rw [map_one, Matrix.toLin'_one]
        rfl
      map_mul' := fun σ τ => by
        show Matrix.toLin' (ρM (σ * τ)) = Matrix.toLin' (ρM σ) * Matrix.toLin' (ρM τ)
        rw [map_mul, Matrix.toLin'_mul]
        rfl }
  have hf : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), f σ = Matrix.toLin' (ρM σ) := fun σ => rfl

  refine ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F)).toMonoidHom.comp f.toHomUnits,
    fun σ => ?_⟩
  show ((LinearMap.GeneralLinearGroup.generalLinearEquiv F (Fin 2 → F)) (f.toHomUnits σ)).toLinearMap =
    Matrix.toLin' (ρM σ)
  rw [LinearMap.GeneralLinearGroup.generalLinearEquiv_to_linearMap, MonoidHom.coe_toHomUnits, hf]

private theorem glue_exists_matRep (k : Type) [Field k] (V₀ : Type) [AddCommGroup V₀] [Module k V₀]
    (hV₀ : Module.finrank k V₀ = 2) (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V₀ ≃ₗ[k] V₀)) :
    ∃ (e : (V₀ →ₗ[k] V₀) ≃ₗ[k] Matrix (Fin 2) (Fin 2) k) (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k),
      (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ σ = e (ρ₀ σ).toLinearMap) ∧
      (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        (ρ σ).trace = LinearMap.trace k V₀ (ρ₀ σ).toLinearMap ∧ (ρ σ).det = LinearMap.det (ρ₀ σ).toLinearMap) ∧
      (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ₀ σ = 1 → ρ σ = 1) := by
  classical
  haveI : Module.Finite k V₀ := Module.finite_of_finrank_eq_succ hV₀

  let b : Module.Basis (Fin 2) k V₀ := Module.finBasisOfFinrankEq k V₀ hV₀
  have hone : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ₀ σ = 1 →
      (ρ₀ σ).toLinearMap = LinearMap.id := fun σ h => by
    rw [h]
    rfl
  have hmul : ∀ σ τ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (ρ₀ (σ * τ)).toLinearMap = (ρ₀ σ).toLinearMap * (ρ₀ τ).toLinearMap := fun σ τ => by
    rw [map_mul]
    rfl
  let ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k :=
    { toFun := fun σ => LinearMap.toMatrix b b (ρ₀ σ).toLinearMap
      map_one' := by
        show LinearMap.toMatrix b b (ρ₀ 1).toLinearMap = 1
        rw [hone 1 (map_one ρ₀), LinearMap.toMatrix_id]
      map_mul' := fun σ τ => by
        show LinearMap.toMatrix b b (ρ₀ (σ * τ)).toLinearMap =
          LinearMap.toMatrix b b (ρ₀ σ).toLinearMap * LinearMap.toMatrix b b (ρ₀ τ).toLinearMap
        rw [hmul, LinearMap.toMatrix_mul] }
  have hρ : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      ρ σ = LinearMap.toMatrix b b (ρ₀ σ).toLinearMap := fun σ => rfl
  refine ⟨LinearMap.toMatrix b b, ρ, hρ, fun σ => ⟨?_, ?_⟩, fun σ h1 => ?_⟩
  ·
    rw [hρ, LinearMap.trace_eq_matrix_trace k b]
  ·
    rw [hρ, LinearMap.det_toMatrix]
  · rw [hρ, hone σ h1, LinearMap.toMatrix_id]

private theorem glue_finite_range {N : Type} [Monoid N] (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* N)
    (hρ : GaloisFactorsThroughFiniteLevel ρ) :
    (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)).Finite := by
  classical
  obtain ⟨L, hL, hfix⟩ := hρ
  haveI : FiniteDimensional ℚ L := hL

  haveI hNbar : Normal ℚ (AlgebraicClosure ℚ) := by
    have h : @Normal ℚ (AlgebraicClosure ℚ) _ _ (@AlgebraicClosure.instAlgebra ℚ _ ℚ _ (Algebra.id ℚ)) :=
      inferInstance
    convert h <;> try first | with_reducible_and_instances rfl | rfl | exact Subsingleton.elim _ _

  haveI hN : Normal ℚ (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) :=
    normalClosure.normal ℚ L (AlgebraicClosure ℚ)

  have hfac : Function.FactorsThrough (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)
      (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =>
        AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) g) := by
    intro σ τ hστ
    have hστ' : AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) σ =
        AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) τ := hστ

    have h1 : AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) (τ⁻¹ * σ) = 1 := by
      rw [map_mul, map_inv, hστ', inv_mul_cancel]
    have hfixL : ∀ x ∈ L, (τ⁻¹ * σ) x = x := by
      intro x hx
      have hxE : x ∈ IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ) :=
        IntermediateField.le_normalClosure L hx
      have h2 : ((AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) (τ⁻¹ * σ))
          ⟨x, hxE⟩ : AlgebraicClosure ℚ) = (τ⁻¹ * σ) x :=
        AlgEquiv.restrictNormalHom_apply (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) (τ⁻¹ * σ) ⟨x, hxE⟩
      rw [h1] at h2
      simpa using h2.symm
    have h3 : ρ (τ⁻¹ * σ) = 1 := hfix (τ⁻¹ * σ) hfixL
    show ρ σ = ρ τ
    calc ρ σ = ρ (τ * (τ⁻¹ * σ)) := by rw [mul_inv_cancel_left]
      _ = ρ τ := by rw [map_mul, h3, mul_one]

  have hsub : Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g) ⊆
      Set.range (Function.extend
        (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =>
          AlgEquiv.restrictNormalHom (IntermediateField.normalClosure ℚ L (AlgebraicClosure ℚ)) g)
        (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g) (fun _ => 1)) := by
    rintro _ ⟨σ, rfl⟩
    exact ⟨_, hfac.extend_apply _ σ⟩
  exact (Set.finite_range _).subset hsub

private theorem glue_irreducible (F F' : Type) [Field F] [Field F'] (φ : F →+* F')
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (hspan : Submodule.span F (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρM g)) = ⊤)
    (ρL : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* ((Fin 2 → F') ≃ₗ[F'] (Fin 2 → F')))
    (hρL : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (ρL σ).toLinearMap = Matrix.toLin' ((ρM σ).map φ)) :
    ∀ W : Submodule F' (Fin 2 → F'), (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ∀ v ∈ W, ρL σ v ∈ W) → W = ⊥ ∨ W = ⊤ := by
  classical
  intro W hW

  have hstab : ∀ X : Matrix (Fin 2) (Fin 2) F', ∀ v ∈ W, Matrix.toLin' X v ∈ W := by

    have hT : ∀ Y : Matrix (Fin 2) (Fin 2) F, Y ∈ Submodule.span F (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρM g)) →
        ∀ v ∈ W, Matrix.toLin' (Y.map φ) v ∈ W := by
      intro Y hY
      induction hY using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨σ, rfl⟩ := hx
        intro v hv
        have h := hW σ v hv
        rwa [← LinearEquiv.coe_toLinearMap, hρL] at h
      | zero => intro v hv; simp
      | add x y _ _ hx hy =>
        intro v hv
        rw [Matrix.map_add _ (map_add φ), map_add, LinearMap.add_apply]
        exact W.add_mem (hx v hv) (hy v hv)
      | smul c x _ hx =>
        intro v hv
        have hcx : (c • x).map φ = φ c • x.map φ := by
          ext i j; simp [Matrix.map_apply]
        rw [hcx, map_smul, LinearMap.smul_apply]
        exact W.smul_mem _ (hx v hv)
    have hsingle : ∀ (i j : Fin 2) (v : Fin 2 → F'), v ∈ W → Matrix.toLin' (Matrix.single i j (1 : F')) v ∈ W := by
      intro i j v hv
      have hY : Matrix.single i j (1 : F) ∈ Submodule.span F (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρM g)) := by
        rw [hspan]; exact Submodule.mem_top
      have h := hT _ hY v hv
      have hmap : (Matrix.single i j (1 : F)).map φ = Matrix.single i j (1 : F') := by
        ext a b; simp [Matrix.map_apply, Matrix.single, apply_ite φ]
      rwa [hmap] at h
    intro X v hv
    rw [Matrix.matrix_eq_sum_single X]
    simp only [map_sum, LinearMap.sum_apply]
    refine W.sum_mem fun i _ => W.sum_mem fun j _ => ?_
    have hs : Matrix.single i j (X i j) = X i j • Matrix.single i j (1 : F') := by
      ext a b; simp [Matrix.single, Matrix.smul_apply]
    rw [hs, map_smul, LinearMap.smul_apply]
    exact W.smul_mem _ (hsingle i j v hv)

  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
      by_contra h; push Not at h; exact hw0 (funext h)
    apply top_unique
    intro v _
    let c : Fin 2 → F' := Pi.single i (w i)⁻¹
    have hcw : dotProduct c w = 1 := by
      simp [c, inv_mul_cancel₀ hi]
    have hXw : Matrix.toLin' (Matrix.vecMulVec v c) w = v := by
      rw [Matrix.toLin'_apply, Matrix.vecMulVec_mulVec, hcw]
      simp
    rw [← hXw]
    exact hstab _ w hwW

private theorem glue_trace_det (F F' : Type) [Field F] [Field F'] (φ : F →+* F')
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (ρL : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* ((Fin 2 → F') ≃ₗ[F'] (Fin 2 → F')))
    (hρL : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (ρL σ).toLinearMap = Matrix.toLin' ((ρM σ).map φ))
    (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) :
    LinearMap.trace F' (Fin 2 → F') (ρL σ).toLinearMap = φ (ρM σ).trace ∧
      LinearMap.det (ρL σ).toLinearMap = φ (ρM σ).det := by
  have htm : LinearMap.toMatrix' (ρL σ).toLinearMap = (ρM σ).map φ := by
    rw [hρL, LinearMap.toMatrix'_toLin']
  constructor
  · rw [LinearMap.trace_eq_matrix_trace F' (Pi.basisFun F' (Fin 2)), LinearMap.toMatrix_eq_toMatrix', htm,
      ← AddMonoidHom.map_trace]
  · rw [hρL, LinearMap.det_toLin', ← RingHom.mapMatrix_apply, ← RingHom.map_det]

private theorem glue_exists_gram_det_ne_zero (F : Type) [Field F]
    (ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) F)
    (hspan : Submodule.span F (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρM g)) = ⊤) :
    ∃ σs : Fin 4 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (Matrix.of fun i j => ((ρM (σs i)) * (ρM (σs j))).trace).det ≠ 0 := by
  classical

  obtain ⟨t, htR, hspan_t, hli⟩ := exists_linearIndependent F (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρM g))
  rw [hspan] at hspan_t
  have hfin : t.Finite := LinearIndependent.setFinite hli
  haveI : Fintype t := hfin.fintype
  have hli' : LinearIndepOn F id t := hli
  have hcard : Fintype.card t = 4 := by
    have h := finrank_span_set_eq_card (R := F) hli'
    rw [hspan_t, finrank_top] at h
    rw [← Set.toFinset_card, ← h]
    simp [Module.finrank_matrix]
  let e : Fin 4 ≃ t := (Fintype.equivFinOfCardEq hcard).symm
  choose σs hσs using fun i : Fin 4 => htR (e i).2

  let g : Fin 4 → Matrix (Fin 2) (Fin 2) F := fun i => (e i : Matrix (Fin 2) (Fin 2) F)
  have hg : LinearIndependent F g := hli.comp e e.injective
  have hgσ : ∀ i, ρM (σs i) = g i := fun i => hσs i
  let bM : Module.Basis (Fin 4) F (Matrix (Fin 2) (Fin 2) F) :=
    basisOfLinearIndependentOfCardEqFinrank hg (by simp [Module.finrank_matrix])
  have hbM : ∀ i, bM i = g i := fun i => by simp [bM, coe_basisOfLinearIndependentOfCardEqFinrank]
  refine ⟨σs, ?_⟩
  intro hdet
  obtain ⟨c, hc0, hGc⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet

  set y : Matrix (Fin 2) (Fin 2) F := ∑ j, c j • g j with hy
  have hy_i : ∀ i, Matrix.trace (g i * y) = 0 := by
    intro i
    have h := congrFun hGc i
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply] at h
    rw [hy, Finset.mul_sum, Matrix.trace_sum]
    simp_rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, ← hgσ]
    simpa [mul_comm] using h
  have hall : ∀ x : Matrix (Fin 2) (Fin 2) F, Matrix.trace (x * y) = 0 := by
    intro x
    rw [← bM.sum_repr x, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [Matrix.smul_mul, Matrix.trace_smul, hbM, hy_i i, smul_zero]
  have hy0 : y = 0 := by
    ext i j
    have h := hall (Matrix.single j i 1)
    simpa [Matrix.trace_single_mul] using h

  have := Fintype.linearIndependent_iff.mp hg c (by rw [← hy]; exact hy0)
  exact hc0 (funext this)

private theorem glue_span_eq_top_of_gram (k : Type) [Field k] (V₀ : Type) [AddCommGroup V₀] [Module k V₀]
    (hV₀ : Module.finrank k V₀ = 2) (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* (V₀ ≃ₗ[k] V₀)) (σs : Fin 4 → (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : (Matrix.of fun i j =>
      LinearMap.trace k V₀ ((ρ₀ (σs i)).toLinearMap * (ρ₀ (σs j)).toLinearMap)).det ≠ 0) :
    Submodule.span k (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => (ρ₀ g).toLinearMap)) = ⊤ := by
  classical
  haveI : Module.Finite k V₀ := Module.finite_of_finrank_pos (by omega)
  let f : Fin 4 → (V₀ →ₗ[k] V₀) := fun i => (ρ₀ (σs i)).toLinearMap
  have hli : LinearIndependent k f := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    by_contra hne
    push Not at hne
    apply h
    apply Matrix.exists_vecMul_eq_zero_iff.mp
    refine ⟨c, fun h0 => ?_, ?_⟩
    · obtain ⟨i, hi⟩ := hne; exact hi (congrFun h0 i)
    · ext j
      have hsum : LinearMap.trace k V₀ ((∑ i, c i • f i) * f j) = 0 := by rw [hc, zero_mul, map_zero]
      rw [Finset.sum_mul, map_sum] at hsum
      simp only [Matrix.vecMul, dotProduct, Matrix.of_apply, Pi.zero_apply]
      simpa [smul_mul_assoc, f] using hsum
  have hcard : Fintype.card (Fin 4) = Module.finrank k (V₀ →ₗ[k] V₀) := by
    rw [Module.finrank_linearMap, hV₀]; simp
  have htop := hli.span_eq_top_of_card_eq_finrank' hcard
  apply top_unique
  rw [← htop]
  apply Submodule.span_mono
  rintro x ⟨i, rfl⟩
  exact ⟨σs i, rfl⟩

private theorem exists_matrixRep_descend_of_span_eq_top
    (k : Type) [Field k] [Finite k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ) (t d : ∀ ℓ : ℕ, ℓ.Prime → k)
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ' σ).trace = ι (t ℓ hℓ) ∧ (ρ' σ).det = ι (d ℓ hℓ))
    (hd : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → d ℓ hℓ = (ℓ : k))
    (hrange : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
      (ρ' σ).trace ∈ ι.range ∧ (ρ' σ).det ∈ ι.range)
    (hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) = ⊤) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        ι (ρ σ).trace = (ρ' σ).trace ∧ ι (ρ σ).det = (ρ' σ).det) ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          (ρ σ).trace = t ℓ hℓ ∧ (ρ σ).det = d ℓ hℓ) ∧
      Submodule.span k (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤ := by
  classical

  let p : ℕ := ringChar k
  haveI : Fact p.Prime := ⟨CharP.char_is_prime k p⟩
  let Ω : Type := AlgebraicClosure k'
  let φ : k' →+* Ω := algebraMap k' Ω
  let ιΩ : k →+* Ω := φ.comp ι
  have hinjφ : Function.Injective φ := (algebraMap k' Ω).injective

  let ρM : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) Ω := (RingHom.mapMatrix φ).toMonoidHom.comp ρ'
  have hρM : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρM σ = (ρ' σ).map φ := fun σ => rfl
  obtain ⟨ρΩ, hρΩ⟩ := glue_exists_linRep Ω ρM
  have hρΩ' : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), (ρΩ σ).toLinearMap = Matrix.toLin' ((ρ' σ).map φ) := fun σ => by
    rw [hρΩ, hρM]
  have hone : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ρ' σ = 1 → ρΩ σ = 1 := fun σ h1 => by
    apply LinearEquiv.toLinearMap_injective
    rw [hρΩ', h1, Matrix.map_one φ (map_zero φ) (map_one φ), Matrix.toLin'_one]
    rfl

  have hp : (p : Ω) = 0 := by
    have h0 : (p : k) = 0 := ringChar.Nat.cast_ringChar
    rw [← map_natCast ιΩ p, h0, map_zero]
  have hV : Module.finrank Ω (Fin 2 → Ω) = 2 := Module.finrank_fin_fun Ω
  have hlevΩ : GaloisFactorsThroughFiniteLevel ρΩ := by
    obtain ⟨L, hL, h1⟩ := hρ'
    exact ⟨L, hL, fun σ hσ => hone σ (h1 σ hσ)⟩
  have hfin : Finite ρΩ.range := by
    have h := glue_finite_range ρΩ hlevΩ
    have h' : ((ρΩ.range : Subgroup ((Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω))) :
        Set ((Fin 2 → Ω) ≃ₗ[Ω] (Fin 2 → Ω))).Finite := by
      rw [MonoidHom.coe_range]; exact h
    exact Set.finite_coe_iff.mpr h'
  have hirr := glue_irreducible k' Ω φ ρ' hspan ρΩ hρΩ'
  have htd := glue_trace_det k' Ω φ ρ' ρΩ hρΩ'
  have htr : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), LinearMap.trace Ω (Fin 2 → Ω) (ρΩ σ).toLinearMap ∈ ιΩ.range := fun σ => by
    obtain ⟨x, hx⟩ := (hrange σ).1
    exact ⟨x, by rw [(htd σ).1, ← hx]; rfl⟩
  have hdet : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), LinearMap.det (ρΩ σ).toLinearMap ∈ ιΩ.range := fun σ => by
    obtain ⟨x, hx⟩ := (hrange σ).2
    exact ⟨x, by rw [(htd σ).2, ← hx]; rfl⟩
  have hcyc : ModularCurve.CyclotomicDeterminant (S.prod id) p ρΩ := by
    intro ℓ hℓ hndvd A hA σ hσ
    have hℓS : ℓ ∉ S := fun hmem => hndvd (dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem id hmem) p)
    rw [(htd σ).2, (hfrob ℓ hℓ hℓS A hA σ hσ).2, hd ℓ hℓ hℓS, map_natCast, map_natCast]
  obtain ⟨V₀, _i1, _i2, ρ₀, hV₀, -, hker, htr₀, hdet₀, -⟩ :=
    ModularCurve.exists_semisimple_descent_of_trace_det_mem_range_finite (S.prod id) p Ω k ιΩ (Fin 2 → Ω) ρΩ
      hp hV hfin hirr htr hdet hcyc

  obtain ⟨e, ρ, hρe, htrdet, hone₀⟩ := glue_exists_matRep k V₀ hV₀ ρ₀
  have hιeq : ∀ σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), ι (ρ σ).trace = (ρ' σ).trace ∧ ι (ρ σ).det = (ρ' σ).det := by
    intro σ
    constructor
    · apply hinjφ
      calc φ (ι (ρ σ).trace) = ιΩ (LinearMap.trace k V₀ (ρ₀ σ).toLinearMap) := by rw [(htrdet σ).1]; rfl
        _ = LinearMap.trace Ω (Fin 2 → Ω) (ρΩ σ).toLinearMap := htr₀ σ
        _ = φ (ρ' σ).trace := (htd σ).1
    · apply hinjφ
      calc φ (ι (ρ σ).det) = ιΩ (LinearMap.det (ρ₀ σ).toLinearMap) := by rw [(htrdet σ).2]; rfl
        _ = LinearMap.det (ρΩ σ).toLinearMap := hdet₀ σ
        _ = φ (ρ' σ).det := (htd σ).2
  refine ⟨ρ, ?_, hιeq, ?_, ?_⟩
  · obtain ⟨L, hL, h1⟩ := hρ'
    refine ⟨L, hL, fun σ hσ => hone₀ σ ?_⟩
    have hmem : σ ∈ ρΩ.ker := by rw [MonoidHom.mem_ker]; exact hone σ (h1 σ hσ)
    exact (MonoidHom.mem_ker).mp (hker hmem)
  · intro ℓ hℓ hℓS A hA σ hσ
    obtain ⟨h1, h2⟩ := hfrob ℓ hℓ hℓS A hA σ hσ
    exact ⟨ι.injective (by rw [(hιeq σ).1, h1]), ι.injective (by rw [(hιeq σ).2, h2])⟩
  ·
    obtain ⟨σs, hG⟩ := glue_exists_gram_det_ne_zero k' ρ' hspan
    have hentry : ∀ i j : Fin 4,
        ιΩ (LinearMap.trace k V₀ ((ρ₀ (σs i)).toLinearMap * (ρ₀ (σs j)).toLinearMap)) =
          φ (((ρ' (σs i)) * (ρ' (σs j))).trace) := by
      intro i j
      have hm : (ρ₀ (σs i)).toLinearMap * (ρ₀ (σs j)).toLinearMap = (ρ₀ (σs i * σs j)).toLinearMap := by
        rw [map_mul]; rfl
      rw [hm, htr₀, (htd _).1, map_mul]
    have hG₀ : (Matrix.of fun i j =>
        LinearMap.trace k V₀ ((ρ₀ (σs i)).toLinearMap * (ρ₀ (σs j)).toLinearMap)).det ≠ 0 := by
      intro h0
      apply hG
      apply hinjφ
      rw [map_zero, RingHom.map_det]
      have hmat : (RingHom.mapMatrix φ) (Matrix.of fun i j => ((ρ' (σs i)) * (ρ' (σs j))).trace) =
          (RingHom.mapMatrix ιΩ) (Matrix.of fun i j =>
            LinearMap.trace k V₀ ((ρ₀ (σs i)).toLinearMap * (ρ₀ (σs j)).toLinearMap)) := by
        ext i j
        simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
        rw [hentry]
      rw [hmat, ← RingHom.map_det, h0, map_zero]
    have hspan₀ := glue_span_eq_top_of_gram k V₀ hV₀ ρ₀ σs hG₀
    have hrange_eq : Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g) =
        e.toLinearMap '' Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => (ρ₀ g).toLinearMap) := by
      ext m
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, (hρe σ).symm⟩
      · rintro ⟨x, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, hρe σ⟩
    rw [hrange_eq, Submodule.span_image, hspan₀, Submodule.map_top, LinearEquiv.range]

private def entryFunctional (L : Type) [Field L] (i j : Fin 2) : Matrix (Fin 2) (Fin 2) L →ₗ[L] L where
  toFun N := N i j
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] private theorem entryFunctional_apply (L : Type) [Field L] (i j : Fin 2) (N : Matrix (Fin 2) (Fin 2) L) :
    entryFunctional L i j N = N i j := rfl

private theorem span_eq_top_of_span_map_eq_top_fin_two {K L : Type} [Field K] [Field L] (f : K →+* L)
    (S : Set (Matrix (Fin 2) (Fin 2) K))
    (h : Submodule.span L ((fun M : Matrix (Fin 2) (Fin 2) K => M.map f) '' S) = ⊤) :
    Submodule.span K S = ⊤ := by
  by_contra hne
  obtain ⟨ℓ, hℓ0, hℓ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
  have hℓsum : ∀ M : Matrix (Fin 2) (Fin 2) K, ℓ M = ∑ i, ∑ j, M i j * ℓ (Matrix.single i j 1) := by
    intro M
    conv_lhs => rw [Matrix.matrix_eq_sum_single M]
    simp only [map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← smul_eq_mul, ← map_smul, Matrix.smul_single, smul_eq_mul, mul_one]
  let ℓ' : Matrix (Fin 2) (Fin 2) L →ₗ[L] L := ∑ i, ∑ j, f (ℓ (Matrix.single i j 1)) • entryFunctional L i j
  have hℓ' : ∀ M : Matrix (Fin 2) (Fin 2) K, ℓ' (M.map f) = f (ℓ M) := by
    intro M
    rw [hℓsum, map_sum]
    simp only [ℓ', LinearMap.sum_apply, LinearMap.smul_apply, entryFunctional_apply, Matrix.map_apply, smul_eq_mul,
      map_sum, map_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring
  have hker : (⊤ : Submodule L (Matrix (Fin 2) (Fin 2) L)) ≤ LinearMap.ker ℓ' := by
    rw [← h, Submodule.span_le]
    rintro _ ⟨M, hM, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, hℓ', LinearMap.mem_ker.mp (hℓ (Submodule.subset_span hM)),
      map_zero]
  have hc : ∀ i j, ℓ (Matrix.single i j 1) = 0 := by
    intro i j
    have h1 : ℓ' ((Matrix.single i j (1 : K)).map f) = 0 := hker Submodule.mem_top
    rw [hℓ'] at h1
    exact (map_eq_zero_iff f f.injective).mp h1
  apply hℓ0
  ext M
  rw [hℓsum]
  simp [hc]

private theorem exists_stableLine_of_span_ne_top
    (k' : Type) [Field k'] (Ω : Type) [Field Ω] [IsAlgClosed Ω] (j : k' →+* Ω)
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) ≠ ⊤) :
    ∃ w : Fin 2 → Ω, w ≠ 0 ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ∃ c : Ω, Matrix.mulVec ((ρ' σ).map j) w = c • w := by
  classical
  by_contra hno
  push Not at hno

  let ρΩ : Representation Ω (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Fin 2 → Ω) :=
    { toFun := fun σ => Matrix.toLin' (j.mapMatrix (ρ' σ))
      map_one' := by rw [map_one, map_one, Matrix.toLin'_one]; rfl
      map_mul' := fun σ τ => by rw [map_mul, map_mul, Matrix.toLin'_mul]; rfl }
  have hρΩ : ∀ σ (v : Fin 2 → Ω), ρΩ σ v = Matrix.mulVec ((ρ' σ).map j) v := fun σ v => rfl

  haveI : Nontrivial (Subrepresentation ρΩ) := ⟨⊥, ⊤, fun hbt => by
    have h1 : (⊥ : Subrepresentation ρΩ).toSubmodule = (⊤ : Subrepresentation ρΩ).toSubmodule := by rw [hbt]
    exact bot_ne_top (h1 : (⊥ : Submodule Ω (Fin 2 → Ω)) = ⊤)⟩
  haveI : ρΩ.IsIrreducible := by
    refine ⟨fun W => ?_⟩
    by_contra hW
    push Not at hW
    have hWb : W.toSubmodule ≠ ⊥ := fun h0 => hW.1 (Subrepresentation.toSubmodule_injective h0)
    have hWt : W.toSubmodule ≠ ⊤ := fun h0 => hW.2 (Subrepresentation.toSubmodule_injective h0)
    obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWb
    obtain ⟨σ, hσ⟩ := hno w hw0
    have hlt : Module.finrank Ω W.toSubmodule < 2 := by
      have h2 := Submodule.finrank_lt hWt
      rwa [Module.finrank_fin_fun] at h2
    have hne0 : Module.finrank Ω W.toSubmodule ≠ 0 := fun h0 => hWb (Submodule.finrank_eq_zero.mp h0)
    have h1 : Module.finrank Ω W.toSubmodule = 1 := by omega
    have hw0' : (⟨w, hwW⟩ : W.toSubmodule) ≠ 0 := fun h0 => hw0 (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hw0').mp h1 ⟨ρΩ σ w, W.apply_mem_toSubmodule σ hwW⟩
    have hc' : c • w = Matrix.mulVec ((ρ' σ).map j) w := by
      have := congrArg Subtype.val hc
      simpa [hρΩ] using this
    exact hσ c hc'.symm

  have hspanΩ : Submodule.span Ω (Set.range ρΩ) = ⊤ := Representation.span_range_eq_top_of_isIrreducible ρΩ
  have hspanM : Submodule.span Ω (Set.range fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (ρ' σ).map j) = ⊤ := by
    have hset : Set.range ρΩ = (Matrix.toLin' : Matrix (Fin 2) (Fin 2) Ω ≃ₗ[Ω] _).toLinearMap ''
        Set.range (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => (ρ' σ).map j) := by
      ext f
      simp only [Set.mem_range, Set.mem_image]
      constructor
      · rintro ⟨σ, rfl⟩
        exact ⟨_, ⟨σ, rfl⟩, rfl⟩
      · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
        exact ⟨σ, rfl⟩
    apply Submodule.map_injective_of_injective
      (f := (Matrix.toLin' : Matrix (Fin 2) (Fin 2) Ω ≃ₗ[Ω] _).toLinearMap) (fun x y hxy => by simpa using hxy)
    rw [Submodule.map_top, LinearEquiv.range, ← Submodule.span_image, ← hset, hspanΩ]

  have hT : (fun M : Matrix (Fin 2) (Fin 2) k' => M.map j) ''
      Set.range (fun g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => ρ' g) =
      Set.range (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => (ρ' σ).map j) := by
    ext N
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨σ, rfl⟩, rfl⟩
      exact ⟨σ, rfl⟩
    · rintro ⟨σ, rfl⟩
      exact ⟨_, ⟨σ, rfl⟩, rfl⟩
  exact hspan (span_eq_top_of_span_map_eq_top_fin_two j
    (Set.range (fun g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ => ρ' g)) (by rw [hT]; exact hspanM))

private theorem mul_self_eq_trace_smul_sub_det_smul_fin_two {K : Type} [CommRing K]
    (A : Matrix (Fin 2) (Fin 2) K) :
    A * A = A.trace • A - A.det • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two, Matrix.one_fin_two] <;> ring

private theorem exists_characters_of_stableLine
    {G : Type} [Group G] (K : Type) [Field K] (R : G →* Matrix (Fin 2) (Fin 2) K)
    (w : Fin 2 → K) (hw : w ≠ 0) (hstab : ∀ g : G, ∃ c : K, Matrix.mulVec (R g) w = c • w) :
    ∃ χ₁ χ₂ : G →* K,
      (∀ g : G, (R g).trace = χ₁ g + χ₂ g ∧ (R g).det = χ₁ g * χ₂ g) ∧
      ∀ g : G, R g = 1 → χ₁ g = 1 ∧ χ₂ g = 1 := by
  classical
  choose c hc using hstab
  have huniq : ∀ a b : K, a • w = b • w → a = b := by
    intro a b h
    have h0 : (a - b) • w = 0 := by rw [sub_smul, h, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hw)
  have hc1 : c 1 = 1 := huniq _ _ (by rw [← hc 1, map_one, Matrix.one_mulVec, one_smul])
  have hcmul : ∀ g h : G, c (g * h) = c g * c h := by
    intro g h
    apply huniq
    rw [← hc (g * h), map_mul, ← Matrix.mulVec_mulVec, hc h, Matrix.mulVec_smul, hc g, smul_smul, mul_comm]
  have hcne : ∀ g : G, c g ≠ 0 := by
    intro g h0
    have h1 := hcmul g g⁻¹
    rw [mul_inv_cancel, hc1, h0, zero_mul] at h1
    exact one_ne_zero h1
  have hc_of_eq_one : ∀ g : G, R g = 1 → c g = 1 := by
    intro g hg
    apply huniq
    rw [← hc g, hg, Matrix.one_mulVec, one_smul]

  have hCH : ∀ g : G, c g * c g = (R g).trace * c g - (R g).det := by
    intro g
    apply huniq
    have h1 : Matrix.mulVec (R g * R g) w = (c g * c g) • w := by
      rw [← Matrix.mulVec_mulVec, hc g, Matrix.mulVec_smul, hc g, smul_smul]
    have h2 : Matrix.mulVec ((R g).trace • R g - (R g).det • (1 : Matrix (Fin 2) (Fin 2) K)) w
        = ((R g).trace * c g - (R g).det) • w := by
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, hc g, smul_smul, Matrix.smul_mulVec, Matrix.one_mulVec,
        sub_smul]
    rw [← h1, mul_self_eq_trace_smul_sub_det_smul_fin_two, h2]
  let χ₁ : G →* K := { toFun := c, map_one' := hc1, map_mul' := hcmul }
  let χ₂ : G →* K :=
    { toFun := fun g => (R g).det * (c g)⁻¹
      map_one' := by rw [map_one, Matrix.det_one, hc1, inv_one, mul_one]
      map_mul' := fun g h => by rw [map_mul, Matrix.det_mul, hcmul, mul_inv]; ring }
  refine ⟨χ₁, χ₂, fun g => ⟨?_, ?_⟩, fun g hg => ⟨hc_of_eq_one g hg, ?_⟩⟩
  · show (R g).trace = c g + (R g).det * (c g)⁻¹
    calc (R g).trace = (R g).trace * c g * (c g)⁻¹ := by rw [mul_inv_cancel_right₀ (hcne g)]
      _ = (c g * c g + (R g).det) * (c g)⁻¹ := by rw [hCH g, sub_add_cancel]
      _ = c g + (R g).det * (c g)⁻¹ := by rw [add_mul, mul_inv_cancel_right₀ (hcne g)]
  · show (R g).det = c g * ((R g).det * (c g)⁻¹)
    rw [mul_left_comm, mul_inv_cancel₀ (hcne g), mul_one]
  · show (R g).det * (c g)⁻¹ = 1
    rw [hg, Matrix.det_one, hc_of_eq_one g hg, inv_one, mul_one]

private theorem exists_characters_of_span_ne_top
    (k' : Type) [Field k']
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) ≠ ⊤) :
    ∃ (K : Type) (_ : Field K) (j : k' →+* K)
      (χ₁ χ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* K),
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        j (ρ' σ).trace = χ₁ σ + χ₂ σ ∧ j (ρ' σ).det = χ₁ σ * χ₂ σ) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ' σ = 1 → χ₁ σ = 1 ∧ χ₂ σ = 1 := by
  obtain ⟨w, hw, hstab⟩ :=
    exists_stableLine_of_span_ne_top k' (AlgebraicClosure k') (algebraMap k' (AlgebraicClosure k')) ρ' hspan
  let R : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (AlgebraicClosure k') :=
    (algebraMap k' (AlgebraicClosure k')).mapMatrix.toMonoidHom.comp ρ'
  have hR : ∀ σ, R σ = (ρ' σ).map (algebraMap k' (AlgebraicClosure k')) := fun σ => rfl
  obtain ⟨χ₁, χ₂, hid, hker⟩ :=
    exists_characters_of_stableLine (AlgebraicClosure k') R w hw (fun σ => by rw [hR]; exact hstab σ)
  refine ⟨AlgebraicClosure k', inferInstance, algebraMap k' (AlgebraicClosure k'), χ₁, χ₂, fun σ => ?_,
    fun σ hσ => hker σ ?_⟩
  · exact ⟨(AddMonoidHom.map_trace (algebraMap k' (AlgebraicClosure k')) (ρ' σ)).trans (hid σ).1,
      (RingHom.map_det (algebraMap k' (AlgebraicClosure k')) (ρ' σ)).trans (hid σ).2⟩
  · rw [hR, hσ]
    exact Matrix.map_one (algebraMap k' (AlgebraicClosure k')) (map_zero _) (map_one _)

private theorem quadCoords_injective {k K : Type} [Field k] [Field K] (e : k →+* K) (α : K)
    (hα : α ∉ e.range) : Function.Injective (fun ab : k × k => e ab.1 + e ab.2 * α) := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  change e a + e b * α = e a' + e b' * α at h
  by_cases hb : b = b'
  · subst hb
    have ha : e a = e a' := add_right_cancel h
    rw [e.injective ha]
  · exfalso
    apply hα
    have hbb : e b - e b' ≠ 0 := sub_ne_zero.mpr (fun h' => hb (e.injective h'))
    refine RingHom.mem_range.mpr ⟨(a' - a) / (b - b'), ?_⟩
    rw [map_div₀, map_sub, map_sub, div_eq_iff hbb]
    linear_combination -h

private theorem pow_q_pow_q_eq_self {k K : Type} [Field k] [Field K] (e : k →+* K) (q : ℕ)
    (hsub : ∀ y z : K, (y - z) ^ q = y ^ q - z ^ q) (hfix : ∀ a : k, (e a) ^ q = e a)
    (x : K) (t d : k) (hx : x * x = e t * x - e d) : (x ^ q) ^ q = x := by
  have hxq : x ^ q * x ^ q = e t * x ^ q - e d := by
    rw [← mul_pow, hx, hsub, mul_pow, hfix, hfix]
  have h2 : (x ^ q - x) * (x ^ q + x - e t) = 0 := by linear_combination hxq - hx
  rcases mul_eq_zero.mp h2 with h | h
  · have hxx : x ^ q = x := sub_eq_zero.mp h
    rw [hxx, hxx]
  · have hxx : x ^ q = e t - x := by linear_combination h
    rw [hxx, hsub, hfix, hxx, sub_sub_cancel]

private theorem exists_quadCoords {k K : Type} [Field k] [Finite k] [Field K] (e : k →+* K)
    (α : K) (hα : α ∉ e.range) (t₀ d₀ : k) (hα2 : α * α = e t₀ * α - e d₀)
    (x : K) (t d : k) (hx : x * x = e t * x - e d) :
    ∃ a b : k, x = e a + e b * α := by
  classical
  cases nonempty_fintype k
  obtain ⟨p, hpchar, n, hp, hcard⟩ := FiniteField.card' k
  haveI : CharP k p := hpchar
  haveI : CharP K p := charP_of_injective_ringHom e.injective p
  haveI : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 < Fintype.card k := Fintype.one_lt_card
  have hadd : ∀ y z : K, (y + z) ^ Fintype.card k = y ^ Fintype.card k + z ^ Fintype.card k :=
    fun y z => by rw [hcard]; exact add_pow_char_pow y z p n
  have hsub : ∀ y z : K, (y - z) ^ Fintype.card k = y ^ Fintype.card k - z ^ Fintype.card k :=
    fun y z => by rw [hcard]; exact sub_pow_char_pow y z n
  have hfix : ∀ a : k, (e a) ^ Fintype.card k = e a := fun a => by
    rw [← map_pow, FiniteField.pow_card]
  have hroot : ∀ (y : K) (t d : k), y * y = e t * y - e d →
      y ^ (Fintype.card k * Fintype.card k) = y := fun y t d hy => by
    rw [pow_mul]; exact pow_q_pow_q_eq_self e _ hsub hfix y t d hy
  have hFfix : ∀ a b : k, (e a + e b * α) ^ (Fintype.card k * Fintype.card k) = e a + e b * α := by
    intro a b
    rw [pow_mul, hadd, mul_pow, hfix, hfix, hadd, mul_pow, hfix, hfix, ← pow_mul, hroot α t₀ d₀ hα2]
  obtain ⟨F, hF⟩ : ∃ F : Finset K,
      F = (Finset.univ : Finset (k × k)).image (fun ab : k × k => e ab.1 + e ab.2 * α) := ⟨_, rfl⟩
  have hFcard : F.card = Fintype.card k * Fintype.card k := by
    rw [hF, Finset.card_image_of_injective _ (quadCoords_injective e α hα), Finset.card_univ,
      Fintype.card_prod]
  have hQ : 1 < Fintype.card k * Fintype.card k := by nlinarith
  obtain ⟨P, hP⟩ : ∃ P : Polynomial K,
      P = Polynomial.X ^ (Fintype.card k * Fintype.card k) - Polynomial.X := ⟨_, rfl⟩
  have hP0 : P ≠ 0 := by rw [hP]; exact FiniteField.X_pow_card_sub_X_ne_zero K hQ
  have hPdeg : P.natDegree = Fintype.card k * Fintype.card k := by
    rw [hP]; exact FiniteField.X_pow_card_sub_X_natDegree_eq K hQ
  have hmemR : ∀ y : K, y ∈ P.roots.toFinset ↔ y ^ (Fintype.card k * Fintype.card k) = y := by
    intro y
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def, hP]
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, sub_eq_zero]
  have hRcard : P.roots.toFinset.card ≤ Fintype.card k * Fintype.card k :=
    (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hPdeg.le)
  have hFR : F ⊆ P.roots.toFinset := by
    intro y hy
    rw [hF, Finset.mem_image] at hy
    obtain ⟨⟨a, b⟩, -, hy⟩ := hy
    rw [hmemR, ← hy]
    exact hFfix a b
  have hFeq : F = P.roots.toFinset := Finset.eq_of_subset_of_card_le hFR (by rw [hFcard]; exact hRcard)
  have hxR : x ∈ P.roots.toFinset := (hmemR x).mpr (hroot x t d hx)
  rw [← hFeq, hF, Finset.mem_image] at hxR
  obtain ⟨⟨a, b⟩, -, hab⟩ := hxR
  exact ⟨a, b, hab.symm⟩

private def quadMat {k : Type} [Field k] (t₀ d₀ : k) (ab : k × k) : Matrix (Fin 2) (Fin 2) k :=
  Matrix.of ![![ab.1, -(ab.2 * d₀)], ![ab.2, ab.1 + ab.2 * t₀]]

private def quadMul {k : Type} [Field k] (t₀ d₀ : k) (x y : k × k) : k × k :=
  (x.1 * y.1 - x.2 * y.2 * d₀, x.1 * y.2 + x.2 * y.1 + x.2 * y.2 * t₀)

private theorem quadMul_comm {k : Type} [Field k] (t₀ d₀ : k) (x y : k × k) :
    quadMul t₀ d₀ x y = quadMul t₀ d₀ y x := by
  simp only [quadMul, Prod.mk.injEq]
  constructor <;> ring

private theorem quadMat_one {k : Type} [Field k] (t₀ d₀ : k) : quadMat t₀ d₀ (1, 0) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat]

private theorem quadMat_mul {k : Type} [Field k] (t₀ d₀ : k) (x y : k × k) :
    quadMat t₀ d₀ x * quadMat t₀ d₀ y = quadMat t₀ d₀ (quadMul t₀ d₀ x y) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [quadMat, quadMul, Matrix.mul_apply, Fin.sum_univ_two] <;> ring

private theorem quadMat_trace {k : Type} [Field k] (t₀ d₀ : k) (ab : k × k) :
    (quadMat t₀ d₀ ab).trace = ab.1 + (ab.1 + ab.2 * t₀) := by
  simp [quadMat, Matrix.trace_fin_two]

private theorem quadMat_det {k : Type} [Field k] (t₀ d₀ : k) (ab : k × k) :
    (quadMat t₀ d₀ ab).det = ab.1 * (ab.1 + ab.2 * t₀) + ab.2 * ab.2 * d₀ := by
  simp [quadMat, Matrix.det_fin_two]
  ring

private theorem embed_quadMul {k K : Type} [Field k] [Field K] (e : k →+* K) (α : K) (t₀ d₀ : k)
    (hα2 : α * α = e t₀ * α - e d₀) (x y : k × k) :
    e (quadMul t₀ d₀ x y).1 + e (quadMul t₀ d₀ x y).2 * α = (e x.1 + e x.2 * α) * (e y.1 + e y.2 * α) := by
  simp only [quadMul, map_add, map_sub, map_mul]
  linear_combination (-(e x.2 * e y.2)) * hα2

private theorem quad_partner_eq {k K : Type} [Field k] [Field K] (e : k →+* K) (α : K) (hα : α ∉ e.range)
    (t₀ d₀ : k) (hα2 : α * α = e t₀ * α - e d₀) (a b : k) (hb : b ≠ 0) (y : K) (t d : k)
    (hsum : e a + e b * α + y = e t) (hprod : (e a + e b * α) * y = e d) :
    y = e (a + b * t₀) - e b * α := by
  have hy : y = e t - (e a + e b * α) := by linear_combination hsum
  have hkey : e (a * t - a * a + b * b * d₀) + e (b * t - (a * b + a * b) - b * b * t₀) * α
      = e d + e 0 * α := by
    rw [map_zero, zero_mul, add_zero, ← hprod, hy]
    simp only [map_add, map_sub, map_mul]
    linear_combination (e b * e b) * hα2
  have h2 : ((a * t - a * a + b * b * d₀, b * t - (a * b + a * b) - b * b * t₀) : k × k) = (d, 0) :=
    quadCoords_injective e α hα hkey
  have h3 : b * t - (a * b + a * b) - b * b * t₀ = 0 := congrArg Prod.snd h2
  have ht : t = a + a + b * t₀ := by
    have h4 : b * (t - (a + a + b * t₀)) = 0 := by linear_combination h3
    rcases mul_eq_zero.mp h4 with h | h
    · exact absurd h hb
    · linear_combination h
  rw [hy, ht]
  simp only [map_add, map_mul]
  ring

private theorem chi2_eq_conj {k K G : Type} [Field k] [Field K] [Group G] (e : k →+* K)
    (χ₁ χ₂ : G →* K) (hs : ∀ σ, χ₁ σ + χ₂ σ ∈ e.range) (hp : ∀ σ, χ₁ σ * χ₂ σ ∈ e.range)
    (τ₀ : G) (hα : χ₁ τ₀ ∉ e.range) (t₀ d₀ : k) (ht₀ : χ₁ τ₀ + χ₂ τ₀ = e t₀)
    (hd₀ : χ₁ τ₀ * χ₂ τ₀ = e d₀) (σ : G) (a b : k) (hab : χ₁ σ = e a + e b * χ₁ τ₀) :
    χ₂ σ = e (a + b * t₀) - e b * χ₁ τ₀ := by
  have hα2 : χ₁ τ₀ * χ₁ τ₀ = e t₀ * χ₁ τ₀ - e d₀ := by linear_combination -hd₀ + χ₁ τ₀ * ht₀
  by_cases hb : b = 0
  · subst hb
    have ha : a ≠ 0 := by
      rintro rfl
      have h1 : χ₁ σ * χ₁ σ⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      have h0 : χ₁ σ ≠ 0 := left_ne_zero_of_mul_eq_one h1
      apply h0
      rw [hab]
      simp
    have hστ : χ₁ (σ * τ₀) = e 0 + e a * χ₁ τ₀ := by
      rw [map_mul, hab]
      simp
    obtain ⟨t, ht⟩ := RingHom.mem_range.mp (hs (σ * τ₀))
    obtain ⟨d, hd⟩ := RingHom.mem_range.mp (hp (σ * τ₀))
    have h1 := quad_partner_eq e (χ₁ τ₀) hα t₀ d₀ hα2 0 a ha (χ₂ (σ * τ₀)) t d
      (by rw [← hστ]; exact ht.symm) (by rw [← hστ]; exact hd.symm)
    have h2 : χ₂ τ₀ = e t₀ - χ₁ τ₀ := by linear_combination ht₀
    have hne : e t₀ - χ₁ τ₀ ≠ 0 := fun h0 =>
      hα (RingHom.mem_range.mpr ⟨t₀, by linear_combination h0⟩)
    rw [map_mul, h2] at h1
    have h3 : χ₂ σ * (e t₀ - χ₁ τ₀) = e a * (e t₀ - χ₁ τ₀) := by
      rw [h1]
      simp only [map_mul, zero_add]
      ring
    rw [mul_right_cancel₀ hne h3]
    simp
  · obtain ⟨t, ht⟩ := RingHom.mem_range.mp (hs σ)
    obtain ⟨d, hd⟩ := RingHom.mem_range.mp (hp σ)
    exact quad_partner_eq e (χ₁ τ₀) hα t₀ d₀ hα2 a b hb (χ₂ σ) t d
      (by rw [← hab]; exact ht.symm) (by rw [← hab]; exact hd.symm)

private theorem exists_matrixRep_of_two_characters {k K G : Type} [Field k] [Finite k] [Field K]
    [Group G] (e : k →+* K) (χ₁ χ₂ : G →* K)
    (hs : ∀ σ, χ₁ σ + χ₂ σ ∈ e.range) (hp : ∀ σ, χ₁ σ * χ₂ σ ∈ e.range) :
    ∃ ρ : G →* Matrix (Fin 2) (Fin 2) k,
      (∀ σ, e (ρ σ).trace = χ₁ σ + χ₂ σ ∧ e (ρ σ).det = χ₁ σ * χ₂ σ) ∧
      (∀ σ τ, ρ σ * ρ τ = ρ τ * ρ σ) ∧
      ∀ σ, χ₁ σ = 1 → χ₂ σ = 1 → ρ σ = 1 := by
  classical
  by_cases hall : ∀ σ, χ₁ σ ∈ e.range
  ·
    have hall₂ : ∀ σ, χ₂ σ ∈ e.range := fun σ => by
      have h := sub_mem (hs σ) (hall σ)
      rwa [add_sub_cancel_left] at h
    choose f₁ hf₁ using fun σ => RingHom.mem_range.mp (hall σ)
    choose f₂ hf₂ using fun σ => RingHom.mem_range.mp (hall₂ σ)
    have hf₁1 : f₁ 1 = 1 := e.injective (by simp only [hf₁, map_one])
    have hf₂1 : f₂ 1 = 1 := e.injective (by simp only [hf₂, map_one])
    have hf₁m : ∀ σ τ, f₁ (σ * τ) = f₁ σ * f₁ τ := fun σ τ =>
      e.injective (by simp only [hf₁, map_mul])
    have hf₂m : ∀ σ τ, f₂ (σ * τ) = f₂ σ * f₂ τ := fun σ τ =>
      e.injective (by simp only [hf₂, map_mul])
    refine ⟨{ toFun := fun σ => Matrix.of ![![f₁ σ, 0], ![0, f₂ σ]]
              map_one' := ?_
              map_mul' := ?_ }, ?_, ?_, ?_⟩
    · ext i j
      fin_cases i <;> fin_cases j <;> simp [hf₁1, hf₂1]
    · intro σ τ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hf₁m, hf₂m, Matrix.mul_apply, Fin.sum_univ_two]
    · intro σ
      refine ⟨?_, ?_⟩
      · simp [Matrix.trace_fin_two, hf₁, hf₂]
      · simp [Matrix.det_fin_two, hf₁, hf₂]
    · intro σ τ
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
    · intro σ h₁ h₂
      have g₁ : f₁ σ = 1 := e.injective (by rw [hf₁, h₁, map_one])
      have g₂ : f₂ σ = 1 := e.injective (by rw [hf₂, h₂, map_one])
      ext i j
      fin_cases i <;> fin_cases j <;> simp [g₁, g₂]
  ·
    obtain ⟨τ₀, hα⟩ := not_forall.mp hall
    obtain ⟨t₀, ht₀⟩ := RingHom.mem_range.mp (hs τ₀)
    obtain ⟨d₀, hd₀⟩ := RingHom.mem_range.mp (hp τ₀)
    have hα2 : χ₁ τ₀ * χ₁ τ₀ = e t₀ * χ₁ τ₀ - e d₀ := by linear_combination hd₀ - χ₁ τ₀ * ht₀

    have hmem : ∀ σ, ∃ ab : k × k, χ₁ σ = e ab.1 + e ab.2 * χ₁ τ₀ := by
      intro σ
      obtain ⟨t, ht⟩ := RingHom.mem_range.mp (hs σ)
      obtain ⟨d, hd⟩ := RingHom.mem_range.mp (hp σ)
      have hx : χ₁ σ * χ₁ σ = e t * χ₁ σ - e d := by linear_combination hd - χ₁ σ * ht
      obtain ⟨a, b, hab⟩ := exists_quadCoords e (χ₁ τ₀) hα t₀ d₀ hα2 (χ₁ σ) t d hx
      exact ⟨(a, b), hab⟩
    choose c hc using hmem
    have hconj : ∀ σ, χ₂ σ = e ((c σ).1 + (c σ).2 * t₀) - e (c σ).2 * χ₁ τ₀ := fun σ =>
      chi2_eq_conj e χ₁ χ₂ hs hp τ₀ hα t₀ d₀ ht₀.symm hd₀.symm σ (c σ).1 (c σ).2 (hc σ)
    have hinj := quadCoords_injective e (χ₁ τ₀) hα
    have hc1 : c 1 = (1, 0) := hinj (by
      change e (c 1).1 + e (c 1).2 * χ₁ τ₀ = e 1 + e 0 * χ₁ τ₀
      rw [← hc 1, map_one, map_one, map_zero, zero_mul, add_zero])
    have hcm : ∀ σ τ, c (σ * τ) = quadMul t₀ d₀ (c σ) (c τ) := fun σ τ => hinj (by
      change e (c (σ * τ)).1 + e (c (σ * τ)).2 * χ₁ τ₀
        = e (quadMul t₀ d₀ (c σ) (c τ)).1 + e (quadMul t₀ d₀ (c σ) (c τ)).2 * χ₁ τ₀
      rw [embed_quadMul e (χ₁ τ₀) t₀ d₀ hα2, ← hc (σ * τ), ← hc σ, ← hc τ, map_mul])
    refine ⟨{ toFun := fun σ => quadMat t₀ d₀ (c σ)
              map_one' := ?_
              map_mul' := ?_ }, ?_, ?_, ?_⟩
    · show quadMat t₀ d₀ (c 1) = 1
      rw [hc1, quadMat_one]
    · intro σ τ
      show quadMat t₀ d₀ (c (σ * τ)) = quadMat t₀ d₀ (c σ) * quadMat t₀ d₀ (c τ)
      rw [hcm, quadMat_mul]
    · intro σ
      refine ⟨?_, ?_⟩
      · show e (quadMat t₀ d₀ (c σ)).trace = χ₁ σ + χ₂ σ
        rw [quadMat_trace, hc σ, hconj σ]
        simp only [map_add, map_mul]
        ring
      · show e (quadMat t₀ d₀ (c σ)).det = χ₁ σ * χ₂ σ
        rw [quadMat_det, hc σ, hconj σ]
        simp only [map_add, map_mul]
        linear_combination (e (c σ).2 * e (c σ).2) * hα2
    · intro σ τ
      show quadMat t₀ d₀ (c σ) * quadMat t₀ d₀ (c τ) = quadMat t₀ d₀ (c τ) * quadMat t₀ d₀ (c σ)
      rw [quadMat_mul, quadMat_mul, quadMul_comm]
    · intro σ h₁ _
      show quadMat t₀ d₀ (c σ) = 1
      have : c σ = (1, 0) := hinj (by
        change e (c σ).1 + e (c σ).2 * χ₁ τ₀ = e 1 + e 0 * χ₁ τ₀
        rw [← hc σ, h₁, map_one, map_zero, zero_mul, add_zero])
      rw [this, quadMat_one]

private theorem exists_matrixRep_of_characters
    (k : Type) [Field k] [Finite k] (K : Type) [Field K] (ι' : k →+* K)
    (χ₁ χ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* K)
    (hs : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, χ₁ σ + χ₂ σ ∈ ι'.range)
    (hp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, χ₁ σ * χ₂ σ ∈ ι'.range) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k,
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ι' (ρ σ).trace = χ₁ σ + χ₂ σ ∧ ι' (ρ σ).det = χ₁ σ * χ₂ σ) ∧
      (∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ) ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, χ₁ σ = 1 → χ₂ σ = 1 → ρ σ = 1 := by
  exact exists_matrixRep_of_two_characters ι' χ₁ χ₂ hs hp

private theorem exists_matrixRep_descend_forall_of_span_ne_top
    (k : Type) [Field k] [Finite k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (hrange : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ' σ).trace ∈ ι.range ∧ (ρ' σ).det ∈ ι.range)
    (hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) ≠ ⊤) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        ι (ρ σ).trace = (ρ' σ).trace ∧ ι (ρ σ).det = (ρ' σ).det) ∧
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ := by
  obtain ⟨K, _, j, χ₁, χ₂, hχ, hker⟩ := exists_characters_of_span_ne_top k' ρ' hspan

  have hs : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, χ₁ σ + χ₂ σ ∈ (j.comp ι).range := by
    intro σ
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (hrange σ).1
    exact RingHom.mem_range.mpr ⟨a, by rw [RingHom.comp_apply, ha, (hχ σ).1]⟩
  have hp : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, χ₁ σ * χ₂ σ ∈ (j.comp ι).range := by
    intro σ
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp (hrange σ).2
    exact RingHom.mem_range.mpr ⟨a, by rw [RingHom.comp_apply, ha, (hχ σ).2]⟩
  obtain ⟨ρ, htd, hcomm, hone⟩ := exists_matrixRep_of_characters k K (j.comp ι) χ₁ χ₂ hs hp
  refine ⟨ρ, ?_, ?_, hcomm⟩
  ·
    obtain ⟨L, hL, h1⟩ := hρ'
    refine ⟨L, hL, fun σ hσ => ?_⟩
    obtain ⟨h₁, h₂⟩ := hker σ (h1 σ hσ)
    exact hone σ h₁ h₂
  ·
    intro σ
    refine ⟨j.injective ?_, j.injective ?_⟩
    · rw [(hχ σ).1]
      exact (htd σ).1
    · rw [(hχ σ).2]
      exact (htd σ).2

private theorem frobenius_clause_of_forall
    (k : Type) [Field k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (S : Finset ℕ) (t d : ∀ ℓ : ℕ, ℓ.Prime → k)
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ' σ).trace = ι (t ℓ hℓ) ∧ (ρ' σ).det = ι (d ℓ hℓ))
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    (htd : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      ι (ρ σ).trace = (ρ' σ).trace ∧ ι (ρ σ).det = (ρ' σ).det) :
    ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ σ).trace = t ℓ hℓ ∧ (ρ σ).det = d ℓ hℓ := by
  intro ℓ hℓ hℓS A hA σ hσ
  obtain ⟨ht, hd⟩ := hfrob ℓ hℓ hℓS A hA σ hσ
  exact ⟨ι.injective ((htd σ).1.trans ht), ι.injective ((htd σ).2.trans hd)⟩

private theorem exists_matrixRep_descend_of_span_ne_top
    (k : Type) [Field k] [Finite k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ) (t d : ∀ ℓ : ℕ, ℓ.Prime → k)
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ' σ).trace = ι (t ℓ hℓ) ∧ (ρ' σ).det = ι (d ℓ hℓ))
    (hd : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → d ℓ hℓ = (ℓ : k))
    (hrange : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (ρ' σ).trace ∈ ι.range ∧ (ρ' σ).det ∈ ι.range)
    (hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) ≠ ⊤) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          (ρ σ).trace = t ℓ hℓ ∧ (ρ σ).det = d ℓ hℓ) ∧
      ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ := by
  have _ := hd
  obtain ⟨ρ, hρ, htd, hcomm⟩ := exists_matrixRep_descend_forall_of_span_ne_top k k' ι ρ' hρ' hrange hspan
  exact ⟨ρ, hρ, frobenius_clause_of_forall k k' ι ρ' S t d hfrob ρ htd, hcomm⟩

private theorem exists_matrixRep_descend
    (k : Type) [Field k] [Finite k] (k' : Type) [Field k'] (ι : k →+* k')
    (ρ' : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k')
    (hρ' : GaloisFactorsThroughFiniteLevel ρ')
    (S : Finset ℕ) (t d : ∀ ℓ : ℕ, ℓ.Prime → k)
    (hfrob : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
      A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
        (ρ' σ).trace = ι (t ℓ hℓ) ∧ (ρ' σ).det = ι (d ℓ hℓ))
    (hd : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → d ℓ hℓ = (ℓ : k)) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k,
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          (ρ σ).trace = t ℓ hℓ ∧ (ρ σ).det = d ℓ hℓ) ∧
      (Submodule.span k (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤ ∨
        ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ) := by
  have hrange := trace_mem_range_and_det_mem_range k k' ι ρ' hρ' S t d hfrob
  by_cases hspan : Submodule.span k' (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ' g)) = ⊤
  · obtain ⟨ρ, hlev, -, hfrobρ, hsp⟩ :=
      exists_matrixRep_descend_of_span_eq_top k k' ι ρ' hρ' S t d hfrob hd hrange hspan
    exact ⟨ρ, hlev, hfrobρ, Or.inl hsp⟩
  · obtain ⟨ρ, hlev, hfrobρ, hcomm⟩ :=
      exists_matrixRep_descend_of_span_ne_top k k' ι ρ' hρ' S t d hfrob hd hrange hspan
    exact ⟨ρ, hlev, hfrobρ, Or.inr hcomm⟩

theorem solution
    (M : ℕ) [NeZero M] (𝔪 : Ideal HeckeAlg) [𝔪.IsMaximal]
    (hsupp : letI := heckeModuleBar M; heckeTorsion (JZero M) 𝔪 ≠ ⊥) :
    ∃ ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) (HeckeAlg ⧸ 𝔪),
      GaloisFactorsThroughFiniteLevel ρ ∧
      (∃ S : Finset ℕ, ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ℓ ∉ S → ∀ (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime ℓ → ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), A.IsFrobeniusAt σ ℓ →
          Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩) = (ρ σ).trace ∧
            Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)) = (ρ σ).det) ∧
      (Submodule.span (HeckeAlg ⧸ 𝔪)
          (Set.range (fun g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) => ρ g)) = ⊤ ∨
        ∀ σ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ρ σ * ρ τ = ρ τ * ρ σ) := by
  obtain ⟨hfin, p, hp, -, O, _, _, _, i₀, hpO, θ, ⟨K, _, _, _, Λ, hΛ, hθ⟩, ι, hι⟩ :=
    exists_heckeChar_liesOver M 𝔪 hsupp
  obtain ⟨ρad, hchar, -⟩ :=
    ModularCurve.exists_galoisRepAdic_charpoly_frobenius_of_heckeChar M p O K i₀ hpO Λ hΛ
  obtain ⟨ρ', hρ', htd⟩ := exists_matrixRep_residual O ρad
  haveI := hfin
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have hMp : M * p ≠ 0 := Nat.mul_ne_zero (NeZero.ne M) hp.out.ne_zero
  obtain ⟨ρ, hρ, hfrob, hss⟩ :=
    exists_matrixRep_descend (HeckeAlg ⧸ 𝔪) (IsLocalRing.ResidueField O) ι ρ' hρ' (M * p).primeFactors
      (fun ℓ hℓ => Ideal.Quotient.mk 𝔪 (heckeGen ⟨ℓ, hℓ⟩)) (fun ℓ _ => Ideal.Quotient.mk 𝔪 ((ℓ : HeckeAlg)))
      (by
        intro ℓ hℓ hℓS A hA σ hσ
        have hndvd : ¬ ℓ ∣ M * p := fun h => hℓS (Nat.mem_primeFactors.mpr ⟨hℓ, h, hMp⟩)
        obtain ⟨htr, hdet⟩ :=
          htd σ (θ (heckeGen ⟨ℓ, hℓ⟩)) (ℓ : O) (hchar ℓ hℓ hndvd _ (hθ (heckeGen ⟨ℓ, hℓ⟩)) A hA σ hσ)
        refine ⟨htr.trans (hι _), hdet.trans ?_⟩
        simp only [map_natCast])
      (fun ℓ _ _ => map_natCast (Ideal.Quotient.mk 𝔪) ℓ)
  exact ⟨ρ, hρ, ⟨(M * p).primeFactors, fun ℓ hℓ hℓS A hA σ hσ =>
    ⟨(hfrob ℓ hℓ hℓS A hA σ hσ).1.symm, (hfrob ℓ hℓ hℓS A hA σ hσ).2.symm⟩⟩, hss⟩

#print axioms solution

end S_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot
end P2MW
export P2MW.S_ModularCurve_exists_matrixRep_trace_det_frobenius_of_heckeTorsion_ne_bot (solution)
