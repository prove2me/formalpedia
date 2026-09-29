-- Prove2me | solution 1 for ModularCurve.exists_isMaximal_heckeTorsion_jZero_ne_bot_of_ringHom_heckeAlgebra_two
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/b03c9983-3b44-51e8-a3b1-6a048220bfcd

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_CuspForm_HeckeAlgebra
import Theorems.Thm_CuspForm_exists_isNormalizedEigenform_ker_of_isMaximal
import Theorems.Thm_CuspForm_moduleFinite_heckeAlgebra_two
import Theorems.Thm_ModularCurve_eigenIdeal_isMaximal
import Theorems.Thm_ModularCurve_eigenformSupportAt_jZero
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isMaximal_heckeTorsion_jZero_ne_bot_of_ringHom_heckeAlgebra_two
p2m_attr_erase "instance" "HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve"
p2m_attr_erase "instance" "WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff"
p2m_attr_erase "simp" "ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆"
p2m_attr_erase "simp" "PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆"
p2m_attr_erase "simp" "Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist"
p2m_attr_erase "simp" "ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU ModularCurve.dualHeckeRep_apply_apply ModularCurve.coe_segmentPath ModularCurve.cuspHeckeAeval_heckeGen ModularCurve.coe_periodLatticeRestrict_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap"
set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "heckeModuleBar JZero HeckeAlg heckeGen aeval_heckeGen eigenIdeal mem_eigenIdeal_iff heckeTorsion eigenIdeal_isMaximal eigenformSupportAt_jZero IsEigenformIdeal heckeInputsAll heckeOperatorsCommuteBar"
namespace ResidualEigensystemOccurrence
p2m_open "ModularCurve"

section Contraction

open CuspForm

private theorem finite_of_natCast_eq_zero_of_moduleFinite (R : Type*) [CommRing R] [Module.Finite ℤ R]
    {p : ℕ} (hp : p.Prime) (hpR : (p : R) = 0) : Finite R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  letI : Module (ZMod p) R :=
    AddCommMonoid.zmodModule (fun x => by rw [nsmul_eq_mul, hpR, zero_mul])
  haveI hf : Module.Finite (ZMod p) R := Module.Finite.of_restrictScalars_finite ℤ (ZMod p) R
  exact @Module.finite_of_finite (ZMod p) R _ _ _ _ hf

private theorem isMaximal_ker (N : ℕ) [NeZero N] (S : Set ℕ) (p : ℕ) [Fact p.Prime]
    {F : Type} [Field F] [CharP F p] (θ : CuspForm.heckeAlgebra N 2 S →+* F) :
    (RingHom.ker θ).IsMaximal := by

  haveI : Module.Finite ℤ (heckeAlgebra N 2 S) := CuspForm.moduleFinite_heckeAlgebra_two N S
  haveI : Module.Finite ℤ θ.range :=
    Module.Finite.of_surjective θ.rangeRestrict.toAddMonoidHom.toIntLinearMap θ.rangeRestrict_surjective
  have hpr : ((p : ℕ) : θ.range) = 0 := by
    rw [← map_natCast θ.rangeRestrict p]
    exact Subtype.ext (by
      rw [RingHom.coe_rangeRestrict, map_natCast, ZeroMemClass.coe_zero]
      exact CharP.cast_eq_zero F p)
  haveI : Finite θ.range := finite_of_natCast_eq_zero_of_moduleFinite θ.range (Fact.out : p.Prime) hpr
  letI : Field θ.range := (Finite.isField_of_domain θ.range).toField
  rw [← RingHom.ker_rangeRestrict θ]
  exact RingHom.ker_isMaximal_of_surjective θ.rangeRestrict θ.rangeRestrict_surjective

private theorem exists_isMaximal_comap_inclusion_eq (N : ℕ) [NeZero N] (S : Set ℕ)
    (I : Ideal (CuspForm.heckeAlgebra N 2 S)) (hI : I.IsMaximal) :
    ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 ∅), 𝔪₁.IsMaximal ∧
      𝔪₁.comap (Subalgebra.inclusion
        (CuspForm.heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))).toRingHom = I := by
  haveI := hI
  letI : Algebra (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) :=
    (Subalgebra.inclusion (heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))).toRingHom.toAlgebra
  haveI : IsScalarTower ℤ (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) :=
    IsScalarTower.of_algebraMap_eq fun z =>
      ((Subalgebra.inclusion (heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))).commutes z).symm
  haveI : Module.Finite ℤ (heckeAlgebra N 2 ∅) := CuspForm.moduleFinite_heckeAlgebra_two N ∅
  haveI : Algebra.IsIntegral (heckeAlgebra N 2 S) (heckeAlgebra N 2 ∅) :=
    Algebra.IsIntegral.tower_top (R := ℤ)
  obtain ⟨Q, hQ, hQcomap⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral
    (S := heckeAlgebra N 2 ∅) I (by
      intro x hx
      rw [RingHom.mem_ker] at hx
      have hx0 : x = 0 :=
        Subalgebra.inclusion_injective (heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))
          (by rw [map_zero]; exact hx)
      rw [hx0]; exact Ideal.zero_mem _)
  exact ⟨Q, hQ, hQcomap⟩

private theorem exists_isMaximal_comap_eq_ker (N : ℕ) [NeZero N] (S : Set ℕ) (p : ℕ) [Fact p.Prime]
    {F : Type} [Field F] [CharP F p] (θ : CuspForm.heckeAlgebra N 2 S →+* F) :
    (RingHom.ker θ).IsMaximal ∧
      ∃ 𝔪₁ : Ideal (CuspForm.heckeAlgebra N 2 ∅), 𝔪₁.IsMaximal ∧
        𝔪₁.comap (Subalgebra.inclusion
          (CuspForm.heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))).toRingHom =
          RingHom.ker θ :=
  ⟨isMaximal_ker N S p θ, exists_isMaximal_comap_inclusion_eq N S _ (isMaximal_ker N S p θ)⟩

end Contraction

private theorem exists_ringHom_algebraicClosure_comp_eq {R₀ k F : Type*} [Field R₀] [Field k] [Finite k]
    [Field F] (f : R₀ →+* k) (g : R₀ →+* F) :
    ∃ ι : k →+* AlgebraicClosure F,
      ∀ r : R₀, ι (f r) = algebraMap F (AlgebraicClosure F) (g r) := by
  letI : Algebra R₀ k := f.toAlgebra
  letI : Algebra R₀ (AlgebraicClosure F) := ((algebraMap F (AlgebraicClosure F)).comp g).toAlgebra
  haveI : Module.Finite R₀ k := Module.Finite.of_finite
  haveI : Algebra.IsAlgebraic R₀ k := Algebra.IsAlgebraic.of_finite R₀ k
  let φ : k →ₐ[R₀] AlgebraicClosure F := IsAlgClosed.lift
  refine ⟨φ.toRingHom, fun r => ?_⟩
  have h1 : f r = algebraMap R₀ k r := rfl
  have h2 : algebraMap R₀ (AlgebraicClosure F) r = algebraMap F (AlgebraicClosure F) (g r) := rfl
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, h1, φ.commutes r, h2]

private theorem exists_ringHom_comp_eq {R : Type} [CommRing R] {F : Type} [Field F]
    {k : Type} [Field k] [Finite k] (θ : R →+* F) (hθ : (RingHom.ker θ).IsMaximal)
    (ψ : R →+* k) (h : ∀ t : R, θ t = 0 → ψ t = 0) :
    ∃ (F' : Type) (_ : Field F') (e : F →+* F') (j : k →+* F'), ∀ t : R, j (ψ t) = e (θ t) := by
  haveI : (RingHom.ker θ).IsMaximal := hθ
  letI : Field (R ⧸ RingHom.ker θ) := Ideal.Quotient.field (RingHom.ker θ)
  let f₀ : R ⧸ RingHom.ker θ →+* k :=
    Ideal.Quotient.lift (RingHom.ker θ) ψ (fun t ht => h t (RingHom.mem_ker.1 ht))
  let g₀ : R ⧸ RingHom.ker θ →+* F := RingHom.kerLift θ
  obtain ⟨ι, hι⟩ := exists_ringHom_algebraicClosure_comp_eq f₀ g₀
  refine ⟨AlgebraicClosure F, inferInstance, algebraMap F (AlgebraicClosure F), ι, fun t => ?_⟩
  have h1 : ψ t = f₀ (Ideal.Quotient.mk (RingHom.ker θ) t) := (Ideal.Quotient.lift_mk _ _ _).symm
  have h2 : θ t = g₀ (Ideal.Quotient.mk (RingHom.ker θ) t) := (RingHom.kerLift_mk θ t).symm
  rw [h1, h2]
  exact hι _

end ModularCurve.ResidualEigensystemOccurrence

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (S : Set ℕ)
    {F : Type} [Field F] [CharP F p] (θ : CuspForm.heckeAlgebra N 2 S →+* F) :
    letI := ModularCurve.heckeModuleBar N
    ∃ 𝔪 : Ideal ModularCurve.HeckeAlg, 𝔪.IsMaximal ∧
      ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪 ∧
      Finite (ModularCurve.HeckeAlg ⧸ 𝔪) ∧
      ModularCurve.heckeTorsion (ModularCurve.JZero N) 𝔪 ≠ ⊥ ∧
      ∃ (F' : Type) (_ : Field F') (e : F →+* F') (ι : ModularCurve.HeckeAlg ⧸ 𝔪 →+* F'),
        ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
          ι (Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩)) =
            e (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨hθmax, 𝔪₁, h𝔪₁, hcomap⟩ :=
    ModularCurve.ResidualEigensystemOccurrence.exists_isMaximal_comap_eq_ker N S p θ
  obtain ⟨f, hf, k, hkF, hkfin, 𝒪, h𝒪, φ, χ, hker, hT, -⟩ :=
    CuspForm.exists_isNormalizedEigenform_ker_of_isMaximal N 𝔪₁ h𝔪₁

  let incl : CuspForm.heckeAlgebra N 2 S →+* CuspForm.heckeAlgebra N 2 ∅ :=
    (Subalgebra.inclusion (CuspForm.heckeAlgebra_mono (N := N) (k := 2) (Set.empty_subset S))).toRingHom
  let ψ : CuspForm.heckeAlgebra N 2 S →+* k := χ.comp incl
  have hψ : ∀ t, θ t = 0 → ψ t = 0 := by
    intro t ht
    have h1 : t ∈ RingHom.ker θ := RingHom.mem_ker.mpr ht
    rw [← hcomap, Ideal.mem_comap, hker, RingHom.mem_ker] at h1
    exact h1
  have hψT : ∀ (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) (hℓS : ℓ ∉ S),
      ψ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) = φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ⟨ℓ, hℓ⟩⟩ := by
    intro ℓ hℓ hℓN hℓS
    have h1 : incl (CuspForm.heckeAlgebra.T hℓ hℓN hℓS) =
        CuspForm.heckeAlgebra.T hℓ hℓN (Set.notMem_empty ℓ) := Subtype.ext rfl
    show χ (incl (CuspForm.heckeAlgebra.T hℓ hℓN hℓS)) = _
    rw [h1]
    exact hT ⟨ℓ, hℓ⟩ hℓN (Set.notMem_empty ℓ)

  have hpk : (p : k) = 0 := by
    have h1 := hψ (p : CuspForm.heckeAlgebra N 2 S) (by rw [map_natCast]; exact CharP.cast_eq_zero F p)
    rwa [map_natCast] at h1

  obtain ⟨𝔪, h𝔪⟩ : ∃ 𝔪 : Ideal ModularCurve.HeckeAlg,
      𝔪 = ModularCurve.eigenIdeal (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) := ⟨_, rfl⟩
  have hEig : ModularCurve.IsEigenformIdeal N 𝔪 := ⟨f, hf, k, hkF, hkfin, 𝒪, h𝒪, φ, h𝔪⟩
  have hmax : 𝔪.IsMaximal := h𝔪 ▸ ModularCurve.eigenIdeal_isMaximal _
  have hmem : ∀ t : ModularCurve.HeckeAlg,
      t ∈ 𝔪 ↔ MvPolynomial.aeval (R := ℤ) (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) t = 0 := by
    intro t
    rw [h𝔪, ModularCurve.mem_eigenIdeal_iff]
  have hpm : ((p : ℕ) : ModularCurve.HeckeAlg) ∈ 𝔪 := by
    rw [hmem, map_natCast, hpk]
  have hfin : Finite (ModularCurve.HeckeAlg ⧸ 𝔪) := by
    subst h𝔪
    haveI : Finite (MvPolynomial.aeval (R := ℤ)
        (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) : ModularCurve.HeckeAlg →ₐ[ℤ] k).range :=
      Subtype.finite
    exact Finite.of_equiv _ (Ideal.quotientKerEquivRange (MvPolynomial.aeval (R := ℤ)
      (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩))).symm.toEquiv

  obtain ⟨F', hF', e, j, hj⟩ :=
    ModularCurve.ResidualEigensystemOccurrence.exists_ringHom_comp_eq θ hθmax ψ hψ
  let ι₀ : ModularCurve.HeckeAlg ⧸ 𝔪 →+* k :=
    Ideal.Quotient.lift 𝔪
      (MvPolynomial.aeval (R := ℤ) (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) :
        ModularCurve.HeckeAlg →+* k)
      (fun t ht => (hmem t).mp ht)
  refine ⟨𝔪, hmax, hpm, hfin, ?_, F', hF', e, j.comp ι₀, ?_⟩
  ·
    exact ModularCurve.eigenformSupportAt_jZero N p hp (ModularCurve.heckeInputsAll N)
      (ModularCurve.heckeOperatorsCommuteBar N) 𝔪 hEig hpm
  · intro ℓ hℓ hℓN hℓS
    show j (ι₀ (Ideal.Quotient.mk 𝔪 (ModularCurve.heckeGen ⟨ℓ, hℓ⟩))) =
      e (θ (CuspForm.heckeAlgebra.T hℓ hℓN hℓS))
    rw [← hj, hψT ℓ hℓ hℓN hℓS]
    congr 1
    show (MvPolynomial.aeval (R := ℤ) (fun ℓ : Nat.Primes => φ ⟨ModularFormClass.qCoeff f ℓ, h𝒪 ℓ⟩) :
        ModularCurve.HeckeAlg →+* k) (ModularCurve.heckeGen ⟨ℓ, hℓ⟩) = _
    rw [RingHom.coe_coe, ModularCurve.aeval_heckeGen]

end S_ModularCurve_exists_isMaximal_heckeTorsion_jZero_ne_bot_of_ringHom_heckeAlgebra_two
end P2MW
export P2MW.S_ModularCurve_exists_isMaximal_heckeTorsion_jZero_ne_bot_of_ringHom_heckeAlgebra_two (solution)
