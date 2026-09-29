-- Prove2me | solution 1 for ModularCurve.exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5109e777-1df9-5cbd-acca-a26db5032818

import Mathlib
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice
import Theorems.Thm_Ideal_exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice
import Theorems.Thm_ModularCurve_natCard_torsion_jZero_eq_pow_finrank_periodLattice
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Theorems.Thm_Submodule_natCard_torsionBy_quotient_eq_pow_finrank
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply"
p2m_attr_erase "simp" "HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply"

noncomputable section

namespace P2MR2LB

open Module

section Transfer

variable {R T : Type*} [CommRing R] [CommRing T] (φ : R →+* T) (hφ : Function.Surjective φ)
variable {𝕜 : Type*} [Field 𝕜] {D : Type*} [AddCommGroup D] [Module 𝕜 D]
variable (ρ : R →+* Module.End 𝕜 D) (hker : ∀ a, φ a = 0 → ρ a = 0)

def τ : T →+* Module.End 𝕜 D :=
  φ.liftOfSurjective hφ ⟨ρ, fun a ha => by
    rw [RingHom.mem_ker] at ha ⊢
    exact hker a ha⟩

theorem τ_φ (a : R) : τ φ hφ ρ hker (φ a) = ρ a :=
  φ.liftOfSurjective_comp_apply hφ ⟨ρ, _⟩ a

theorem τ_natCast (c : ℕ) (x : D) : τ φ hφ ρ hker (c : T) x = (c : 𝕜) • x := by
  rw [map_natCast, Module.End.natCast_apply, Nat.cast_smul_eq_nsmul]

variable (v w : D)

def ι : T × T →+ D where
  toFun p := τ φ hφ ρ hker p.1 v + τ φ hφ ρ hker p.2 w
  map_zero' := by simp
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, LinearMap.add_apply]
    abel

theorem ι_apply (p : T × T) :
    ι φ hφ ρ hker v w p = τ φ hφ ρ hker p.1 v + τ φ hφ ρ hker p.2 w := rfl

theorem ι_φ (a b : R) : ι φ hφ ρ hker v w (φ a, φ b) = ρ a v + ρ b w := by
  rw [ι_apply, τ_φ, τ_φ]

theorem ρ_ι (a : R) (p : T × T) :
    ρ a (ι φ hφ ρ hker v w p) = ι φ hφ ρ hker v w (φ a • p) := by
  rw [ι_apply, ι_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
    τ_φ, map_add, Module.End.mul_apply, Module.End.mul_apply]

theorem ι_natCast_smul (c : ℕ) (p : T × T) :
    ι φ hφ ρ hker v w ((c : T) • p) = (c : 𝕜) • ι φ hφ ρ hker v w p := by
  rw [ι_apply, ι_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
    Module.End.mul_apply, Module.End.mul_apply, τ_natCast, τ_natCast, smul_add]

variable (Λ : Submodule ℤ D) (hΛ : ∀ (a : R) (x : D), x ∈ Λ → ρ a x ∈ Λ) (hv : v ∈ Λ) (hw : w ∈ Λ)

include hΛ in
theorem τ_mem (s : T) (x : D) (hx : x ∈ Λ) : τ φ hφ ρ hker s x ∈ Λ := by
  obtain ⟨a, rfl⟩ := hφ s
  rw [τ_φ]
  exact hΛ a x hx

include hΛ hv hw in
theorem ι_mem (p : T × T) : ι φ hφ ρ hker v w p ∈ Λ :=
  Λ.add_mem (τ_mem φ hφ ρ hker Λ hΛ _ v hv) (τ_mem φ hφ ρ hker Λ hΛ _ w hw)

variable (hinj : ∀ a b : R, ρ a v + ρ b w = 0 → φ a = 0 ∧ φ b = 0)

include hinj in
theorem ι_injective : Function.Injective (ι φ hφ ρ hker v w) := by
  refine (injective_iff_map_eq_zero _).mpr fun p hp => ?_
  obtain ⟨a, ha⟩ := hφ p.1
  obtain ⟨b, hb⟩ := hφ p.2
  have hp' : ι φ hφ ρ hker v w (φ a, φ b) = 0 := by rw [ha, hb]; exact hp
  rw [ι_φ] at hp'
  obtain ⟨h1, h2⟩ := hinj a b hp'
  ext
  · rw [← ha, h1]; rfl
  · rw [← hb, h2]; rfl

variable (𝔍 : Ideal T) (c : ℕ)

abbrev 𝔮 : AddSubgroup T := (Ideal.span {(c : T)}).toAddSubgroup

omit hφ in
theorem mem_𝔮 {x : T} : x ∈ 𝔮 (T := T) c ↔ ∃ a : T, a * c = x := by
  change x ∈ Ideal.span {(c : T)} ↔ _
  exact Ideal.mem_span_singleton'

private def _root_.P2MR2LB.X : AddSubgroup T where
  carrier := {x | ∀ j ∈ 𝔍, j * x ∈ Ideal.span {(c : T)}}
  zero_mem' := fun j _ => by simp
  add_mem' := fun {x y} hx hy j hj => by
    simp only [mul_add]
    exact Ideal.add_mem _ (hx j hj) (hy j hj)
  neg_mem' := fun {x} hx j hj => by
    simp only [mul_neg]
    exact Submodule.neg_mem _ (hx j hj)

p2m_export "P2MR2LB" "X"
omit hφ in
theorem mem_X {x : T} : x ∈ X 𝔍 c ↔ ∀ j ∈ 𝔍, j * x ∈ Ideal.span {(c : T)} := Iff.rfl

omit hφ in
theorem 𝔮_le_X : 𝔮 (T := T) c ≤ X 𝔍 c := fun _ hx _ _ => Ideal.mul_mem_left _ _ hx

omit hφ in

theorem natCard_torsionBySet_eq_relIndex :
    Nat.card ↥(Submodule.torsionBySet T (T ⧸ Ideal.span {(c : T)}) (𝔍 : Set T)) =
      (𝔮 (T := T) c).relIndex (X 𝔍 c) := by
  have hk : ((Ideal.Quotient.mk (Ideal.span {(c : T)})).toAddMonoidHom).ker = 𝔮 (T := T) c := by
    ext x
    rw [AddMonoidHom.mem_ker]
    exact Ideal.Quotient.eq_zero_iff_mem
  rw [← hk, AddSubgroup.relIndex_ker]
  symm
  refine Nat.card_congr (Equiv.subtypeEquivRight fun y => ?_)
  change y ∈ AddSubgroup.map _ (X 𝔍 c) ↔ y ∈ Submodule.torsionBySet _ _ _
  rw [AddSubgroup.mem_map, Submodule.mem_torsionBySet_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩ ⟨a, ha⟩
    change Ideal.Quotient.mk _ (a * x) = 0
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact hx a ha
  · intro hy
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨x, ?_, rfl⟩
    rw [mem_X]
    intro a ha
    have := hy ⟨a, ha⟩
    change Ideal.Quotient.mk _ (a * x) = 0 at this
    rwa [Ideal.Quotient.eq_zero_iff_mem] at this

variable [CharZero 𝕜]
variable {G : Type*} [AddCommGroup G] [Module R G] (u : G →+ D ⧸ Λ)
  (hu_inj : Function.Injective u) (hu_fin : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
  (hu_eq : ∀ (a : R) (x : G) (ψ : D), u x = Λ.mkQ ψ → u (a • x) = Λ.mkQ (ρ a ψ))
variable (d : ℕ) (hd : d ≠ 0) (hgen : ∀ x ∈ Λ, ∃ a b : R, (d : 𝕜) • x = ρ a v + ρ b w)
variable (S : Set R) (hS : ∀ a ∈ S, φ a ∈ 𝔍) (hc : c ≠ 0)

def Ψ : ↥(X 𝔍 c) × ↥(X 𝔍 c) →+ D ⧸ Λ where
  toFun p := Λ.mkQ (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T)))
  map_zero' := by
    have : (((0 : ↥(X 𝔍 c) × ↥(X 𝔍 c)).1 : T), ((0 : ↥(X 𝔍 c) × ↥(X 𝔍 c)).2 : T)) = (0 : T × T) := rfl
    rw [this, map_zero, smul_zero, map_zero]
  map_add' p p' := by
    have : (((p + p').1 : T), ((p + p').2 : T)) = ((p.1 : T), (p.2 : T)) + ((p'.1 : T), (p'.2 : T)) := rfl
    rw [this, map_add, smul_add, map_add]

omit [CharZero 𝕜] in
theorem Ψ_apply (p : ↥(X 𝔍 c) × ↥(X 𝔍 c)) :
    Ψ φ hφ ρ hker v w Λ 𝔍 c p = Λ.mkQ (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T))) := rfl

abbrev L' : Submodule ℤ D := LinearMap.range (ι φ hφ ρ hker v w).toIntLinearMap

def hmap : ↥(X 𝔍 c) × ↥(X 𝔍 c) →+ D ⧸ L' φ hφ ρ hker v w where
  toFun p := (L' φ hφ ρ hker v w).mkQ (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T)))
  map_zero' := by
    have : (((0 : ↥(X 𝔍 c) × ↥(X 𝔍 c)).1 : T), ((0 : ↥(X 𝔍 c) × ↥(X 𝔍 c)).2 : T)) = (0 : T × T) := rfl
    rw [this, map_zero, smul_zero, map_zero]
  map_add' p p' := by
    have : (((p + p').1 : T), ((p + p').2 : T)) = ((p.1 : T), (p.2 : T)) + ((p'.1 : T), (p'.2 : T)) := rfl
    rw [this, map_add, smul_add, map_add]

omit [CharZero 𝕜] in
theorem hmap_apply (p : ↥(X 𝔍 c) × ↥(X 𝔍 c)) :
    hmap φ hφ ρ hker v w 𝔍 c p =
      (L' φ hφ ρ hker v w).mkQ (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T))) := rfl

abbrev P₂ : AddSubgroup (↥(X 𝔍 c) × ↥(X 𝔍 c)) :=
  ((𝔮 (T := T) c).addSubgroupOf (X 𝔍 c)).prod ((𝔮 (T := T) c).addSubgroupOf (X 𝔍 c))

omit hφ in
theorem index_P₂ : (P₂ 𝔍 c).index = ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 := by
  rw [AddSubgroup.index_prod, sq]
  rfl

omit hφ in
theorem mem_P₂ {p : ↥(X 𝔍 c) × ↥(X 𝔍 c)} :
    p ∈ P₂ 𝔍 c ↔ (p.1 : T) ∈ 𝔮 (T := T) c ∧ (p.2 : T) ∈ 𝔮 (T := T) c := by
  rw [AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]

omit hφ in
theorem exists_of_mem_P₂ {p : ↥(X 𝔍 c) × ↥(X 𝔍 c)} (hp : p ∈ P₂ 𝔍 c) :
    ∃ q' : T × T, ((p.1 : T), (p.2 : T)) = (c : T) • q' := by
  rw [mem_P₂] at hp
  obtain ⟨a, ha⟩ := (mem_𝔮 c).mp hp.1
  obtain ⟨b, hb⟩ := (mem_𝔮 c).mp hp.2
  refine ⟨(a, b), ?_⟩
  rw [Prod.smul_mk, smul_eq_mul, smul_eq_mul, mul_comm (c : T) a, mul_comm (c : T) b, ha, hb]

include hc hΛ hv hw in
theorem P₂_le_ker : P₂ 𝔍 c ≤ (Ψ φ hφ ρ hker v w Λ 𝔍 c).ker := by
  intro p hp
  obtain ⟨q', hq'⟩ := exists_of_mem_P₂ 𝔍 c hp
  have hc' : (c : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hc
  rw [AddMonoidHom.mem_ker, Ψ_apply, hq', ι_natCast_smul, inv_smul_smul₀ hc', Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero]
  exact ι_mem φ hφ ρ hker v w Λ hΛ hv hw q'

include hinj hc in
theorem ker_hmap_le : (hmap φ hφ ρ hker v w 𝔍 c).ker ≤ P₂ 𝔍 c := by
  intro p hp
  rw [AddMonoidHom.mem_ker, hmap_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
  obtain ⟨q', hq'⟩ := hp
  change ι φ hφ ρ hker v w q' = _ at hq'
  have hc' : (c : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have h1 : ι φ hφ ρ hker v w ((c : T) • q') = ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T)) := by
    rw [ι_natCast_smul, hq', smul_inv_smul₀ hc']
  have h2 := ι_injective φ hφ ρ hker v w hinj h1
  rw [mem_P₂, mem_𝔮, mem_𝔮]
  have h3 : (p.1 : T) = (c : T) * q'.1 := by
    have := congrArg Prod.fst h2; simpa using this.symm
  have h4 : (p.2 : T) = (c : T) * q'.2 := by
    have := congrArg Prod.snd h2; simpa using this.symm
  exact ⟨⟨q'.1, by rw [h3, mul_comm]⟩, ⟨q'.2, by rw [h4, mul_comm]⟩⟩

include hgen in
omit [CharZero 𝕜] in
theorem map_ker_le :
    ((Ψ φ hφ ρ hker v w Λ 𝔍 c).ker).map (hmap φ hφ ρ hker v w 𝔍 c) ≤
      (Submodule.torsionBy ℤ (D ⧸ L' φ hφ ρ hker v w) (d : ℕ)).toAddSubgroup := by
  rintro _ ⟨p, hp, rfl⟩
  change (Ψ φ hφ ρ hker v w Λ 𝔍 c p) = 0 at hp
  rw [Ψ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hp
  obtain ⟨a, b, hab⟩ := hgen _ hp
  change hmap φ hφ ρ hker v w 𝔍 c p ∈ Submodule.torsionBy ℤ _ _
  rw [Submodule.mem_torsionBy_iff, hmap_apply, Submodule.mkQ_apply]
  change Submodule.Quotient.mk (((d : ℕ) : ℤ) •
      (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T)))) = (0 : D ⧸ L' φ hφ ρ hker v w)
  rw [Submodule.Quotient.mk_eq_zero, natCast_zsmul, ← Nat.cast_smul_eq_nsmul 𝕜, hab, ← ι_φ φ hφ ρ hker]
  exact ⟨(φ a, φ b), rfl⟩

include hΛ hv hw hu_inj hu_fin hu_eq hS hc in
theorem range_Ψ_subset :
    ((Ψ φ hφ ρ hker v w Λ 𝔍 c).range : Set (D ⧸ Λ)) ⊆ u '' (Submodule.torsionBySet R G S) := by
  rintro _ ⟨p, rfl⟩
  have hc' : (c : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hc
  set y := Ψ φ hφ ρ hker v w Λ 𝔍 c p with hy

  have hfin : IsOfFinAddOrder y := by
    refine (isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨c, Nat.pos_of_ne_zero hc, ?_⟩
    rw [hy, Ψ_apply, ← map_nsmul, ← Nat.cast_smul_eq_nsmul 𝕜, smul_inv_smul₀ hc', Submodule.mkQ_apply,
      Submodule.Quotient.mk_eq_zero]
    exact ι_mem φ hφ ρ hker v w Λ hΛ hv hw _
  obtain ⟨x, hx⟩ := hu_fin y hfin
  refine ⟨x, ?_, hx⟩
  rw [SetLike.mem_coe, Submodule.mem_torsionBySet_iff]
  rintro ⟨a, ha⟩
  apply hu_inj
  rw [map_zero]
  have hux : u x = Λ.mkQ (((c : 𝕜)⁻¹) • ι φ hφ ρ hker v w ((p.1 : T), (p.2 : T))) := by
    rw [hx, hy, Ψ_apply]
  rw [hu_eq a x _ hux, map_smul, ρ_ι]

  have h1 : φ a * (p.1 : T) ∈ Ideal.span {(c : T)} := p.1.2 (φ a) (hS a ha)
  have h2 : φ a * (p.2 : T) ∈ Ideal.span {(c : T)} := p.2.2 (φ a) (hS a ha)
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp h1
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.mp h2
  have h3 : φ a • ((p.1 : T), (p.2 : T)) = (c : T) • (s, t) := by
    rw [Prod.smul_mk, Prod.smul_mk, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, ← hs, ← ht,
      mul_comm s, mul_comm t]
  rw [h3, ι_natCast_smul, inv_smul_smul₀ hc', Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ι_mem φ hφ ρ hker v w Λ hΛ hv hw _

include hφ hker hd hΛ hv hw hinj hu_inj hu_fin hu_eq hgen hS hc in

theorem transfer_bound [Module.Free ℤ T] [Module.Finite ℤ T]
    (hfinite : (Submodule.torsionBySet R G S : Set G).Finite) :
    ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 ≤
      d ^ Module.finrank ℤ (T × T) * Nat.card ↥(Submodule.torsionBySet R G S) := by
  classical

  have hιinj := ι_injective φ hφ ρ hker v w hinj
  let eL : (T × T) ≃ₗ[ℤ] ↥(L' φ hφ ρ hker v w) :=
    LinearEquiv.ofInjective (ι φ hφ ρ hker v w).toIntLinearMap hιinj
  haveI : Module.Free ℤ ↥(L' φ hφ ρ hker v w) := Module.Free.of_equiv eL
  haveI : Module.Finite ℤ ↥(L' φ hφ ρ hker v w) := Module.Finite.equiv eL
  have hrank : Module.finrank ℤ ↥(L' φ hφ ρ hker v w) = Module.finrank ℤ (T × T) :=
    eL.finrank_eq.symm
  have hcardT := Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := 𝕜)
    (L' φ hφ ρ hker v w) d hd
  haveI : Finite ↥(Submodule.torsionBy ℤ (D ⧸ L' φ hφ ρ hker v w) (d : ℕ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardT]
    exact pow_ne_zero _ hd

  set Y := (Ψ φ hφ ρ hker v w Λ 𝔍 c).ker with hY
  have hPY : P₂ 𝔍 c ≤ Y := P₂_le_ker φ hφ ρ hker v w Λ hΛ hv hw 𝔍 c hc

  haveI : Finite ↥(Ψ φ hφ ρ hker v w Λ 𝔍 c).range :=
    Set.Finite.to_subtype ((hfinite.image u).subset
      (range_Ψ_subset φ hφ ρ hker v w Λ hΛ hv hw 𝔍 c u hu_inj hu_fin hu_eq S hS hc))
  have ha : Y.index ≤ Nat.card ↥(Submodule.torsionBySet R G S) := by
    rw [hY, AddSubgroup.index_ker]
    calc Nat.card ↥(Ψ φ hφ ρ hker v w Λ 𝔍 c).range
        ≤ Nat.card ↥(u '' (Submodule.torsionBySet R G S)) :=
          Nat.card_mono (hfinite.image u)
            (range_Ψ_subset φ hφ ρ hker v w Λ hΛ hv hw 𝔍 c u hu_inj hu_fin hu_eq S hS hc)
      _ = Nat.card ↥(Submodule.torsionBySet R G S : Set G) := Nat.card_image_of_injective hu_inj _
      _ = Nat.card ↥(Submodule.torsionBySet R G S) := rfl

  haveI : Finite ↥(Y.map (hmap φ hφ ρ hker v w 𝔍 c)) :=
    Finite.of_injective (fun y : ↥(Y.map (hmap φ hφ ρ hker v w 𝔍 c)) =>
      (⟨y.1, map_ker_le φ hφ ρ hker v w Λ 𝔍 c d hgen y.2⟩ :
        ↥(Submodule.torsionBy ℤ (D ⧸ L' φ hφ ρ hker v w) (d : ℕ)).toAddSubgroup))
      (fun a b h => by
        apply Subtype.ext
        have h' := congrArg Subtype.val h
        exact h')
  have hb : (P₂ 𝔍 c).relIndex Y ≤ d ^ Module.finrank ℤ (T × T) := by
    have h1 : (P₂ 𝔍 c).relIndex Y ≤ (hmap φ hφ ρ hker v w 𝔍 c).ker.relIndex Y := by
      apply Nat.le_of_dvd
      · rw [AddSubgroup.relIndex_ker]
        exact Nat.card_pos
      · exact AddSubgroup.relIndex_dvd_of_le_left Y (ker_hmap_le φ hφ ρ hker v w hinj 𝔍 c hc)
    calc (P₂ 𝔍 c).relIndex Y ≤ (hmap φ hφ ρ hker v w 𝔍 c).ker.relIndex Y := h1
      _ = Nat.card ↥(Y.map (hmap φ hφ ρ hker v w 𝔍 c)) := AddSubgroup.relIndex_ker _ _
      _ ≤ Nat.card ↥(Submodule.torsionBy ℤ (D ⧸ L' φ hφ ρ hker v w) (d : ℕ)).toAddSubgroup :=
          AddSubgroup.card_le_of_le (map_ker_le φ hφ ρ hker v w Λ 𝔍 c d hgen)
      _ = d ^ Module.finrank ℤ ↥(L' φ hφ ρ hker v w) := hcardT
      _ = d ^ Module.finrank ℤ (T × T) := by rw [hrank]

  calc ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 = (P₂ 𝔍 c).index := (index_P₂ 𝔍 c).symm
    _ = (P₂ 𝔍 c).relIndex Y * Y.index := (AddSubgroup.relIndex_mul_index hPY).symm
    _ ≤ d ^ Module.finrank ℤ (T × T) * Nat.card ↥(Submodule.torsionBySet R G S) :=
        Nat.mul_le_mul hb ha

end Transfer

section Concrete

open ModularCurve CuspForm AlgebraicCurve

variable (N : ℕ) [NeZero N]

abbrev TL : Type := ↥(heckeLatticeAlgebra N ∅)

abbrev Dd : Type := Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)

abbrev φL : HeckeAlg →+* TL N := (latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)

theorem φL_apply (a : HeckeAlg) : φL N a = latticeRestrictHom N ∅ (heckeEvalForms N 2 a) := rfl

theorem cuspHeckeAeval_eq (a : HeckeAlg) :
    (cuspHeckeAeval N a : heckeAlgebra N 2 ∅) = heckeEvalForms N 2 a := rfl

theorem φL_surjective : Function.Surjective (φL N) := by
  intro t
  obtain ⟨s, rfl⟩ := latticeRestrictHom_surjective N ∅ t
  have hs : s ∈ (cuspHeckeAeval N).range := by rw [cuspHeckeAeval_range]; trivial
  obtain ⟨a, ha⟩ := hs
  change cuspHeckeAeval N a = s at ha
  refine ⟨a, ?_⟩
  rw [φL_apply]
  change latticeRestrictHom N ∅ (cuspHeckeAeval N a) = _
  rw [ha]

theorem dualHeckeRep_eq_zero_of_φL (a : HeckeAlg) (h : φL N a = 0) : dualHeckeRep N a = 0 := by
  have h1 : heckeEvalForms N 2 a = 0 := by
    apply (latticeRestrictHom_bijective N ∅ (CuspForm.hasIntegralStructure_two N)).1
    rw [map_zero]
    exact h
  have h2 : cuspHeckeRep N a = 0 := by
    rw [cuspHeckeRep_apply, cuspHeckeAeval_eq, h1]
    rfl
  apply LinearMap.ext fun ψ => ?_
  apply LinearMap.ext fun f => ?_
  rw [dualHeckeRep_apply_apply, h2]
  simp

theorem φL_eq_zero_of_periodLatticeHeckeEnd (a : HeckeAlg) (h : periodLatticeHeckeEnd N a = 0) :
    φL N a = 0 := by
  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  obtain ⟨n, b, hli, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  have h1 : dualHeckeRep N a = 0 := by
    have h0 : (dualHeckeRep N a).restrictScalars ℝ = (0 : Dd N →ₗ[ℂ] Dd N).restrictScalars ℝ := by
      refine LinearMap.ext_on_range hsp fun i => ?_
      rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.zero_apply,
        ← coe_periodLatticeHeckeEnd_apply hst, h, LinearMap.zero_apply, Submodule.coe_zero]
    exact LinearMap.restrictScalars_injective ℝ h0
  have h2 : cuspHeckeRep N a = 0 := by
    apply LinearMap.ext fun f => ?_
    rw [LinearMap.zero_apply]
    refine (Module.forall_dual_apply_eq_zero_iff ℂ _).mp fun ψ => ?_
    have := congrArg (fun S : Module.End ℂ (Dd N) => S ψ f) h1
    simpa [dualHeckeRep_apply_apply] using this
  have h3 : heckeEvalForms N 2 a = 0 := by
    apply Subtype.ext
    rw [← cuspHeckeAeval_eq, ← cuspHeckeRep_apply, h2]
    rfl
  rw [φL_apply, h3, map_zero]

theorem u_equivariant (u : JZero N →+ Dd N ⧸ periodLattice N)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : Dd N), u x = Submodule.Quotient.mk φ →
      u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (a : HeckeAlg) (x : JZero N) (ψ : Dd N) (hx : u x = (periodLattice N).mkQ ψ) :
    u (letI := heckeModuleBar N; a • x) = (periodLattice N).mkQ (dualHeckeRep N a ψ) := by
  letI : Module HeckeAlg (JZero N) := heckeModuleBar N
  have h599 : HeckeOperatorsCommuteBar N := ModularCurve.heckeOperatorsCommuteBar N
  induction a using MvPolynomial.induction_on generalizing x ψ with
  | C k =>
    rw [heckeModuleBar_C_smul, map_zsmul, hx, dualHeckeRep_C, ← map_zsmul]
  | add p q hp hq =>
    rw [add_smul, map_add, hp x ψ hx, hq x ψ hx, map_add, LinearMap.add_apply, map_add]
  | mul_X p ℓ hp =>
    have hgen : (MvPolynomial.X ℓ : HeckeAlg) • x = heckeOperatorBar N ℓ x :=
      heckeModuleBar_heckeGen_smul h599 ℓ x
    have hx' : u (heckeOperatorBar N ℓ x) = (periodLattice N).mkQ (dualHeckeRep N (heckeGen ℓ) ψ) := by
      rw [Submodule.mkQ_apply] at hx ⊢
      exact hu ℓ x ψ hx
    rw [mul_smul, hgen, hp (heckeOperatorBar N ℓ x) _ hx', map_mul, Module.End.mul_apply]
    rfl

theorem torsion_finite (q m : ℕ) (hq : q ≠ 0) (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    (letI := heckeModuleBar N;
      (Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg) : Set (JZero N))).Finite := by
  letI : Module HeckeAlg (JZero N) := heckeModuleBar N
  have hcard := ModularCurve.natCard_torsion_jZero_eq_pow_finrank_periodLattice N (q ^ m)
    (pow_ne_zero m hq)
  haveI : Finite ↥(Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (q ^ m)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcard]
    exact pow_ne_zero _ (pow_ne_zero m hq)
  have hfin : (Pic0.torsion (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (q ^ m) :
      Set (JZero N)).Finite := Set.toFinite _
  refine hfin.subset fun x hx => ?_
  have h1 : ((q ^ m : ℕ) : HeckeAlg) ∈ I ^ m := by
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow hqI m
  have h2 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨_, h1⟩
  change ((q ^ m : ℕ) : HeckeAlg) • x = 0 at h2
  rw [Nat.cast_smul_eq_nsmul, ← natCast_zsmul] at h2
  exact (Pic0.mem_torsion (K := AlgebraicClosure ℚ) (F := modularFunctionFieldBar N)).mpr h2

theorem le_pow_self {q : ℕ} (hq : 1 < q) (n : ℕ) : n ≤ q ^ n := (Nat.lt_pow_self hq).le

theorem final_arith {L cD r d f Jm q K : ℕ} (h1 : L ≤ cD * r) (h2 : r ^ 2 ≤ d ^ f * Jm)
    (h3 : cD ^ 2 * d ^ f ≤ q ^ K) : L ^ 2 ≤ Jm * q ^ K := by
  calc L ^ 2 ≤ (cD * r) ^ 2 := Nat.pow_le_pow_left h1 2
    _ = cD ^ 2 * r ^ 2 := by ring
    _ ≤ cD ^ 2 * (d ^ f * Jm) := Nat.mul_le_mul_left _ h2
    _ = Jm * (cD ^ 2 * d ^ f) := by ring
    _ ≤ Jm * q ^ K := Nat.mul_le_mul_left _ h3

set_option synthInstance.maxHeartbeats 1600000 in

theorem main_step (q : ℕ) (hq1 : 1 < q) (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I)
    (u : JZero N →+ Dd N ⧸ periodLattice N) (hu_inj : Function.Injective u)
    (hu_fin : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (hu_eq : ∀ (a : HeckeAlg) (x : JZero N) (ψ : Dd N), u x = (periodLattice N).mkQ ψ →
      u (letI := heckeModuleBar N; a • x) = (periodLattice N).mkQ (dualHeckeRep N a ψ))
    (v w : Dd N) (hv : v ∈ periodLattice N) (hw : w ∈ periodLattice N) (d : ℕ) (hd : d ≠ 0)
    (hgen : ∀ x ∈ periodLattice N, ∃ a b : HeckeAlg, (d : ℂ) • x = dualHeckeRep N a v + dualHeckeRep N b w)
    (hinj : ∀ a b : HeckeAlg, dualHeckeRep N a v + dualHeckeRep N b w = 0 → φL N a = 0 ∧ φL N b = 0)
    (cD : ℕ) (hD : ∀ (n : ℕ), n ≠ 0 → ∀ J : Ideal (TL N), (n : TL N) ∈ J →
      Nat.card (TL N ⧸ J) ≤
        cD * Nat.card ↥(Submodule.torsionBySet (TL N) (TL N ⧸ Ideal.span {(n : TL N)}) (J : Set (TL N))))
    (m : ℕ) :
    Nat.card (TL N ⧸ (Ideal.map (φL N) I) ^ m) ^ 2 ≤
      Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) *
        q ^ (cD ^ 2 * d ^ Module.finrank ℤ (TL N × TL N)) := by
  letI instMod : Module HeckeAlg (JZero N) := heckeModuleBar N
  have hq0 : q ≠ 0 := by omega
  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  have hker : ∀ a, φL N a = 0 → dualHeckeRep N a = 0 := dualHeckeRep_eq_zero_of_φL N
  have hΛ : ∀ (a : HeckeAlg) (x : Dd N), x ∈ periodLattice N → dualHeckeRep N a x ∈ periodLattice N :=
    fun a x hx => periodLattice_stable_of hst a x hx
  have hS : ∀ a ∈ (↑(I ^ m) : Set HeckeAlg), φL N a ∈ (Ideal.map (φL N) I) ^ m := fun a ha => by
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ ha
  have hc : q ^ m ≠ 0 := pow_ne_zero m hq0
  have hc𝔍 : ((q ^ m : ℕ) : TL N) ∈ (Ideal.map (φL N) I) ^ m := by
    rw [Nat.cast_pow]
    refine Ideal.pow_mem_pow ?_ m
    rw [← map_natCast (φL N)]
    exact Ideal.mem_map_of_mem _ hqI
  have hfinite := torsion_finite N q m hq0 I hqI

  have hT := transfer_bound (R := HeckeAlg) (T := TL N) (𝕜 := ℂ) (D := Dd N) (G := JZero N)
    (φL N) (φL_surjective N) (dualHeckeRep N) hker v w
    (periodLattice N) hΛ hv hw hinj ((Ideal.map (φL N) I) ^ m) (q ^ m) u hu_inj hu_fin hu_eq d hd
    hgen (↑(I ^ m) : Set HeckeAlg) hS hc hfinite

  have hDm := hD (q ^ m) hc ((Ideal.map (φL N) I) ^ m) hc𝔍
  rw [natCard_torsionBySet_eq_relIndex] at hDm

  have hKq : cD ^ 2 * d ^ Module.finrank ℤ (TL N × TL N) ≤
      q ^ (cD ^ 2 * d ^ Module.finrank ℤ (TL N × TL N)) := le_pow_self hq1 _
  exact final_arith hDm hT hKq

theorem main (hred : IsReduced ↥(heckeLatticeAlgebra N ∅))
    (q : ℕ) [Fact q.Prime] (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card (↥(heckeLatticeAlgebra N ∅) ⧸
          (Ideal.map ((latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)) I) ^ m) ^ 2 ≤
        Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) * q ^ C := by
  classical
  haveI : IsReduced (TL N) := hred
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N

  obtain ⟨cD, -, hD⟩ :=
    Ideal.exists_forall_natCard_quotient_le_mul_natCard_torsionBySet_of_isReduced (TL N)
  obtain ⟨v₀, w₀, d, hd, hgen₀, hinj₀⟩ := ModularCurve.exists_nsmul_eq_smul_add_smul_periodLattice N
  obtain ⟨u, hu_inj, hu_fin, hu_eq₀⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice N
      (ModularCurve.heckeInputsAll N) hst

  have hgen : ∀ x ∈ periodLattice N, ∃ a b : HeckeAlg,
      (d : ℂ) • x = dualHeckeRep N a (v₀ : Dd N) + dualHeckeRep N b (w₀ : Dd N) := by
    intro x hx
    obtain ⟨s, t, h⟩ := hgen₀ ⟨x, hx⟩
    refine ⟨s, t, ?_⟩
    have := congrArg Subtype.val h
    rw [Submodule.coe_add, coe_periodLatticeHeckeEnd_apply hst, coe_periodLatticeHeckeEnd_apply hst,
      Submodule.coe_smul_of_tower] at this
    rw [Nat.cast_smul_eq_nsmul]
    exact this
  have hinj : ∀ a b : HeckeAlg,
      dualHeckeRep N a (v₀ : Dd N) + dualHeckeRep N b (w₀ : Dd N) = 0 → φL N a = 0 ∧ φL N b = 0 := by
    intro a b h
    have h' : periodLatticeHeckeEnd N a v₀ + periodLatticeHeckeEnd N b w₀ = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_add, coe_periodLatticeHeckeEnd_apply hst, coe_periodLatticeHeckeEnd_apply hst,
        Submodule.coe_zero]
      exact h
    obtain ⟨ha, hb⟩ := hinj₀ a b h'
    exact ⟨φL_eq_zero_of_periodLatticeHeckeEnd N a ha, φL_eq_zero_of_periodLatticeHeckeEnd N b hb⟩
  have hu_eq : ∀ (a : HeckeAlg) (x : JZero N) (ψ : Dd N), u x = (periodLattice N).mkQ ψ →
      u (letI := heckeModuleBar N; a • x) = (periodLattice N).mkQ (dualHeckeRep N a ψ) :=
    fun a x ψ hx => u_equivariant N u hu_eq₀ a x ψ hx
  exact ⟨cD ^ 2 * d ^ Module.finrank ℤ (TL N × TL N), fun m =>
    main_step N q hq1 I hqI u hu_inj hu_fin hu_eq v₀ w₀ v₀.2 w₀.2 d hd hgen hinj cD hD m⟩

end Concrete

end P2MR2LB

end

open ModularCurve CuspForm

theorem solution
    (N : ℕ) [NeZero N] (hred : IsReduced ↥(heckeLatticeAlgebra N ∅))
    (q : ℕ) [Fact q.Prime] (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card (↥(heckeLatticeAlgebra N ∅) ⧸
          (Ideal.map ((latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)) I) ^ m) ^ 2 ≤
        Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) * q ^ C :=
  P2MR2LB.main N hred q I hqI

end S_ModularCurve_exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow
end P2MW
export P2MW.S_ModularCurve_exists_sq_natCard_heckeLatticeAlgebra_quotient_le_natCard_torsionBySet_mul_pow (solution)
