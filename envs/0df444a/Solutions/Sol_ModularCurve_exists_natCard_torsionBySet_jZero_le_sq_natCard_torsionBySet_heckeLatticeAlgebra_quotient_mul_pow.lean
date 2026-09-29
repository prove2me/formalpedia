-- Prove2me | solution 1 for ModularCurve.exists_natCard_torsionBySet_jZero_le_sq_natCard_torsionBySet_heckeLatticeAlgebra_quotient_mul_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/89d0d873-fc0c-5f4f-bd3a-ffe32ff32ec0

import Mathlib
import Definitions.Def_CuspForm_HeckeLocal
import Definitions.Def_CuspForm_HeckeEvalForms
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_PeriodLattice
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_ModularCurve_exists_nsmul_eq_smul_add_smul_periodLattice
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

namespace P2MW.S_ModularCurve_exists_natCard_torsionBySet_jZero_le_sq_natCard_torsionBySet_heckeLatticeAlgebra_quotient_mul_pow
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

set_option autoImplicit false

noncomputable section

namespace P2MR2UB

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

private def _root_.P2MR2UB.X : AddSubgroup T where
  carrier := {x | ∀ j ∈ 𝔍, j * x ∈ Ideal.span {(c : T)}}
  zero_mem' := fun j _ => by simp
  add_mem' := fun {x y} hx hy j hj => by
    simp only [mul_add]
    exact Ideal.add_mem _ (hx j hj) (hy j hj)
  neg_mem' := fun {x} hx j hj => by
    simp only [mul_neg]
    exact Submodule.neg_mem _ (hx j hj)

p2m_export "P2MR2UB" "X"
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

theorem finite_quotient_of_natCast_mem {S' : Type*} [CommRing S'] [inst : Module ℤ S']
    [hS' : Module.Finite ℤ S'] (I' : Ideal S') (n : ℕ) (hn : n ≠ 0) (hI : (n : S') ∈ I') :
    Finite (S' ⧸ I') := by
  obtain rfl : inst = AddCommGroup.toIntModule S' := Subsingleton.elim _ _
  haveI : Module.Finite ℤ (S' ⧸ I') := Module.Finite.quotient ℤ I'
  refine Module.finite_of_fg_torsion (S' ⧸ I') fun x => ?_
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hn' : (n : ℤ) ∈ nonZeroDivisors ℤ :=
    mem_nonZeroDivisors_of_ne_zero (Int.natCast_ne_zero.mpr hn)
  refine ⟨⟨n, hn'⟩, ?_⟩
  have h1 : ((⟨n, hn'⟩ : nonZeroDivisors ℤ) • Ideal.Quotient.mk I' s) =
      Ideal.Quotient.mk I' ((n : ℤ) • s) := rfl
  rw [h1, zsmul_eq_mul, Int.cast_natCast, Ideal.Quotient.eq_zero_iff_mem]
  exact I'.mul_mem_right s hI

omit hφ in

theorem relIndex_ne_zero [Module.Finite ℤ T] (hc : c ≠ 0) :
    (𝔮 (T := T) c).relIndex (X 𝔍 c) ≠ 0 := by
  haveI : Finite (T ⧸ Ideal.span {(c : T)}) :=
    finite_quotient_of_natCast_mem (Ideal.span {(c : T)}) c hc (Ideal.subset_span rfl)
  have hidx : (𝔮 (T := T) c).index ≠ 0 := by
    have : (𝔮 (T := T) c).index = Nat.card (T ⧸ Ideal.span {(c : T)}) := rfl
    rw [this]
    exact Nat.card_pos.ne'
  have hmul := AddSubgroup.relIndex_mul_index (𝔮_le_X 𝔍 c)
  rw [← hmul] at hidx
  exact left_ne_zero_of_mul hidx

variable [CharZero 𝕜]
variable {G : Type*} [AddCommGroup G] [Module R G] (u : G →+ D ⧸ Λ)
  (hu_inj : Function.Injective u)
  (hu_eq : ∀ (a : R) (x : G) (ψ : D), u x = Λ.mkQ ψ → u (a • x) = Λ.mkQ (ρ a ψ))
variable (d : ℕ) (hd : d ≠ 0) (hgen : ∀ x ∈ Λ, ∃ a b : R, (d : 𝕜) • x = ρ a v + ρ b w)
variable (S : Set R) (hS : ∀ j ∈ 𝔍, ∃ a ∈ S, φ a = j) (hcS : ((c : ℕ) : R) ∈ S) (hc : c ≠ 0)

abbrev L' : Submodule ℤ D := LinearMap.range (ι φ hφ ρ hker v w).toIntLinearMap

def ΛS : AddSubgroup D :=
  (((Submodule.torsionBySet R G S).toAddSubgroup).map u).comap Λ.mkQ.toAddMonoidHom

omit [CharZero 𝕜] in
theorem mem_ΛS {z : D} :
    z ∈ ΛS Λ u S ↔ ∃ x ∈ Submodule.torsionBySet R G S, u x = Λ.mkQ z := by
  unfold ΛS
  rw [AddSubgroup.mem_comap, AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, hxz⟩
  · rintro ⟨x, hx, hxz⟩
    exact ⟨x, hx, hxz⟩

omit [CharZero 𝕜] in
theorem Λ_le_ΛS : Λ.toAddSubgroup ≤ ΛS Λ u S := by
  intro z hz
  rw [mem_ΛS]
  refine ⟨0, Submodule.zero_mem _, ?_⟩
  rw [map_zero, Submodule.mkQ_apply, eq_comm, Submodule.Quotient.mk_eq_zero]
  exact hz

omit [CharZero 𝕜] in
include hu_inj in

theorem relIndex_Λ_ΛS :
    Λ.toAddSubgroup.relIndex (ΛS Λ u S) = Nat.card ↥(Submodule.torsionBySet R G S) := by
  have hk : (Λ.mkQ.toAddMonoidHom).ker = Λ.toAddSubgroup := by
    ext z
    rw [AddMonoidHom.mem_ker]
    change Λ.mkQ z = 0 ↔ z ∈ Λ
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  have hsurj : Function.Surjective (Λ.mkQ.toAddMonoidHom) := fun y => Submodule.mkQ_surjective Λ y
  unfold ΛS
  rw [← hk, AddSubgroup.relIndex_ker, AddSubgroup.map_comap_eq_self_of_surjective hsurj]
  have e1 : Nat.card ↥(((Submodule.torsionBySet R G S).toAddSubgroup).map u) =
      Nat.card ↥(u '' (Submodule.torsionBySet R G S : Set G)) := rfl
  rw [e1, Nat.card_image_of_injective hu_inj]
  rfl

include hu_eq hcS in
omit [CharZero 𝕜] in

theorem c_smul_mem {z : D} (hz : z ∈ ΛS Λ u S) : (c : 𝕜) • z ∈ Λ := by
  obtain ⟨x, hx, hxz⟩ := (mem_ΛS Λ u S).mp hz
  have h0 : ((c : ℕ) : R) • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨_, hcS⟩
  have h1 := hu_eq ((c : ℕ) : R) x z hxz
  rw [h0, map_zero, map_natCast, Module.End.natCast_apply] at h1
  have h2 : Λ.mkQ ((c : 𝕜) • z) = 0 := by
    first
      | (rw [Nat.cast_smul_eq_nsmul]; exact h1.symm)
      | exact h1.symm
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h2
  exact h2

include hu_eq in
omit [CharZero 𝕜] in

theorem ρ_mem_of_mem_S {z : D} (hz : z ∈ ΛS Λ u S) {a : R} (ha : a ∈ S) : ρ a z ∈ Λ := by
  obtain ⟨x, hx, hxz⟩ := (mem_ΛS Λ u S).mp hz
  have h0 : a • x = 0 := (Submodule.mem_torsionBySet_iff _ _).mp hx ⟨a, ha⟩
  have h1 := hu_eq a x z hxz
  rw [h0, map_zero] at h1
  rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
  exact h1.symm

include hgen hu_eq hcS in
omit [CharZero 𝕜] in

theorem dc_smul_mem_L' {z : D} (hz : z ∈ ΛS Λ u S) :
    ((d : 𝕜) * (c : 𝕜)) • z ∈ L' φ hφ ρ hker v w := by
  have h1 := c_smul_mem ρ Λ c u hu_eq S hcS hz
  obtain ⟨a, b, hab⟩ := hgen _ h1
  rw [mul_smul, hab, ← ι_φ φ hφ ρ hker]
  exact ⟨(φ a, φ b), rfl⟩

def eL (hinj' : Function.Injective (ι φ hφ ρ hker v w)) : (T × T) ≃ₗ[ℤ] ↥(L' φ hφ ρ hker v w) :=
  LinearEquiv.ofInjective (ι φ hφ ρ hker v w).toIntLinearMap hinj'

omit [CharZero 𝕜] in
theorem ι_eL_symm (hinj' : Function.Injective (ι φ hφ ρ hker v w)) (y : ↥(L' φ hφ ρ hker v w)) :
    ι φ hφ ρ hker v w ((eL φ hφ ρ hker v w hinj').symm y) = (y : D) :=
  LinearEquiv.ofInjective_symm_apply (f := (ι φ hφ ρ hker v w).toIntLinearMap) (h := hinj') y

def dcMap : ↥(ΛS Λ u S) →+ ↥(L' φ hφ ρ hker v w) where
  toFun z := ⟨((d : 𝕜) * (c : 𝕜)) • (z : D), dc_smul_mem_L' φ hφ ρ hker v w Λ c u hu_eq d hgen S hcS z.2⟩
  map_zero' := by
    apply Subtype.ext
    change ((d : 𝕜) * (c : 𝕜)) • (0 : D) = 0
    rw [smul_zero]
  map_add' z z' := by
    apply Subtype.ext
    change ((d : 𝕜) * (c : 𝕜)) • ((z : D) + (z' : D)) =
      ((d : 𝕜) * (c : 𝕜)) • (z : D) + ((d : 𝕜) * (c : 𝕜)) • (z' : D)
    rw [smul_add]

def θ : ↥(ΛS Λ u S) →+ T × T :=
  ((eL φ hφ ρ hker v w (ι_injective φ hφ ρ hker v w hinj)).symm.toAddMonoidHom).comp
    (dcMap φ hφ ρ hker v w Λ c u hu_eq d hgen S hcS)

omit [CharZero 𝕜] in
theorem ι_θ (z : ↥(ΛS Λ u S)) :
    ι φ hφ ρ hker v w (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z) =
      ((d : 𝕜) * (c : 𝕜)) • (z : D) := by
  unfold θ
  rw [AddMonoidHom.comp_apply]
  exact ι_eL_symm φ hφ ρ hker v w _ _

include hS in
omit [CharZero 𝕜] in

theorem exists_smul_θ_eq (z : ↥(ΛS Λ u S)) {j : T} (hj : j ∈ 𝔍) :
    ∃ p' : T × T, j • θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z = (c : T) • p' := by
  obtain ⟨a, ha, rfl⟩ := hS j hj
  have hρ : ρ a (z : D) ∈ Λ := ρ_mem_of_mem_S ρ Λ u hu_eq S z.2 ha
  obtain ⟨a', b', hab⟩ := hgen _ hρ
  refine ⟨(φ a', φ b'), ι_injective φ hφ ρ hker v w hinj ?_⟩
  rw [← ρ_ι, ι_θ, map_smul, mul_comm, mul_smul, hab, ← ι_φ φ hφ ρ hker, ← ι_natCast_smul]

include hS in
omit [CharZero 𝕜] in
theorem θ_fst_mem_X (z : ↥(ΛS Λ u S)) :
    (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z).1 ∈ X 𝔍 c := by
  rw [mem_X]
  intro j hj
  obtain ⟨p', hp'⟩ := exists_smul_θ_eq φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z hj
  have h1 := congrArg Prod.fst hp'
  rw [Prod.smul_fst, Prod.smul_fst, smul_eq_mul, smul_eq_mul] at h1
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

include hS in
omit [CharZero 𝕜] in
theorem θ_snd_mem_X (z : ↥(ΛS Λ u S)) :
    (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z).2 ∈ X 𝔍 c := by
  rw [mem_X]
  intro j hj
  obtain ⟨p', hp'⟩ := exists_smul_θ_eq φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z hj
  have h1 := congrArg Prod.snd hp'
  rw [Prod.smul_snd, Prod.smul_snd, smul_eq_mul, smul_eq_mul] at h1
  rw [h1]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)

def θX : ↥(ΛS Λ u S) →+ ↥(X 𝔍 c) × ↥(X 𝔍 c) :=
  (((AddMonoidHom.fst T T).comp (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS)).codRestrict
      (X 𝔍 c) (fun z => θ_fst_mem_X φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z)).prod
    (((AddMonoidHom.snd T T).comp (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS)).codRestrict
      (X 𝔍 c) (fun z => θ_snd_mem_X φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z))

omit [CharZero 𝕜] in
theorem θX_fst (z : ↥(ΛS Λ u S)) :
    ((θX φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z).1 : T) =
      (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z).1 := rfl

omit [CharZero 𝕜] in
theorem θX_snd (z : ↥(ΛS Λ u S)) :
    ((θX φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS z).2 : T) =
      (θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z).2 := rfl

def θbar : ↥(ΛS Λ u S) →+ (↥(X 𝔍 c) × ↥(X 𝔍 c)) ⧸ P₂ 𝔍 c :=
  (QuotientAddGroup.mk' (P₂ 𝔍 c)).comp (θX φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS)

include hΛ hv hw hc in

theorem mkQ_mem_torsionBy_of_mem_ker (z : ↥(ΛS Λ u S))
    (hz : z ∈ (θbar φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS).ker) :
    Λ.mkQ (z : D) ∈ Submodule.torsionBy ℤ (D ⧸ Λ) (d : ℕ) := by
  rw [AddMonoidHom.mem_ker] at hz
  unfold θbar at hz
  rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_P₂,
    θX_fst, θX_snd, mem_𝔮, mem_𝔮] at hz
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hz
  set p := θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z with hp
  have hpc : p = (c : T) • (a, b) := by
    ext
    · rw [Prod.smul_fst, smul_eq_mul, mul_comm]; exact ha.symm
    · rw [Prod.smul_snd, smul_eq_mul, mul_comm]; exact hb.symm
  have hιp : ι φ hφ ρ hker v w p = ((d : 𝕜) * (c : 𝕜)) • (z : D) :=
    ι_θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z
  rw [hpc, ι_natCast_smul, mul_comm, mul_smul] at hιp
  have hc' : (c : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hc
  have hdz : (d : 𝕜) • (z : D) = ι φ hφ ρ hker v w (a, b) := smul_right_injective D hc' hιp.symm
  have hmem : (d : 𝕜) • (z : D) ∈ Λ := by
    rw [hdz]
    exact ι_mem φ hφ ρ hker v w Λ hΛ hv hw _
  rw [Submodule.mem_torsionBy_iff, Submodule.mkQ_apply]
  change Submodule.Quotient.mk (p := Λ) (((d : ℕ) : ℤ) • (z : D)) = 0
  rw [Submodule.Quotient.mk_eq_zero, natCast_zsmul, ← Nat.cast_smul_eq_nsmul 𝕜]
  exact hmem

include hφ hker hd hΛ hv hw hinj hu_inj hu_eq hgen hS hcS hc in

theorem reverse_transfer_bound [Module.Finite ℤ T] [Module.Free ℤ ↥Λ] [Module.Finite ℤ ↥Λ] :
    Nat.card ↥(Submodule.torsionBySet R G S) ≤
      ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 * d ^ Module.finrank ℤ ↥Λ := by
  classical
  have hcardT := Submodule.natCard_torsionBy_quotient_eq_pow_finrank (K := 𝕜) Λ d hd
  haveI hfinT : Finite ↥(Submodule.torsionBy ℤ (D ⧸ Λ) (d : ℕ)) := by
    apply Nat.finite_of_card_ne_zero
    rw [hcardT]
    exact pow_ne_zero _ hd

  set A := ΛS Λ u S with hA
  set K := (θbar φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS).ker with hK
  have hΛA : Λ.toAddSubgroup ≤ A := Λ_le_ΛS Λ u S

  have hΛK : (Λ.toAddSubgroup).addSubgroupOf A ≤ K := by
    intro z hz
    rw [AddSubgroup.mem_addSubgroupOf] at hz
    rw [hK, AddMonoidHom.mem_ker]
    unfold θbar
    rw [AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, mem_P₂,
      θX_fst, θX_snd]
    obtain ⟨a, b, hab⟩ := hgen _ hz
    set p := θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z with hp
    have hιp : ι φ hφ ρ hker v w p = ((d : 𝕜) * (c : 𝕜)) • ((z : D)) :=
      ι_θ φ hφ ρ hker v w Λ hinj c u hu_eq d hgen S hcS z
    have h2 : ι φ hφ ρ hker v w p = ι φ hφ ρ hker v w ((c : T) • (φ a, φ b)) := by
      rw [hιp, ι_natCast_smul, ι_φ, ← hab, ← mul_smul, mul_comm]
    have h3 := ι_injective φ hφ ρ hker v w hinj h2
    rw [h3, mem_𝔮, mem_𝔮]
    exact ⟨⟨φ a, by rw [Prod.smul_fst, smul_eq_mul, mul_comm]⟩,
      ⟨φ b, by rw [Prod.smul_snd, smul_eq_mul, mul_comm]⟩⟩

  have hP₂ : (P₂ 𝔍 c).index ≠ 0 := by
    rw [index_P₂]
    exact pow_ne_zero _ (relIndex_ne_zero 𝔍 c hc)
  haveI : Finite ((↥(X 𝔍 c) × ↥(X 𝔍 c)) ⧸ P₂ 𝔍 c) := Nat.finite_of_card_ne_zero hP₂
  have ha : K.index ≤ ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 := by
    rw [hK, AddSubgroup.index_ker, ← index_P₂ 𝔍 c]
    calc Nat.card ↥(θbar φ hφ ρ hker v w Λ hinj 𝔍 c u hu_eq d hgen S hS hcS).range
        ≤ Nat.card ((↥(X 𝔍 c) × ↥(X 𝔍 c)) ⧸ P₂ 𝔍 c) :=
          Nat.card_le_card_of_injective _ Subtype.val_injective
      _ = (P₂ 𝔍 c).index := rfl

  let f : ↥K →+ D ⧸ Λ := (Λ.mkQ.toAddMonoidHom).comp ((A.subtype).comp K.subtype)
  have hfker : f.ker = ((Λ.toAddSubgroup).addSubgroupOf A).addSubgroupOf K := by
    ext z
    rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_addSubgroupOf]
    change Λ.mkQ ((z : ↥A) : D) = 0 ↔ ((z : ↥A) : D) ∈ Λ.toAddSubgroup
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    rfl
  have hfrange : f.range ≤ (Submodule.torsionBy ℤ (D ⧸ Λ) (d : ℕ)).toAddSubgroup := by
    rintro _ ⟨z, rfl⟩
    exact mkQ_mem_torsionBy_of_mem_ker φ hφ ρ hker v w Λ hΛ hv hw hinj 𝔍 c u hu_eq d hgen S hS hcS
      hc (z : ↥A) z.2
  have hb : ((Λ.toAddSubgroup).addSubgroupOf A).relIndex K ≤ d ^ Module.finrank ℤ ↥Λ := by
    rw [AddSubgroup.relIndex, ← hfker, AddSubgroup.index_ker]
    calc Nat.card ↥f.range ≤ Nat.card ↥(Submodule.torsionBy ℤ (D ⧸ Λ) (d : ℕ)).toAddSubgroup :=
          AddSubgroup.card_le_of_le hfrange
      _ = d ^ Module.finrank ℤ ↥Λ := hcardT

  have hidx : Λ.toAddSubgroup.relIndex A =
      ((Λ.toAddSubgroup).addSubgroupOf A).relIndex K * K.index := by
    rw [AddSubgroup.relIndex]
    exact (AddSubgroup.relIndex_mul_index hΛK).symm
  rw [← relIndex_Λ_ΛS Λ u hu_inj S, ← hA, hidx]
  calc ((Λ.toAddSubgroup).addSubgroupOf A).relIndex K * K.index
      ≤ d ^ Module.finrank ℤ ↥Λ * ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 := Nat.mul_le_mul hb ha
    _ = ((𝔮 (T := T) c).relIndex (X 𝔍 c)) ^ 2 * d ^ Module.finrank ℤ ↥Λ := Nat.mul_comm _ _

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

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem main_step (q : ℕ) (hq1 : 1 < q) (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I)
    (u : JZero N →+ Dd N ⧸ periodLattice N) (hu_inj : Function.Injective u)
    (hu_eq : ∀ (a : HeckeAlg) (x : JZero N) (ψ : Dd N), u x = (periodLattice N).mkQ ψ →
      u (letI := heckeModuleBar N; a • x) = (periodLattice N).mkQ (dualHeckeRep N a ψ))
    (v w : Dd N) (hv : v ∈ periodLattice N) (hw : w ∈ periodLattice N) (d : ℕ) (hd : d ≠ 0)
    (hgen : ∀ x ∈ periodLattice N, ∃ a b : HeckeAlg, (d : ℂ) • x = dualHeckeRep N a v + dualHeckeRep N b w)
    (hinj : ∀ a b : HeckeAlg, dualHeckeRep N a v + dualHeckeRep N b w = 0 → φL N a = 0 ∧ φL N b = 0)
    [Module.Free ℤ ↥(periodLattice N)] [Module.Finite ℤ ↥(periodLattice N)]
    (m : ℕ) :
    Nat.card ↥(letI := heckeModuleBar N;
        Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) ≤
      Nat.card ↥(Submodule.torsionBySet (TL N) (TL N ⧸ Ideal.span {(q : TL N) ^ m})
          (↑((Ideal.map (φL N) I) ^ m) : Set (TL N))) ^ 2 *
        q ^ (d ^ Module.finrank ℤ ↥(periodLattice N)) := by
  letI instMod : Module HeckeAlg (JZero N) := heckeModuleBar N
  have hq0 : q ≠ 0 := by omega
  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  have hker : ∀ a, φL N a = 0 → dualHeckeRep N a = 0 := dualHeckeRep_eq_zero_of_φL N
  have hΛ : ∀ (a : HeckeAlg) (x : Dd N), x ∈ periodLattice N → dualHeckeRep N a x ∈ periodLattice N :=
    fun a x hx => periodLattice_stable_of hst a x hx
  have hS : ∀ j ∈ (Ideal.map (φL N) I) ^ m, ∃ a ∈ (↑(I ^ m) : Set HeckeAlg), φL N a = j := by
    intro j hj
    rw [← Ideal.map_pow, Ideal.mem_map_iff_of_surjective (φL N) (φL_surjective N)] at hj
    obtain ⟨a, ha, rfl⟩ := hj
    exact ⟨a, ha, rfl⟩
  have hc : q ^ m ≠ 0 := pow_ne_zero m hq0
  have hcS : (((q ^ m : ℕ) : ℕ) : HeckeAlg) ∈ (↑(I ^ m) : Set HeckeAlg) := by
    show ((q ^ m : ℕ) : HeckeAlg) ∈ I ^ m
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_pow hqI m
  have hT := reverse_transfer_bound (R := HeckeAlg) (T := TL N) (𝕜 := ℂ) (D := Dd N) (G := JZero N)
    (φL N) (φL_surjective N) (dualHeckeRep N) hker v w (periodLattice N) hΛ hv hw hinj
    ((Ideal.map (φL N) I) ^ m) (q ^ m) u hu_inj hu_eq d hd hgen (↑(I ^ m) : Set HeckeAlg) hS hcS hc
  rw [← natCard_torsionBySet_eq_relIndex] at hT
  have key : ((q ^ m : ℕ) : TL N) = (q : TL N) ^ m := Nat.cast_pow q m
  rw [key] at hT
  exact hT.trans (Nat.mul_le_mul_left _ (le_pow_self hq1 _))

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in

theorem main (q : ℕ) [Fact q.Prime] (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) ≤
        Nat.card ↥(Submodule.torsionBySet ↥(heckeLatticeAlgebra N ∅)
            (↥(heckeLatticeAlgebra N ∅) ⧸ Ideal.span {(q : ↥(heckeLatticeAlgebra N ∅)) ^ m})
            (↑((Ideal.map ((latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)) I) ^ m) :
              Set ↥(heckeLatticeAlgebra N ∅))) ^ 2 * q ^ C := by
  classical
  have hq1 : 1 < q := (Fact.out : q.Prime).one_lt
  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N

  obtain ⟨n, b, -, -⟩ := ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  haveI : Module.Free ℤ ↥(periodLattice N) := Module.Free.of_basis b
  haveI : Module.Finite ℤ ↥(periodLattice N) := Module.Finite.of_basis b

  obtain ⟨v₀, w₀, d, hd, hgen₀, hinj₀⟩ := ModularCurve.exists_nsmul_eq_smul_add_smul_periodLattice N
  obtain ⟨u, hu_inj, -, hu_eq₀⟩ :=
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
  exact ⟨d ^ Module.finrank ℤ ↥(periodLattice N), fun m =>
    main_step N q hq1 I hqI u hu_inj hu_eq v₀ w₀ v₀.2 w₀.2 d hd hgen hinj m⟩

end Concrete

end P2MR2UB

end

open ModularCurve CuspForm

set_option maxHeartbeats 6400000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (N : ℕ) [NeZero N] (q : ℕ) [Fact q.Prime] (I : Ideal HeckeAlg) (hqI : (q : HeckeAlg) ∈ I) :
    ∃ C : ℕ, ∀ m : ℕ,
      Nat.card ↥(letI := heckeModuleBar N;
          Submodule.torsionBySet HeckeAlg (JZero N) (↑(I ^ m) : Set HeckeAlg)) ≤
        Nat.card ↥(Submodule.torsionBySet ↥(heckeLatticeAlgebra N ∅)
            (↥(heckeLatticeAlgebra N ∅) ⧸ Ideal.span {(q : ↥(heckeLatticeAlgebra N ∅)) ^ m})
            (↑((Ideal.map ((latticeRestrictHom N ∅).toRingHom.comp (heckeEvalForms N 2)) I) ^ m) :
              Set ↥(heckeLatticeAlgebra N ∅))) ^ 2 * q ^ C :=
  P2MR2UB.main N q I hqI

end S_ModularCurve_exists_natCard_torsionBySet_jZero_le_sq_natCard_torsionBySet_heckeLatticeAlgebra_quotient_mul_pow
end P2MW
export P2MW.S_ModularCurve_exists_natCard_torsionBySet_jZero_le_sq_natCard_torsionBySet_heckeLatticeAlgebra_quotient_mul_pow (solution)
