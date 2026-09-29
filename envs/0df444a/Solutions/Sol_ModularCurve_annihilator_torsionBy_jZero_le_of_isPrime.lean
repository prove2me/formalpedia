-- Prove2me | solution 1 for ModularCurve.annihilator_torsionBy_jZero_le_of_isPrime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/7516c306-b344-5be0-8519-29e344e9bbe6

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_PeriodLattice
import Theorems.Thm_ModularCurve_periodLatticeHeckeStable
import Theorems.Thm_ModularCurve_exists_basis_periodLattice_linearIndependent_real_span_eq_top
import Theorems.Thm_ModularCurve_exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime
p2m_attr_erase "instance" "ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin FLT.Gamma0FundamentalSet.instContinuousConstSMulSpecialLinearGroupFinOfNatNatIntUpperHalfPlane_definitions FLT.HyperbolicMeasure.instSMulInvariantMeasureSpecialLinearGroupFinOfNatNatIntUpperHalfPlaneVolume_definitions FLT.HyperbolicMeasure.instIsOpenPosMeasureUpperHalfPlaneVolume_definitions FLT.L2ProductionInstance.isFiniteMeasure_gamma0 FLT.L2ProductionInstance.countable_SL2Z FLT.L2ProductionInstance.countable_quotient FLT.L2ProductionInstance.nontrivial_gamma0L2 HeckeEis.instModuleCoeffH1par HeckeEis.instAddCommGroupCoeffH1par HeckeEis.instFiniteIndexHeckeUpper"
p2m_attr_erase "simp" "ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.coe_cuspidalDivisor₀ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff"
p2m_attr_erase "simp" "ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.jqNModC_one WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.veluY_empty WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal"
p2m_attr_erase "simp" "AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial"
p2m_attr_erase "simp" "WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen"
p2m_attr_erase "simp" "ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.injEq ModularCurve.ComplexPlaceDictionary.mk.sizeOf_spec FLT.TruncatedDomainPartition.unipotentDiagonalSum_zero HeckeEis.coeffCoboundaryMap_apply HeckeEis.heckeConjMat_apply_one_one"
p2m_attr_erase "simp" "HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero"

open scoped Pointwise

noncomputable section

namespace A04866

open ModularCurve

section Support

theorem annihilator_quotSMulTop_le {R L : Type*} [CommRing R] [AddCommGroup L] [Module R L]
    [Module.Finite R L] (𝔭 : Ideal R) [h𝔭 : 𝔭.IsPrime]
    (hann : Module.annihilator R L ≤ 𝔭) (x : R) (hx : x ∈ 𝔭) :
    Module.annihilator R (QuotSMulTop x L) ≤ 𝔭 := by
  let P : PrimeSpectrum R := ⟨𝔭, h𝔭⟩
  have hP : P ∈ Module.support R L := Module.mem_support_iff_of_finite.mpr hann
  have hPx : P ∈ PrimeSpectrum.zeroLocus {x} := by
    rw [PrimeSpectrum.mem_zeroLocus, Set.singleton_subset_iff]
    exact hx
  have hP' : P ∈ Module.support R (QuotSMulTop x L) := by
    rw [Module.support_quotSMulTop]
    exact ⟨hP, hPx⟩
  exact Module.mem_support_iff_of_finite.mp hP'

theorem annihilator_torsionBy_le_of_map {R J L : Type*} [CommRing R] [AddCommGroup J] [Module R J]
    [AddCommGroup L] [Module R L] [Module.Finite R L] (x : R) (𝔭 : Ideal R) [𝔭.IsPrime]
    (hx : x ∈ 𝔭) (hannL : Module.annihilator R L ≤ 𝔭)
    (ψ : L →ₗ[R] J) (hψ : ∀ l, x • ψ l = 0)
    (hker : ∀ l, ψ l = 0 → l ∈ x • (⊤ : Submodule R L)) :
    (Submodule.torsionBy R J x).annihilator ≤ 𝔭 := by
  let ψ' : L →ₗ[R] Submodule.torsionBy R J x :=
    LinearMap.codRestrict _ ψ (fun l => (Submodule.mem_torsionBy_iff x _).mpr (hψ l))
  have hle : x • (⊤ : Submodule R L) ≤ LinearMap.ker ψ' := by
    intro l hl
    obtain ⟨m, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists l x ⊤).mp hl
    rw [LinearMap.mem_ker, map_smul]
    exact Subtype.ext (by simp [ψ'])
  let φ : QuotSMulTop x L →ₗ[R] Submodule.torsionBy R J x := (x • ⊤ : Submodule R L).liftQ ψ' hle
  have hφ : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    refine Submodule.ker_liftQ_eq_bot _ _ _ ?_
    intro l hl
    rw [LinearMap.mem_ker] at hl
    exact hker l (by simpa [ψ'] using congrArg Subtype.val hl)
  exact (LinearMap.annihilator_le_of_injective φ hφ).trans
    (annihilator_quotSMulTop_le 𝔭 hannL x hx)

def pullback {J Q L : Type*} [AddCommGroup J] [AddCommGroup Q] [AddCommGroup L]
    (u : J →+ Q) (hinj : Function.Injective u) (w : L →+ Q) (hw : ∀ l, w l ∈ u.range) : L →+ J where
  toFun l := Classical.choose (AddMonoidHom.mem_range.mp (hw l))
  map_zero' := hinj (by
    rw [Classical.choose_spec (AddMonoidHom.mem_range.mp (hw 0)), map_zero, map_zero])
  map_add' a b := hinj (by
    rw [Classical.choose_spec (AddMonoidHom.mem_range.mp (hw _)), map_add, map_add,
      Classical.choose_spec (AddMonoidHom.mem_range.mp (hw a)),
      Classical.choose_spec (AddMonoidHom.mem_range.mp (hw b))])

theorem pullback_spec {J Q L : Type*} [AddCommGroup J] [AddCommGroup Q] [AddCommGroup L]
    (u : J →+ Q) (hinj : Function.Injective u) (w : L →+ Q) (hw : ∀ l, w l ∈ u.range) (l : L) :
    u (pullback u hinj w hw l) = w l :=
  Classical.choose_spec (AddMonoidHom.mem_range.mp (hw l))

end Support

section Concrete

variable (N : ℕ) [NeZero N]

abbrev D := Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2)

theorem dualHeckeRep_eq_zero_of_span {n : ℕ} (c : Fin n → D N)
    (hsp : Submodule.span ℝ (Set.range c) = ⊤) (s : HeckeAlg)
    (hs : ∀ i, dualHeckeRep N s (c i) = 0) : dualHeckeRep N s = 0 := by
  have h : (dualHeckeRep N s).restrictScalars ℝ = (0 : Module.End ℂ (D N)).restrictScalars ℝ := by
    apply LinearMap.ext_on_range hsp
    intro i
    rw [LinearMap.restrictScalars_apply, LinearMap.restrictScalars_apply, LinearMap.zero_apply]
    exact hs i
  apply LinearMap.ext
  intro φ
  simpa using LinearMap.congr_fun h φ

theorem uniformization_heckeEvalBar (hcomm : HeckeOperatorsCommuteBar N)
    (u : JZero N →+ (D N ⧸ periodLattice N))
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (t : HeckeAlg) :
    ∀ (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeEvalBar hcomm t x) = Submodule.Quotient.mk (dualHeckeRep N t φ) := by
  induction t using MvPolynomial.induction_on with
  | C a =>
      intro x φ hx
      rw [heckeEvalBar_C, Module.End.intCast_apply, map_zsmul, hx, dualHeckeRep_C]
      exact (map_zsmul (Submodule.mkQ (periodLattice N)) a φ).symm
  | add s t hs ht =>
      intro x φ hx
      rw [RingHom.map_add, LinearMap.add_apply, u.map_add, hs x φ hx, ht x φ hx, RingHom.map_add,
        LinearMap.add_apply, Submodule.Quotient.mk_add]
  | mul_X q ℓ hq =>
      intro x φ hx
      have hX : (MvPolynomial.X ℓ : HeckeAlg) = heckeGen ℓ := rfl
      rw [RingHom.map_mul, Module.End.mul_apply, hX, heckeEvalBar_heckeGen, RingHom.map_mul,
        Module.End.mul_apply]
      exact hq _ _ (hu ℓ x φ hx)

theorem heckeEvalBar_eq_zero_of_lattice (hcomm : HeckeOperatorsCommuteBar N)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (u : JZero N →+ (D N ⧸ periodLattice N)) (hinj : Function.Injective u)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (s : HeckeAlg) (hs : ∀ l : periodLattice N, dualHeckeRep N s (l : D N) = 0) (x : JZero N) :
    heckeEvalBar hcomm s x = 0 := by
  have hD : dualHeckeRep N s = 0 :=
    dualHeckeRep_eq_zero_of_span N (fun i => ((b i : periodLattice N) : D N)) hsp s (fun i => hs _)
  obtain ⟨φ, hφ⟩ := Submodule.Quotient.mk_surjective (periodLattice N) (u x)
  have h1 : u (heckeEvalBar hcomm s x) = 0 := by
    rw [uniformization_heckeEvalBar N hcomm u hu s x φ hφ.symm, hD, LinearMap.zero_apply,
      Submodule.Quotient.mk_zero]
  exact hinj (h1.trans u.map_zero.symm)

attribute [local instance] ModularCurve.heckeModuleBar ModularCurve.periodLatticeModule

theorem coe_periodLatticeHeckeEnd (hst : PeriodLatticeHeckeStable N) (t : HeckeAlg)
    (l : periodLattice N) :
    ((periodLatticeHeckeEnd N t l : periodLattice N) : D N) = dualHeckeRep N t (l : D N) :=
  coe_periodLatticeHeckeEnd_apply hst t l

theorem annihilator_lattice_le (hcomm : HeckeOperatorsCommuteBar N)
    (hst : PeriodLatticeHeckeStable N)
    {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : periodLattice N) : D N)) = ⊤)
    (u : JZero N →+ (D N ⧸ periodLattice N)) (hinj : Function.Injective u)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ)) :
    Module.annihilator HeckeAlg (periodLattice N) ≤ Module.annihilator HeckeAlg (JZero N) := by
  intro s hs
  rw [Module.mem_annihilator] at hs ⊢
  intro x
  rw [heckeModuleBar_smul_def hcomm]
  refine heckeEvalBar_eq_zero_of_lattice N hcomm b hsp u hinj hu s ?_ x
  intro l
  have hsl := hs l
  rw [periodLatticeModule_smul_def] at hsl
  rw [← coe_periodLatticeHeckeEnd N hst s l, hsl, Submodule.coe_zero]

theorem finite_lattice {n : ℕ} (b : Module.Basis (Fin n) ℤ (periodLattice N)) :
    Module.Finite HeckeAlg (periodLattice N) := by
  haveI : Module.Finite ℤ (periodLattice N) := Module.Finite.of_basis b
  exact Module.Finite.of_restrictScalars_finite ℤ HeckeAlg (periodLattice N)

def divP (p : ℕ) : periodLattice N →+ (D N ⧸ periodLattice N) where
  toFun l := Submodule.Quotient.mk ((p : ℂ)⁻¹ • (l : D N))
  map_zero' := by simp
  map_add' a b := by
    rw [Submodule.coe_add, smul_add, Submodule.Quotient.mk_add]

omit [NeZero N] in
theorem divP_apply (p : ℕ) (l : periodLattice N) :
    divP N p l = Submodule.Quotient.mk ((p : ℂ)⁻¹ • (l : D N)) := rfl

omit [NeZero N] in
theorem nsmul_inv_smul (p : ℕ) (hp : p.Prime) (v : D N) : p • ((p : ℂ)⁻¹ • v) = v := by
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hp.ne_zero), one_smul]

omit [NeZero N] in
theorem nsmul_divP (p : ℕ) (hp : p.Prime) (l : periodLattice N) : p • divP N p l = 0 := by
  rw [divP_apply, ← Submodule.mkQ_apply, ← map_nsmul, nsmul_inv_smul N p hp,
    Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact l.2

omit [NeZero N] in
theorem divP_mem_range (p : ℕ) (hp : p.Prime) (u : JZero N →+ (D N ⧸ periodLattice N))
    (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) (l : periodLattice N) :
    divP N p l ∈ u.range :=
  htors _ ((isOfFinAddOrder_iff_nsmul_eq_zero).mpr ⟨p, hp.pos, nsmul_divP N p hp l⟩)

def psiAdd (p : ℕ) (hp : p.Prime) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range) :
    periodLattice N →+ JZero N :=
  pullback u hinj (divP N p) (divP_mem_range N p hp u htors)

omit [NeZero N] in
theorem u_psiAdd (p : ℕ) (hp : p.Prime) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (l : periodLattice N) :
    u (psiAdd N p hp u hinj htors l) = Submodule.Quotient.mk ((p : ℂ)⁻¹ • (l : D N)) :=
  pullback_spec u hinj (divP N p) (divP_mem_range N p hp u htors) l

def psi (p : ℕ) (hp : p.Prime) (hcomm : HeckeOperatorsCommuteBar N)
    (hst : PeriodLatticeHeckeStable N) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ)) :
    periodLattice N →ₗ[HeckeAlg] JZero N where
  toFun := psiAdd N p hp u hinj htors
  map_add' := (psiAdd N p hp u hinj htors).map_add
  map_smul' t l := by
    apply hinj
    rw [RingHom.id_apply, periodLatticeModule_smul_def, u_psiAdd, coe_periodLatticeHeckeEnd N hst,
      heckeModuleBar_smul_def hcomm,
      uniformization_heckeEvalBar N hcomm u hu t _ _ (u_psiAdd N p hp u hinj htors l),
      map_smul]

theorem psi_apply (p : ℕ) (hp : p.Prime) (hcomm : HeckeOperatorsCommuteBar N)
    (hst : PeriodLatticeHeckeStable N) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (hu : ∀ (ℓ : Nat.Primes) (x : JZero N) (φ : D N),
      u x = Submodule.Quotient.mk φ →
        u (heckeOperatorBar N ℓ x) = Submodule.Quotient.mk (dualHeckeRep N (heckeGen ℓ) φ))
    (l : periodLattice N) :
    psi N p hp hcomm hst u hinj htors hu l = psiAdd N p hp u hinj htors l := rfl

theorem p_smul_psiAdd (p : ℕ) (hp : p.Prime) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (l : periodLattice N) :
    (p : HeckeAlg) • psiAdd N p hp u hinj htors l = 0 := by
  rw [Nat.cast_smul_eq_nsmul]
  apply hinj
  rw [map_nsmul, u_psiAdd, ← divP_apply, nsmul_divP N p hp, map_zero]

theorem mem_of_psiAdd_eq_zero (p : ℕ) (hp : p.Prime) (u : JZero N →+ (D N ⧸ periodLattice N))
    (hinj : Function.Injective u) (htors : ∀ y, IsOfFinAddOrder y → y ∈ u.range)
    (l : periodLattice N) (hl : psiAdd N p hp u hinj htors l = 0) :
    l ∈ (p : HeckeAlg) • (⊤ : Submodule HeckeAlg (periodLattice N)) := by
  have h : Submodule.Quotient.mk ((p : ℂ)⁻¹ • (l : D N)) = (0 : D N ⧸ periodLattice N) := by
    rw [← u_psiAdd N p hp u hinj htors l, hl, map_zero]
  rw [Submodule.Quotient.mk_eq_zero] at h
  set m : periodLattice N := ⟨(p : ℂ)⁻¹ • (l : D N), h⟩ with hm
  have hmem := Submodule.smul_mem_pointwise_smul m (p : HeckeAlg)
    (⊤ : Submodule HeckeAlg (periodLattice N)) Submodule.mem_top
  rw [Nat.cast_smul_eq_nsmul HeckeAlg p m] at hmem
  have hc : ((p • m : periodLattice N) : D N) = p • (m : D N) :=
    map_nsmul (periodLattice N).subtype p m
  have hl' : l = p • m := by
    apply Subtype.ext
    rw [hc, hm]
    exact (nsmul_inv_smul N p hp (l : D N)).symm
  rwa [hl']

end Concrete

section Main

theorem main (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime)
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (𝔭 : Ideal ModularCurve.HeckeAlg) (h𝔭 : 𝔭.IsPrime)
    (hann : letI := ModularCurve.heckeModuleBar N;
      Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N) ≤ 𝔭)
    (hp𝔭 : (p : ModularCurve.HeckeAlg) ∈ 𝔭) :
    letI := ModularCurve.heckeModuleBar N
    (Submodule.torsionBy ModularCurve.HeckeAlg (ModularCurve.JZero N)
      (p : ModularCurve.HeckeAlg)).annihilator ≤ 𝔭 := by
  letI := ModularCurve.heckeModuleBar N
  letI := ModularCurve.periodLatticeModule N
  haveI := h𝔭

  have hst : PeriodLatticeHeckeStable N := ModularCurve.periodLatticeHeckeStable N
  obtain ⟨n, b, -, hsp⟩ :=
    ModularCurve.exists_basis_periodLattice_linearIndependent_real_span_eq_top N
  obtain ⟨u, hinj, htors, hu⟩ :=
    ModularCurve.exists_injective_heckeEquivariant_addMonoidHom_jZero_quotient_periodLattice N hin hst

  haveI : Module.Finite HeckeAlg (periodLattice N) := finite_lattice N b
  have hannL : Module.annihilator HeckeAlg (periodLattice N) ≤ 𝔭 :=
    (annihilator_lattice_le N hcomm hst b hsp u hinj hu).trans hann

  exact annihilator_torsionBy_le_of_map (p : HeckeAlg) 𝔭 hp𝔭 hannL
    (psi N p hp hcomm hst u hinj htors hu)
    (fun l => p_smul_psiAdd N p hp u hinj htors l)
    (fun l hl => mem_of_psiAdd_eq_zero N p hp u hinj htors l hl)

end Main

end A04866

end

theorem solution (N : ℕ) [NeZero N] (p : ℕ) (hp : p.Prime)
    (hin : ModularCurve.HeckeInputsAll N) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N)
    (𝔭 : Ideal ModularCurve.HeckeAlg) (h𝔭 : 𝔭.IsPrime)
    (hann : letI := ModularCurve.heckeModuleBar N;
      Module.annihilator ModularCurve.HeckeAlg (ModularCurve.JZero N) ≤ 𝔭)
    (hp𝔭 : (p : ModularCurve.HeckeAlg) ∈ 𝔭) :
    letI := ModularCurve.heckeModuleBar N
    (Submodule.torsionBy ModularCurve.HeckeAlg (ModularCurve.JZero N) (p : ModularCurve.HeckeAlg)).annihilator ≤ 𝔭 :=
  A04866.main N p hp hin hcomm 𝔭 h𝔭 hann hp𝔭

end S_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime
end P2MW
export P2MW.S_ModularCurve_annihilator_torsionBy_jZero_le_of_isPrime (solution)
