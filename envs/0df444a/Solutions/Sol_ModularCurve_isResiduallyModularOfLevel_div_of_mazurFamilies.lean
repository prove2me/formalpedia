-- Prove2me | solution 1 for ModularCurve.isResiduallyModularOfLevel_div_of_mazurFamilies
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9a90f34d-9aff-5e42-b94f-e118a1357b5e

import Definitions.Def_ModularCurve_ToricDichotomyData
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_GaloisRep_Residual
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_CuspForm_IntegralStructure
import Theorems.Thm_ModularCurve_mazurPrinciple_of_ne_one_of_toricDichotomy
import Theorems.Thm_ModularCurve_heckeInputsAll
import Theorems.Thm_ModularCurve_heckeOperatorsCommuteBar
import Theorems.Thm_ModularCurve_degeneracyPushforwardInputs
import Theorems.Thm_CuspForm_hasIntegralStructure_two
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois CuspForm.heckeAlgebra.instCommRing CuspForm.heckeAlgebra.instIsMulCommutative CuspForm.heckeAlgebra.instIsAddTorsionFree HeckeEis.instFiniteIndexHeckeUpper ModularCurve.Period.parabolicHoms_int_moduleFinite ModularCurve.Period.instGroupFG_SL2Z ModularCurve.Period.instIsNoetherian_addHom_int ModularCurve.Period.instGroupFG_Gamma0 ModularCurve.CuspSpace.instNonempty ModularCurve.CuspSpace.instSubsingletonOfOne ModularCurve.CuspSpace.instFinite ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraIntermediateFieldLaurent ModularCurve.instIsScalarTowerKaehlerIntermediateFieldLaurent ModularCurve.instIsScalarTowerIntermediateFieldLaurent ModularCurve.instModuleKaehlerIntermediateFieldLaurent ModularCurve.Gamma0Pair.isElliptic ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.instIsElliptic_tateLaurent WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral"
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.B3.instIsElliptic_goodModel AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ CuspForm.heckeAlgebra.coe_U CuspForm.heckeAlgebra.coe_T ModularForm.coe_heckeTLin_apply CuspForm.coe_heckeULin_apply CuspForm.coe_heckeTLin_apply ModularForm.coe_heckeULin_apply ModularCurve.Period.jConjMat_apply_zero_one ModularCurve.Period.jConjSL_coe ModularCurve.Period.jConjMat_apply_one_zero ModularCurve.Period.jConjMat_apply_one_one ModularCurve.Period.jConjGamma0_coe ModularCurve.Period.charInvolution_apply ModularCurve.Period.jConjMat_apply_zero_zero ModularCurve.Period.IsEquivariantPrimitive.periodHom_apply ModularCurve.Period.IsEquivariantPrimitive.period_one HeckeEis.heckeConjMat_apply_one_one HeckeEis.coe_heckeConjSL HeckeEis.mem_heckeUpperSL HeckeEis.resHom_apply HeckeEis.heckeConjMat_apply_zero_one HeckeEis.coe_transferAux HeckeEis.coe_heckeConj HeckeEis.alphaMat_apply_one_one HeckeEis.heckeConjMat_apply_one_zero HeckeEis.alphaMat_apply_zero_one HeckeEis.pullbackHom_apply HeckeEis.alphaMat_apply_one_zero HeckeEis.alphaMat_apply_zero_zero HeckeEis.heckeConjMat_apply_zero_zero ModularCurve.cuspCount_one ModularCurve.CuspSpace.cuspDenomAux_infty ModularCurve.CuspSpace.cuspDenomAux_coe ModularCurve.CuspSpace.cuspDenom_mk_zero ModularCurve.CuspSpace.cuspDenom_mk_infty ModularCurve.mapGL_apply_coe ModularCurve.ratPoint_one_zero"
p2m_attr_erase "simp" "ModularCurve.ratPoint_zero_right ModularCurve.CuspSpace.fromCoset_mk ModularCurve.CuspSpace.cuspDenom_mk ModularCurve.ratPoint_zero_one ModularCurve.ProjectiveLine.map_mk ModularCurve.qEulerFun_coeff ModularCurve.diffQExp_D ModularCurve.qEulerOn_apply ModularCurve.qEuler_coeff AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.gamma0PairMap_gen ModularCurve.moduliPointMapRingHom_mk ModularCurve.Gamma0Pair.mk.injEq ModularCurve.ModuliPoint.j_mk ModularCurve.Gamma0Pair.mk.sizeOf_spec ModularCurve.gamma0PairMap_toCurve WeierstrassCurve.Affine.vcY_vcYInv WeierstrassCurve.Affine.vcXInv_vcX WeierstrassCurve.Affine.Point.vcFun_zero WeierstrassCurve.Affine.vcX_vcXInv WeierstrassCurve.Affine.vcYInv_vcY WeierstrassCurve.Affine.Point.vcInvFun_zero WeierstrassCurve.ratPointHom_apply WeierstrassCurve.ratPointMap_zero ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ WeierstrassCurve.veluX_empty WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap AlgebraicCurve.Divisor.evalFun_zero AlgebraicCurve.Place.evalAt_one WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg"
p2m_attr_erase "simp" "WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero"
p2m_attr_erase "simp" "ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply HahnSeries.ramScale_apply AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none WeierstrassCurve.veluPointMap2_zero AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule"
p2m_attr_erase "simp" "AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU"

set_option autoImplicit false

noncomputable section

open ModularCurve

namespace W5Aux1
namespace D2

theorem mazurEngine_core
    (W : WeierstrassCurve ℤ) (p q N : ℕ) [Fact p.Prime] [NeZero N] [NeZero q]
    (hq : q.Prime) (hqp : q ≠ p) (hq1 : ((q : ℕ) : ZMod p) ≠ 1)

    (𝔪 : Ideal HeckeAlg) (hmax : 𝔪.IsMaximal) (hpm : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (heis : ¬ IsEventuallyEisenstein 𝔪)
    {V : Type} [AddCommGroup V] [Module (HeckeAlg ⧸ 𝔪) V]
    [DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V]
    [SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪) V]
    (hrank : Module.finrank (HeckeAlg ⧸ 𝔪) V = 2)
    (ι : V →+ JZero (N * q)) (hinj : Function.Injective ι)
    (hequiv : ∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (g • v) = g • ι v)
    (htors : letI := heckeModuleBar (N * q); ∀ v : V, ι v ∈ heckeTorsion (JZero (N * q)) 𝔪)
    (hcompat : letI := heckeModuleBar (N * q);
      ∀ (t : HeckeAlg) (v : V), ι (Ideal.Quotient.mk 𝔪 t • v) = t • ι v)
    (hlocal : ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
      (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : V, σ • v = v) ∧
      ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
        LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) = ((q : ℕ) : HeckeAlg ⧸ 𝔪))

    (htoric : ∃ (S : Finset Nat.Primes) (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        (frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime q ∧ A.IsFrobeniusAt frob q ∧ I ≤ A.inertiaSubgroupIn ℚ ∧
        (letI := heckeModuleBar (N * q)
         letI := heckeModuleBar N
         ExistsToricDichotomyDataQGuarded (JZero (N * q)) ⟨q, hq⟩ S I frob (JZero N)) ∧
        (letI := heckeModuleBar N
         HasLowerLevelTorsion S 𝔪 (JZero N) → W.IsResiduallyModularOfLevel p N)) :
    W.IsResiduallyModularOfLevel p N := by
  classical
  obtain ⟨S, I, frob, A, hA, hfrobA, hIA, htor, htransfer⟩ := htoric
  letI := heckeModuleBar (N * q)
  letI := heckeModuleBar N
  obtain ⟨𝒯, hfrobSq, hdich, hhecke⟩ := htor
  haveI : 𝔪.IsMaximal := hmax
  letI : Field (HeckeAlg ⧸ 𝔪) := Ideal.Quotient.field 𝔪

  have hp : p.Prime := Fact.out
  have hp0 : ((p : ℕ) : HeckeAlg ⧸ 𝔪) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk 𝔪) p]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hpm
  haveI : CharP (HeckeAlg ⧸ 𝔪) p := (CharP.charP_iff_prime_eq_zero hp).mpr hp0

  have hq0 : ((q : ℕ) : HeckeAlg ⧸ 𝔪) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (HeckeAlg ⧸ 𝔪) p q]
    exact fun h => hqp ((Nat.prime_dvd_prime_iff_eq hp hq).mp h).symm
  have hqu : IsUnit ((q : ℕ) : HeckeAlg ⧸ 𝔪) := isUnit_iff_ne_zero.mpr hq0

  have hq1' : ((q : ℕ) : HeckeAlg ⧸ 𝔪) ≠ 1 := by
    intro h
    apply hq1
    have hinjc : Function.Injective (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)) :=
      (ZMod.castHom (dvd_refl p) (HeckeAlg ⧸ 𝔪)).injective
    apply hinjc
    rw [map_natCast, map_one, h]

  have hscalar : (∀ v : V, ι v ∈ 𝒯) → ∃ lam : HeckeAlg ⧸ 𝔪, ∀ v : V, frob • v = lam • v := by
    intro hsub
    refine ⟨Ideal.Quotient.mk 𝔪 ((((⟨q, hq⟩ : Nat.Primes) : ℕ) : HeckeAlg) * heckeGen ⟨q, hq⟩), fun v => ?_⟩
    apply hinj
    rw [hequiv, hcompat]
    exact hhecke (ι v) (hsub v)
  have hdet : LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) =
      ((q : ℕ) : HeckeAlg ⧸ 𝔪) := (hlocal A hA).2 frob hfrobA
  have hunr : ∀ σ ∈ I, ∀ v : V, σ • v = v := fun σ hσ v => (hlocal A hA).1 σ (hIA hσ) v
  exact htransfer (ModularCurve.mazurPrinciple_of_ne_one_of_toricDichotomy hfrobSq hdich hmax heis hqu ι hinj hequiv
    htors hrank hdet hunr hscalar hq0 hq1')

end W5Aux1.D2

theorem solution
    (W : WeierstrassCurve ℤ) (p q M : ℕ) [Fact p.Prime] [NeZero q] (hq : q.Prime)
    (hqp : q ≠ p) (hqM : q ∣ M) (hq2 : ¬ q ^ 2 ∣ M)
    (hres : W.IsResiduallyModularOfLevel p M)
    (hq1 : ((q : ℕ) : ZMod p) ≠ 1)
    (hreal : ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → W.IsResiduallyModularOfLevel p (N * q) →
      ∃ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal ∧ ((p : ℕ) : HeckeAlg) ∈ 𝔪 ∧ ¬ IsEventuallyEisenstein 𝔪 ∧
        (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q → ℓ ≠ p →
          heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) ∧
        ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (HeckeAlg ⧸ 𝔪) V)
          (_ : DistribMulAction (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
          (_ : SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (HeckeAlg ⧸ 𝔪) V)
          (ι : V →+ JZero (N * q)),
          Module.finrank (HeckeAlg ⧸ 𝔪) V = 2 ∧ Function.Injective ι ∧
          (∀ (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (v : V), ι (g • v) = g • ι v) ∧
          (letI := heckeModuleBar (N * q); ∀ v : V, ι v ∈ heckeTorsion (JZero (N * q)) 𝔪) ∧
          (letI := heckeModuleBar (N * q);
            ∀ (t : HeckeAlg) (v : V), ι (Ideal.Quotient.mk 𝔪 t • v) = t • ι v) ∧
          ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime q →
            (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ v : V, σ • v = v) ∧
            ∀ frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt frob q →
              LinearMap.det (DistribSMul.toLinearMap (HeckeAlg ⧸ 𝔪) V frob) = ((q : ℕ) : HeckeAlg ⧸ 𝔪))
    (htoric : ∀ (N : ℕ) [NeZero N], ¬ q ∣ N → ∀ 𝔪 : Ideal HeckeAlg, 𝔪.IsMaximal →
      ((p : ℕ) : HeckeAlg) ∈ 𝔪 →
      (∀ (ℓ : ℕ) (hℓ : ℓ.Prime), W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N * q → ℓ ≠ p →
        heckeGen ⟨ℓ, hℓ⟩ - MvPolynomial.C (W.apOfModel ℓ : ℤ) ∈ 𝔪) →
      HeckeInputsAll (N * q) → HeckeOperatorsCommuteBar (N * q) →
      HeckeInputsAll N → HeckeOperatorsCommuteBar N → DegeneracyPushforwardInputs N q →
      CuspForm.HasIntegralStructure N 2 →
      ∃ (S : Finset Nat.Primes) (I : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
        (frob : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (A : ValuationSubring (AlgebraicClosure ℚ)),
        A.LiesOverPrime q ∧ A.IsFrobeniusAt frob q ∧ I ≤ A.inertiaSubgroupIn ℚ ∧
        (letI := heckeModuleBar (N * q)
         letI := heckeModuleBar N
         ExistsToricDichotomyDataQGuarded (JZero (N * q)) ⟨q, hq⟩ S I frob (JZero N)) ∧
        (letI := heckeModuleBar N
         HasLowerLevelTorsion S 𝔪 (JZero N) → W.IsResiduallyModularOfLevel p N)) :
    W.IsResiduallyModularOfLevel p (M / q) := by
  classical
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact hq2 (dvd_zero _)
  obtain ⟨N, rfl⟩ := hqM
  have hN0 : N ≠ 0 := by
    rintro rfl
    exact hM0 (mul_zero q)
  haveI : NeZero N := ⟨hN0⟩
  have hqN : ¬ q ∣ N := by
    rintro ⟨c, rfl⟩
    exact hq2 ⟨c, by ring⟩
  rw [Nat.mul_div_cancel_left N hq.pos]
  rw [mul_comm] at hres
  obtain ⟨𝔪, hmax, hpm, heis, hcong, V, _, _, _, _, ι, hrank, hinj, hequiv, htors, hcompat, hlocal⟩ :=
    hreal N hqN hres
  exact W5Aux1.D2.mazurEngine_core W p q N hq hqp hq1 𝔪 hmax hpm heis hrank ι hinj hequiv
    htors hcompat hlocal (htoric N hqN 𝔪 hmax hpm hcong
      (ModularCurve.heckeInputsAll _) (ModularCurve.heckeOperatorsCommuteBar _) (ModularCurve.heckeInputsAll _)
      (ModularCurve.heckeOperatorsCommuteBar _) (ModularCurve.degeneracyPushforwardInputs N q hq) (CuspForm.hasIntegralStructure_two _))

end

#print axioms solution

end S_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies
end P2MW
export P2MW.S_ModularCurve_isResiduallyModularOfLevel_div_of_mazurFamilies (solution)
