-- Prove2me | solution 1 for ModularCurve.theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/d54911dc-6cd6-59fb-a590-8017f3ce7cf6

import Mathlib
import Definitions.Def_ModularCurve_SSCarrier
import Definitions.Def_ModularCurve_SSHeckeV2
import Definitions.Def_AlgebraicCurve_WeilOfKaehler
import Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_WeightDivisor
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_Repartitions
import Theorems.Thm_ModularCurve_ssResiduePairing_ssHeckeFun_eq_comp_traceAlong
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
import Theorems.Thm_ModularCurve_heckeAlphaCIntegral_unconditional
import Theorems.Thm_ModularCurve_heckeBetaCIntegral_unconditional
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion"
p2m_attr_erase "instance" "instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin"
p2m_attr_erase "simp" "AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.serrePairing_apply_mk AlgebraicCurve.residueSumOffChartLinear_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁"
p2m_attr_erase "simp" "WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.genusOnePic0Equiv_apply WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some"
p2m_attr_erase "simp" "FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 24000000

open AlgebraicCurve ModularCurve

theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K] (N : ℕ) [NeZero N]
    [AlgebraicCurve.IsCurveOver K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := ↥(modularFunctionFieldC K N))]
    [∀ w : AlgebraicCurve.Place K ↥(modularFunctionFieldC K N), w.DCoordGenerates]
    [Nontrivial (Ω[↥(modularFunctionFieldC K N)⁄K])]
    [AlgebraicCurve.HasPrincipalDivisors K ↥(modularFunctionFieldC K N)]
    [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(modularFunctionFieldC K N)]
    (hagree : AlgebraicCurve.WeilKaehlerAgree K ↥(modularFunctionFieldC K N))
    (hN : (N : K) ≠ 0) (m : ℕ) (hm : 1 ≤ m)
    (SS : Finset (AlgebraicCurve.Place K ↥(modularFunctionFieldC K N))) (hSS : ∀ x, x ∈ SS ↔ x ∈ ssPlaces p N K)
    (D' : AlgebraicCurve.Divisor K ↥(modularFunctionFieldC K N))
    (hD'1 : ∀ w, w ∈ ssPlaces p N K → ((placeWidth N w : ℤ) ∣ (m : ℤ)) → D' w = ModularCurve.weightDivisor K N m w - 1)
    (hD'0 : ∀ w, ¬ (w ∈ ssPlaces p N K ∧ ((placeWidth N w : ℤ) ∣ (m : ℤ))) → D' w = ModularCurve.weightDivisor K N m w)
    (Θ : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ)) →ₗ[K]
        Module.Dual K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'))
    (hΘres : ∀ v (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0)
          (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈
            AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
          Θ v ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
            = ∑ x ∈ SS, kaehlerResidueTerm ω
                (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) x)
    (ℓ : ℕ) [Fact ℓ.Prime] [NeZero ℓ] (hℓN : ¬ ℓ ∣ N) (hℓp : ℓ ≠ p)
    [AlgebraicCurve.IsCurveOver K ↥(charLDegeneracyRoof K N ℓ)] [AlgebraicCurve.HasCanonicalLocalResidueKStar K ↥(charLDegeneracyRoof K N ℓ)]
    [∀ w : AlgebraicCurve.Place K ↥(charLDegeneracyRoof K N ℓ), w.DCoordGenerates] [Nontrivial (Ω[↥(charLDegeneracyRoof K N ℓ)⁄K])]
    (TΩ : Module.End K ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')) (s : K) (hs : s ≠ 0)
    (H1 : ∀ μ : ↥(AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
      μ = 0 ∨ ∃ (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0) (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
        μ = ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩)
    (H2z : ∀ (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0) (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D'),
      Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ) ω) = 0 → TΩ ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩ = 0)
    (H2n : ∀ (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0) (hmem : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D')
      (hT : Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ) ω) ≠ 0),
      ∃ hmem' : AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D',
        TΩ ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩ = s • ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hT, hmem'⟩)
    (v : ModularCurve.SSCarrier p N K hp5 (2 * (m : ℤ))) :
    Θ (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v) = s⁻¹ • TΩ.dualMap (Θ v) := by
  classical

  have hαI : HeckeAlphaCIntegral K N ℓ := ModularCurve.heckeAlphaCIntegral_unconditional K N ℓ
  have hβI : HeckeBetaCIntegral K N ℓ := ModularCurve.heckeBetaCIntegral_unconditional K N ℓ
  have hstab : ∀ w : Place K ↥(charLDegeneracyRoof K N ℓ),
      Place.restrictAlong (heckeAlphaC K N ℓ) hαI w ∈ SS ↔ Place.restrictAlong (heckeBetaC K N ℓ) hβI w ∈ SS := by
    intro w
    rw [hSS, hSS]
    exact ModularCurve.restrictAlong_heckeAlphaC_mem_ssPlaces_iff_restrictAlong_heckeBetaC_mem_ssPlaces
      p hp5 K N ℓ hN hℓN hℓp hαI hβI w

  have hpℓ : ¬ p ∣ ℓ := fun h => hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) (Fact.out)).mp h).symm
  have hℓK : (ℓ : K) ≠ 0 := fun h => hpℓ ((CharP.cast_eq_zero_iff K p ℓ).mp h)
  haveI : NeZero ((ℓ : ℕ) : K) := ⟨hℓK⟩
  haveI := IsSepClosed.hasEnoughRootsOfUnity K ℓ
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ℓ
  have hRF := ModularCurve.ssResiduePairing_ssHeckeFun_eq_comp_traceAlong p hp5 K N ℓ hN hℓN hℓp
    (Units.mk0 ζ0 (hζ0.ne_zero (NeZero.ne ℓ))) (by simpa using hζ0) m hm hαI hβI SS hSS hstab v

  have hbd : ∀ (ω : Ω[↥(modularFunctionFieldC K N)⁄K]) (hω : ω ≠ 0),
      AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω ∈ AlgebraicCurve.omegaSpace (K := K) (F := ↥(modularFunctionFieldC K N)) D' →
      (∀ x : ModularCurve.SSIndex p N K hp5 (2 * (m : ℤ)), ModularCurve.weightDivisor K N m x.1 - 1 ≤ x.1.ordDifferential ω) ∧
      (∀ x ∈ SS, ¬ ((placeWidth N x : ℤ) ∣ (m : ℤ)) → ModularCurve.weightDivisor K N m x ≤ x.ordDifferential ω) := by
    intro ω hω hmem
    have hle : D' ≤ canonicalDivisorOf hω := (hagree hω).2.2 D' hmem
    refine ⟨fun x => ?_, fun x hx hdx => ?_⟩
    · have hdiv : (placeWidth N x.1 : ℤ) ∣ (m : ℤ) := by
        obtain ⟨_, _, _, h, _⟩ := x.2
        simpa using h
      have h1 := hle x.1
      rw [canonicalDivisorOf_apply hω x.1, hD'1 x.1 x.2.1 hdiv] at h1
      exact h1
    · have h1 := hle x
      rw [canonicalDivisorOf_apply hω x, hD'0 x (fun h => hdx h.2)] at h1
      exact h1

  apply LinearMap.ext
  intro μ
  rcases H1 μ with rfl | ⟨ω, hω, hmem, rfl⟩
  · simp only [map_zero]
  obtain ⟨hωi, hωn⟩ := hbd ω hω hmem

  have eL : Θ (ModularCurve.ssHeckeFun p N K hp5 (2 * (m : ℤ)) ℓ v)
        ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩
      = ∑ z ∈ SS, kaehlerResidueTerm (Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ) ω))
          (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) z :=
by
    have h2 := congrFun hRF ⟨ω, hωi, hωn⟩
    dsimp only at h2
    rw [hΘres _ ω hω hmem]
    exact h2
  rw [eL, LinearMap.smul_apply, LinearMap.dualMap_apply]
  by_cases hT : Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ) ω) = 0
  ·
    have key : TΩ ⟨AlgebraicCurve.weilOfKaehler K ↥(modularFunctionFieldC K N) hω, hmem⟩ = 0 := H2z ω hω hmem hT
    rw [key, map_zero, smul_zero]
    refine Finset.sum_eq_zero fun z _ => ?_
    have hz : ∀ (η : Ω[↥(modularFunctionFieldC K N)⁄K]), η = 0 →
        kaehlerResidueTerm η (diagonalHom K ↥(modularFunctionFieldC K N) (ModularCurve.liftFun p N K hp5 (2 * (m : ℤ)) v)) z = 0 := by
      rintro η rfl
      unfold kaehlerResidueTerm
      rw [z.differentialCoeff_zero, mul_zero, map_zero, map_zero]
    exact hz _ hT
  ·
    obtain ⟨hmem', key⟩ := H2n ω hω hmem hT
    rw [key, (Θ v).map_smul, smul_eq_mul, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hs, one_mul]
    have hR := hΘres v (Differential.traceAlong (heckeBetaC K N ℓ)
          ((algebraMap K ↥(charLDegeneracyRoof K N ℓ) ((ℓ : K) ^ (m - 1)) * ModularCurve.heckeMultiplier N K ℓ ^ m) •
            Differential.pullbackAlong (heckeAlphaC K N ℓ) ω)) hT hmem'
    exact hR.symm

end S_ModularCurve_theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler
end P2MW
export P2MW.S_ModularCurve_theta_ssHeckeFun_eq_inv_smul_dualMap_of_forall_weilOfKaehler (solution)
