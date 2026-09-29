-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/083b22fa-f169-5224-9da3-bb1b96afa100

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
import Theorems.Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular WeierstrassCurve.Affine.instIsDiscreteValuationRingSubtypeFunctionFieldMemValuationSubringValuationSubringWithZeroMultiplicativeIntValuationInfty WeierstrassCurve.Affine.valuationInfty_isNontrivial WeierstrassCurve.veluQuotient2_isShortNF WeierstrassCurve.instIsShortNFMk"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff WeierstrassCurve.mapPointHom_apply WeierstrassCurve.mapPoint_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero AddMonoid.End.dualEndDataOfSurjective_trace AddMonoid.End.dualEndDataOfSurjective_norm"

set_option autoImplicit false

open AlgebraicCurve ModularCurve CerednikDrinfeld

namespace K1

section Generic

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
variable [HasPrincipalDivisors K F']
variable (φ ψ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hψ : ψ.toRingHom.IsIntegral)

open Classical in
theorem correspondence_single_one_apply (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ W ∈ Place.fiberAlong φ hφ x,
        if W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finset.sum_apply']
  refine Finset.sum_congr rfl fun W _ => ?_
  rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]

open Classical in
theorem correspondence_single_one_apply_eq_finsum (x y : Place K F) :
    Divisor.correspondence φ ψ hφ hψ (Finsupp.single x 1) y =
      ∑ᶠ W : Place K F',
        if W.restrictAlong φ hφ = x ∧ W.restrictAlong ψ hψ = y then
          (W.ramificationIndexAlong φ : ℤ) * (W.inertiaDegAlong ψ hψ : ℤ) else 0 := by
  classical
  rw [correspondence_single_one_apply]
  symm
  rw [finsum_eq_sum_of_support_subset _ (s := Place.fiberAlong φ hφ x)]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    simp only [hW, true_and]
  · intro W hW
    rw [Function.mem_support] at hW
    simp only [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (if_neg fun h => hx h.1)

end Generic

section SS

open ModularCurve

variable (p : ℕ) (K : Type*) [Field K] [DecidableEq K] (N : ℕ) [NeZero N]

theorem ssHeckeMatrixC_apply_eq_correspondence (ℓ : ℕ) [NeZero ℓ]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)]
    (hα : (heckeAlphaC K N ℓ).toRingHom.IsIntegral) (hβ : (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (y x : ↥(ssPlaces p N K)) :
    ssHeckeMatrixC p K N ℓ hα hβ y x =
      Divisor.correspondence (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) hβ hα (Finsupp.single x.1 1) y.1 := by
  rw [correspondence_single_one_apply_eq_finsum]
  all_goals rfl

variable [Fact p.Prime] [CharP K p]

theorem ssHeckeFamilyC_apply_of_ne (data : ModularPolynomialData p) (hKr : KroneckerCongruence p data)
    (hlegs : ∀ (ℓ : ℕ) [NeZero ℓ], (heckeAlphaC K N ℓ).toRingHom.IsIntegral ∧ (heckeBetaC K N ℓ).toRingHom.IsIntegral)
    (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K N ℓ)] (y x : ↥(ssPlaces p N K)) :
    ssHeckeFamilyC p K N data hKr hlegs ℓ y x =
      Divisor.correspondence (heckeBetaC K N ℓ) (heckeAlphaC K N ℓ) (hlegs ℓ).2 (hlegs ℓ).1
        (Finsupp.single x.1 1) y.1 := by
  unfold ssHeckeFamilyC
  rw [if_neg hℓ]
  exact ssHeckeMatrixC_apply_eq_correspondence p K N ℓ (hlegs ℓ).1 (hlegs ℓ).2 y x

end SS

section Datum

open ModularCurve

variable {p : ℕ} [Fact p.Prime] {K : Type*} [Field K] [CharP K p] [DecidableEq K] {M s : ℕ} [NeZero M] [NeZero s]
variable (X : SSLevelDatum p K M s)

theorem edgeHecke_apply_of_ne (ℓ : Nat.Primes) (hℓ : (ℓ : ℕ) ≠ p) [NeZero (ℓ : ℕ)]
    [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) ℓ)] (y x : ↥(ssPlaces p (M * s) K)) :
    X.edgeHecke ℓ y x =
      Divisor.correspondence (heckeBetaC K (M * s) ℓ) (heckeAlphaC K (M * s) ℓ)
        (X.legsIntegral (M * s) ℓ).2 (X.legsIntegral (M * s) ℓ).1 (Finsupp.single x.1 1) y.1 :=
  ssHeckeFamilyC_apply_of_ne p K (M * s) X.frobData X.kronecker (X.legsIntegral (M * s)) ℓ hℓ y x

end Datum

end K1

namespace C3Reduce

set_option synthInstance.maxHeartbeats 400000

section Generic

variable {q' : ℕ} [Fact q'.Prime] {K : Type*} [Field K] [CharP K q'] [DecidableEq K]

theorem pw_pos [IsAlgClosed K] (hq5 : 5 ≤ q') (N : ℕ) [NeZero N] (hq'N : ¬ q' ∣ N)
    (w : Place K ↥(modularFunctionFieldC K N)) (hw : w ∈ ssPlaces q' N K) : 0 < placeWidth N w := by
  have hdvd := ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces (K := K) hq5 hq'N hw
  have hjpos := jWidth_pos (w.evalAt (jGeomGen K N))
  have hrpos : 0 < placeRamificationJ N w := by
    rcases Nat.eq_zero_or_pos (placeRamificationJ N w) with h | h
    · rw [h, zero_dvd_iff] at hdvd
      omega
    · exact h
  unfold placeWidth
  exact Nat.div_pos (Nat.le_of_dvd hjpos hdvd) hrpos

variable {M s : ℕ} [NeZero M] [NeZero s]
variable [Fintype ↥(ssPlaces q' (M * s) K)] [Fintype ↥(ssPlaces q' M K)]
variable [DecidableEq ↥(ssPlaces q' (M * s) K)] [DecidableEq ↥(ssPlaces q' M K)]
variable (X : SSLevelDatum q' K M s)

theorem padj_entry
    (padj : Fin 2 → ((↥(ssPlaces q' M K) → ℤ) →ₗ[ℤ] (↥(ssPlaces q' (M * s) K) → ℤ)))
    (hadj : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M K) → ℤ) (y : ↥(ssPlaces q' (M * s) K) → ℤ),
        (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
          ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e)
    (i : Fin 2) (x : ↥(ssPlaces q' M K) → ℤ) (e : ↥(ssPlaces q' (M * s) K)) :
    (X.degeneracyData.w e : ℤ) * padj i x e =
      (Nat.toPNat' (placeWidth M ((![X.degeneracyData.a, X.degeneracyData.b] i) e).1) : ℤ) *
        x ((![X.degeneracyData.a, X.degeneracyData.b] i) e) := by
  have h := hadj i x (Pi.single e 1)
  have hL : ∀ v : ↥(ssPlaces q' M K),
      (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec (Pi.single e 1) v =
        if (![X.degeneracyData.a, X.degeneracyData.b] i) e = v then 1 else 0 := by
    intro v
    rw [Matrix.mulVec_single_one]
    rfl
  simp_rw [hL] at h
  rw [Finset.sum_eq_single ((![X.degeneracyData.a, X.degeneracyData.b] i) e)] at h
  · rw [if_pos rfl, mul_one] at h
    rw [Finset.sum_eq_single e] at h
    · rw [Pi.single_eq_same, mul_one] at h
      rw [← h]
    · intro e' _ he'
      rw [Pi.single_eq_of_ne he', mul_zero, zero_mul]
    · intro he
      exact absurd (Finset.mem_univ e) he
  · intro v _ hv
    rw [if_neg (Ne.symm hv), mul_zero, zero_mul]
  · intro hv
    exact absurd (Finset.mem_univ _) hv

theorem ram_mul_pw [IsAlgClosed K] (hs : s.Prime) (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    (hq'Ms : ¬ q' ∣ M * s) (e : ↥(ssPlaces q' (M * s) K)) :
    Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) e.1 * placeWidth (M * s) e.1 =
        placeWidth M (X.degeneracyData.a e).1 ∧
    Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 * placeWidth (M * s) e.1 =
        placeWidth M (X.degeneracyData.b e).1 := by
  have hram := ModularCurve.ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong
    M s q' hs hsq' hq'M (k := K)
    ![levelAlphaC K M s X.mem_M, levelBetaC K M s X.mem_s]
    (fun i => by fin_cases i; exacts [X.fstIntegral, X.sndIntegral])
    (fun x => coe_levelAlphaC K M s X.mem_M x) (fun x => coe_levelBetaC K M s X.mem_s x)
  have hside := ModularCurve.placeRamificationJ_dvd_jWidth_of_mem_ssPlaces (K := K) hq5 hq'Ms e.2
  exact ⟨hram 0 e.1 hside, hram 1 e.1 hside⟩

theorem inertia_one [IsAlgClosed K] (x : ↥(ssPlaces q' (M * s) K)) :
    Place.inertiaDegAlong (levelAlphaC K M s X.mem_M) X.fstIntegral x.1 = 1 := by
  letI := AlgebraicCurve.algebraAlong (levelAlphaC K M s X.mem_M)
  haveI := AlgebraicCurve.isScalarTower_along (levelAlphaC K M s X.mem_M)
  haveI := AlgebraicCurve.isIntegral_along (levelAlphaC K M s X.mem_M) X.fstIntegral
  have h := AlgebraicCurve.Place.deg_restrict_mul_inertiaDeg (F := ↥(modularFunctionFieldC K M)) x.1
  rw [ModularCurve.place_deg_eq_one_of_isAlgClosed K (M * s) x.1,
    ModularCurve.place_deg_eq_one_of_isAlgClosed K M _, one_mul] at h
  exact h

theorem padj_explicit [IsAlgClosed K] (hs : s.Prime) (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    (hq'Ms : ¬ q' ∣ M * s)
    (padj : Fin 2 → ((↥(ssPlaces q' M K) → ℤ) →ₗ[ℤ] (↥(ssPlaces q' (M * s) K) → ℤ)))
    (hadj : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M K) → ℤ) (y : ↥(ssPlaces q' (M * s) K) → ℤ),
        (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
          ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e)
    (x : ↥(ssPlaces q' M K) → ℤ) (e : ↥(ssPlaces q' (M * s) K)) :
    padj 0 x e = (Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) e.1 : ℤ) * x (X.degeneracyData.a e) ∧
    padj 1 x e = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 : ℤ) * x (X.degeneracyData.b e) := by
  have hpos := pw_pos (K := K) hq5 (M * s) hq'Ms e.1 e.2
  obtain ⟨hra, hrb⟩ := ram_mul_pw X hs hq5 hsq' hq'M hq'Ms e
  have hposa := pw_pos (K := K) hq5 M hq'M (X.degeneracyData.a e).1 (X.degeneracyData.a e).2
  have hposb := pw_pos (K := K) hq5 M hq'M (X.degeneracyData.b e).1 (X.degeneracyData.b e).2
  have hw : ((X.degeneracyData.w e : ℕ) : ℤ) = (placeWidth (M * s) e.1 : ℤ) := by
    show (((Nat.toPNat' (placeWidth (M * s) e.1)) : ℕ) : ℤ) = _
    rw [PNat.toPNat'_coe hpos]
  have hne : (placeWidth (M * s) e.1 : ℤ) ≠ 0 := by exact_mod_cast hpos.ne'
  have h0 := padj_entry X padj hadj 0 x e
  have h1 := padj_entry X padj hadj 1 x e
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1
  rw [hw, PNat.toPNat'_coe hposa] at h0
  rw [hw, PNat.toPNat'_coe hposb] at h1
  refine ⟨mul_left_cancel₀ hne ?_, mul_left_cancel₀ hne ?_⟩
  · rw [h0, ← mul_assoc]
    congr 1
    exact_mod_cast hra.symm.trans (mul_comm _ _)
  · rw [h1, ← mul_assoc]
    congr 1
    exact_mod_cast hrb.symm.trans (mul_comm _ _)

theorem ram_perm [IsAlgClosed K] (hs : s.Prime) (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M)
    (hq'Ms : ¬ q' ∣ M * s)
    (hb1 : ∀ W : ↥(ssPlaces q' (M * s) K), X.fst (X.atkinLehnerPerm W) = X.snd W)
    (hb4 : ∀ W : ↥(ssPlaces q' (M * s) K), X.degeneracyData.w (X.atkinLehnerPerm W) = X.degeneracyData.w W)
    (e : ↥(ssPlaces q' (M * s) K)) :
    Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) (X.atkinLehnerPerm e).1 =
      Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 := by
  have hpos := pw_pos (K := K) hq5 (M * s) hq'Ms e.1 e.2
  have hpos' := pw_pos (K := K) hq5 (M * s) hq'Ms (X.atkinLehnerPerm e).1 (X.atkinLehnerPerm e).2
  obtain ⟨hra, -⟩ := ram_mul_pw X hs hq5 hsq' hq'M hq'Ms (X.atkinLehnerPerm e)
  obtain ⟨-, hrb⟩ := ram_mul_pw X hs hq5 hsq' hq'M hq'Ms e
  have hw : placeWidth (M * s) (X.atkinLehnerPerm e).1 = placeWidth (M * s) e.1 := by
    have h := congrArg (fun n : ℕ+ => (n : ℕ)) (hb4 e)
    change ((Nat.toPNat' (placeWidth (M * s) (X.atkinLehnerPerm e).1) : ℕ)) =
      ((Nat.toPNat' (placeWidth (M * s) e.1) : ℕ)) at h
    rwa [PNat.toPNat'_coe hpos, PNat.toPNat'_coe hpos'] at h
  have hab : (X.degeneracyData.a (X.atkinLehnerPerm e)) = X.degeneracyData.b e := hb1 e
  rw [hw, hab, ← hrb] at hra
  exact Nat.eq_of_mul_eq_mul_right hpos hra

theorem U_entry [IsAlgClosed K] (hs : s.Prime) (hsq' : s ≠ q') (hsM : ¬ s ∣ M) (hq'Ms : ¬ q' ∣ M * s)
    (e x : ↥(ssPlaces q' (M * s) K)) :
    X.edgeHecke ⟨s, hs⟩ e x =
      (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 : ℤ) *
          (if X.degeneracyData.b e = X.degeneracyData.a x then 1 else 0) -
        (if X.atkinLehnerPerm x = e then 1 else 0) := by
  haveI : Fact s.Prime := ⟨hs⟩
  have hMsK : ((M * s : ℕ) : K) ≠ 0 := fun h => hq'Ms ((CharP.cast_eq_zero_iff K q' (M * s)).1 h)
  have hsK : ((s : ℕ) : K) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff K q' s).1 h
    exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hs).1 this).symm
  haveI instRoof : HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s) :=
    ModularCurve.hasPrincipalDivisors_charLDegeneracyRoof K (M * s) s hMsK hsK
  haveI instFMs : HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s)) :=
    ModularCurve.hasPrincipalDivisors_modularFunctionFieldC_of_perfectField K (M * s)
  haveI : NeZero (((⟨s, hs⟩ : Nat.Primes) : ℕ)) := ⟨hs.ne_zero⟩
  have hK1 := K1.edgeHecke_apply_of_ne X ⟨s, hs⟩ hsq' e x
  have hea := ModularCurve.correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
    M s hs hsM (k := K) q' hq'Ms X.mem_M X.mem_s X.atkinLehnerAut X.isAtkinLehner
    (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2 X.fstIntegral X.sndIntegral x.1
  have hea' := DFunLike.congr_fun hea e.1
  classical
  rw [Finsupp.add_apply, Divisor.pushforwardAlong_single, inertia_one X x, Nat.cast_one, one_mul,
    Divisor.pullbackAlong_apply, Finsupp.single_apply, Finsupp.single_apply] at hea'
  rw [hK1, eq_sub_iff_add_eq]
  calc Divisor.correspondence (heckeBetaC K (M * s) s) (heckeAlphaC K (M * s) s)
          (X.legsIntegral (M * s) s).2 (X.legsIntegral (M * s) s).1 (Finsupp.single x.1 1) e.1 +
          (if X.atkinLehnerPerm x = e then 1 else 0)
        = Divisor.correspondence (heckeBetaC K (M * s) s) (heckeAlphaC K (M * s) s)
          (X.legsIntegral (M * s) s).2 (X.legsIntegral (M * s) s).1 (Finsupp.single x.1 1) e.1 +
          (if autOnPlaces K M s X.atkinLehnerAut x.1 = e.1 then 1 else 0) := by
            congr 1
            exact if_congr (Subtype.ext_iff (a1 := X.atkinLehnerPerm x) (a2 := e)) rfl rfl
    _ = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 : ℤ) *
          (if Place.restrictAlong (levelAlphaC K M s X.mem_M) X.fstIntegral x.1 =
              Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral e.1 then 1 else 0) := hea'
    _ = (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 : ℤ) *
          (if X.degeneracyData.b e = X.degeneracyData.a x then 1 else 0) := by
            congr 1
            exact if_congr ((Subtype.ext_iff (a1 := X.degeneracyData.a x)
              (a2 := X.degeneracyData.b e)).symm.trans eq_comm) rfl rfl

theorem core [IsAlgClosed K] (hs : s.Prime) (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (padj : Fin 2 → ((↥(ssPlaces q' M K) → ℤ) →ₗ[ℤ] (↥(ssPlaces q' (M * s) K) → ℤ)))
    (hadj : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M K) → ℤ) (y : ↥(ssPlaces q' (M * s) K) → ℤ),
        (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
          ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e)
    (h1 : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M K) → ℤ),
        (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec (padj i x) =
          (((s : ℕ) : ℤ) + 1) • x)
    (h2 : ∀ x : ↥(ssPlaces q' M K) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec (padj 1 x) = (X.vertexHecke ⟨s, hs⟩).mulVec x)
    (hb1 : ∀ W : ↥(ssPlaces q' (M * s) K), X.fst (X.atkinLehnerPerm W) = X.snd W)
    (hb2 : ∀ W : ↥(ssPlaces q' (M * s) K), X.snd (X.atkinLehnerPerm W) = X.fst W)
    (hb3 : ∀ W : ↥(ssPlaces q' (M * s) K), X.atkinLehnerPerm (X.atkinLehnerPerm W) = W)
    (hb4 : ∀ W : ↥(ssPlaces q' (M * s) K), X.degeneracyData.w (X.atkinLehnerPerm W) = X.degeneracyData.w W) :
    (∀ x : ↥(ssPlaces q' M K) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec (padj 0 x) = (X.vertexHecke ⟨s, hs⟩).mulVec x) ∧
    (∀ y : ↥(ssPlaces q' (M * s) K) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          (X.vertexHecke ⟨s, hs⟩).mulVec ((CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) -
            (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec y) ∧
    (∀ y : ↥(ssPlaces q' (M * s) K) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          ((s : ℕ) : ℤ) • (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) := by
  have hq'Ms : ¬ q' ∣ M * s := by
    intro h
    rcases (Nat.Prime.dvd_mul (Fact.out : q'.Prime)).1 h with h | h
    · exact hq'M h
    · exact hsq' ((Nat.prime_dvd_prime_iff_eq (Fact.out : q'.Prime) hs).1 h).symm

  set a := X.degeneracyData.a with ha_def
  set b := X.degeneracyData.b with hb_def
  set π := X.atkinLehnerPerm with hπ_def
  set U := X.edgeHecke ⟨s, hs⟩ with hU_def
  set T := X.vertexHecke ⟨s, hs⟩ with hT_def
  set rA : ↥(ssPlaces q' (M * s) K) → ℤ := fun e => (Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) e.1 : ℤ) with hrA_def
  set rB : ↥(ssPlaces q' (M * s) K) → ℤ := fun e => (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 : ℤ) with hrB_def
  have hpA : ∀ (x : ↥(ssPlaces q' M K) → ℤ) (e : ↥(ssPlaces q' (M * s) K)), padj 0 x e = rA e * x (a e) := fun x e =>
    (padj_explicit X hs hq5 hsq' hq'M hq'Ms padj hadj x e).1
  have hpB : ∀ (x : ↥(ssPlaces q' M K) → ℤ) (e : ↥(ssPlaces q' (M * s) K)), padj 1 x e = rB e * x (b e) := fun x e =>
    (padj_explicit X hs hq5 hsq' hq'M hq'Ms padj hadj x e).2
  have hrperm : ∀ e : ↥(ssPlaces q' (M * s) K), rA (π e) = rB e := fun e => by
    simp only [hrA_def, hrB_def]
    exact_mod_cast ram_perm X hs hq5 hsq' hq'M hq'Ms hb1 hb4 e
  have hUe : ∀ e x : ↥(ssPlaces q' (M * s) K), U e x = rB e * (if b e = a x then 1 else 0) - (if π x = e then 1 else 0) :=
    fun e x => U_entry X hs hsq' hsM hq'Ms e x
  have ha1 : ∀ W : ↥(ssPlaces q' (M * s) K), a (π W) = b W := hb1
  have ha2 : ∀ W : ↥(ssPlaces q' (M * s) K), b (π W) = a W := hb2

  have hA : ∀ (f : ↥(ssPlaces q' (M * s) K) → ↥(ssPlaces q' M K)) (v : ↥(ssPlaces q' M K)) (e : ↥(ssPlaces q' (M * s) K)),
      CerednikDrinfeld.degeneracyMatrix f v e = if f e = v then 1 else 0 := fun f v e => rfl

  have hmv : ∀ (f : ↥(ssPlaces q' (M * s) K) → ↥(ssPlaces q' M K)) (z : ↥(ssPlaces q' (M * s) K) → ℤ) (v : ↥(ssPlaces q' M K)),
      (CerednikDrinfeld.degeneracyMatrix f).mulVec z v = ∑ e, (if f e = v then 1 else 0) * z e := by
    intro f z v
    rfl

  have hT : ∀ (v x' : ↥(ssPlaces q' M K)), T v x' = ∑ e, (if a e = v then 1 else 0) * (rB e * (if b e = x' then 1 else 0)) := by
    intro v x'
    have h := congrFun (h2 (Pi.single x' 1)) v
    rw [Matrix.mulVec_single_one] at h
    change _ = T v x' at h
    rw [← h, hmv]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hpB, Pi.single_apply]

  have hdeg : ∀ (v x' : ↥(ssPlaces q' M K)),
      ∑ e, (if b e = v then 1 else 0) * (rB e * (if b e = x' then 1 else 0)) =
        (((s : ℕ) : ℤ) + 1) * (if v = x' then 1 else 0) := by
    intro v x'
    have h := congrFun (h1 1 (Pi.single x' 1)) v
    simp only [Matrix.cons_val_one] at h
    rw [Pi.smul_apply, smul_eq_mul, Pi.single_apply] at h
    change (CerednikDrinfeld.degeneracyMatrix b).mulVec (padj 1 (Pi.single x' 1)) v = _ at h
    rw [hmv] at h
    rw [← h]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hpB, Pi.single_apply]
  refine ⟨?_, ?_, ?_⟩
  ·
    intro x
    rw [← h2 x]
    funext v
    change (CerednikDrinfeld.degeneracyMatrix b).mulVec (padj 0 x) v =
      (CerednikDrinfeld.degeneracyMatrix a).mulVec (padj 1 x) v
    rw [hmv, hmv]
    refine (Fintype.sum_equiv (Function.Involutive.toPerm π hb3) _ _ fun e => ?_).symm
    change (if a e = v then 1 else 0) * padj 1 x e = (if b (π e) = v then 1 else 0) * padj 0 x (π e)
    rw [hpA, hpB, ha2, ha1, hrperm]
  ·
    intro y
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.sub_mulVec]
    congr 1
    ext v x
    rw [Matrix.mul_apply, Matrix.sub_apply, Matrix.mul_apply]
    change ∑ e, (if a e = v then 1 else 0) * U e x = ∑ v', T v v' * (if a x = v' then 1 else 0) - (if b x = v then 1 else 0)
    have hR : ∑ v', T v v' * (if a x = v' then 1 else 0) = T v (a x) := by
      simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (a x) (fun v' => T v v')]
      simp
    rw [hR, hT]
    simp_rw [hUe, mul_sub, Finset.sum_sub_distrib]
    congr 1

    rw [show (∑ e, (if a e = v then (1 : ℤ) else 0) * (if π x = e then 1 else 0)) =
        if a (π x) = v then 1 else 0 from ?_]
    · rw [ha1]
    · simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (π x)]
      simp
  ·
    intro y
    rw [Matrix.mulVec_mulVec, ← Matrix.smul_mulVec]
    congr 1
    ext v x
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
    change ∑ e, (if b e = v then 1 else 0) * U e x = ((s : ℕ) : ℤ) * (if a x = v then 1 else 0)
    simp_rw [hUe, mul_sub, Finset.sum_sub_distrib]
    rw [hdeg v (a x)]
    rw [show (∑ e, (if b e = v then (1 : ℤ) else 0) * (if π x = e then 1 else 0)) =
        if b (π x) = v then 1 else 0 from ?_]
    · rw [ha2]
      by_cases h : a x = v
      · rw [if_pos h, if_pos h.symm]; ring
      · rw [if_neg h, if_neg (Ne.symm h)]; ring
    · simp only [mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq Finset.univ (π x)]
      simp

end Generic

end C3Reduce

theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s)
    (padj : Fin 2 → ((↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ) →ₗ[ℤ]
      (↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ)))
    (hadj : ∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ)
        (y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ),
        (∑ v, (Nat.toPNat' (placeWidth M v.1) : ℤ) *
            (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec y v * x v) =
          ∑ e, (X.degeneracyData.w e : ℤ) * y e * padj i x e) :
    (∀ (i : Fin 2) (x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ),
        (CerednikDrinfeld.degeneracyMatrix (![X.degeneracyData.a, X.degeneracyData.b] i)).mulVec (padj i x) =
          (((s : ℕ) : ℤ) + 1) • x) ∧
    (∀ x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec (padj 1 x) =
          (X.vertexHecke ⟨s, hs⟩).mulVec x) ∧
    (∀ x : ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec (padj 0 x) =
          (X.vertexHecke ⟨s, hs⟩).mulVec x) ∧
    (∀ y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          (X.vertexHecke ⟨s, hs⟩).mulVec ((CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) -
            (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec y) ∧
    (∀ y : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)) → ℤ,
        (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.b).mulVec ((X.edgeHecke ⟨s, hs⟩).mulVec y) =
          ((s : ℕ) : ℤ) • (CerednikDrinfeld.degeneracyMatrix X.degeneracyData.a).mulVec y) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  obtain ⟨h1, h2⟩ :=
    ModularCurve.SSLevelDatum.degeneracyMatrix_mulVec_padj_eq_smul_and_eq_vertexHecke_mulVec
      M s q' hs hq5 hsq' hq'M hsM A X padj hadj
  obtain ⟨hb1, hb2, hb3, hb4, -⟩ :=
    ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
      M s q' hs hq5 hsq' hq'M hsM A X
  obtain ⟨h3, h4, h5⟩ := C3Reduce.core X hs hq5 hsq' hq'M hsM padj hadj h1 h2 hb1 hb2 hb3 hb4
  exact ⟨h1, h2, h3, h4, h5⟩

end S_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_degeneracyMatrix_mulVec_padj_and_edgeHecke_companion_laws (solution)
