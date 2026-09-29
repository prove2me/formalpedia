-- Prove2me | solution 1 for ModularCurve.SSLevelDatum.atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.002793+00:00
-- url     : https://prove2.me/submissions/fbaf75a4-fd6d-5efa-8f70-918b19007109

import Mathlib
import Definitions.Def_ModularCurve_SSDegeneracyHecke
import Theorems.Thm_ModularCurve_SSLevelDatum_degeneracyData_b_eq_a_atkinLehnerPerm
import Theorems.Thm_ModularCurve_correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong
import Theorems.Thm_ModularCurve_ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_charLDegeneracyRoof
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldC_of_perfectField
import Theorems.Thm_AlgebraicCurve_Place_inertiaDeg_eq_one_of_isRational
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions WeierstrassCurve.Affine.Point.instFinite GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions"
p2m_attr_erase "instance" "AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply"
p2m_attr_erase "simp" "AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.qExpandAlgHomC_apply ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.cuspCount_one HahnSeries.ramScale_apply AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq PowerSeries.coeff_heckeV PowerSeries.coeff_heckeU LaurentSeries.coeff_heckeV LaurentSeries.coeff_heckeU FreyPackage.ModMCarrier.coe_rescaleLin_apply ModularForm.AtkinLehnerDatum.mk.injEq"
p2m_attr_erase "simp" "ModularForm.AtkinLehnerDatum.alGL_coe ModularForm.AtkinLehnerDatum.mk.sizeOf_spec ModularForm.AtkinLehnerDatum.sqUnitSL_coe ModularForm.AtkinLehnerDatum.det_sqUnit ModularForm.AtkinLehnerDatum.det_mat ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.ProjectiveLine.map_mk AlgebraicCurve.ConstantReduction.toRegularProlongation_residue AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe"
p2m_attr_erase "simp" "AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁"
p2m_attr_erase "simp" "PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe"
p2m_attr_erase "simp" "ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero"
p2m_attr_erase "simp" "TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open AlgebraicCurve ModularCurve

namespace C3bis

section PlaceCalculus

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

theorem restrictAlong_congrEquiv (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (σ : F' ≃ₐ[K] F')
    (hσφ : (σ.symm.toAlgHom.comp φ).toRingHom.IsIntegral) (w : Place K F') :
    Place.restrictAlong φ hφ (Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c) w) =
      Place.restrictAlong (σ.symm.toAlgHom.comp φ) hσφ w := by
  apply Place.ext
  ext f
  exact Iff.rfl

theorem ord_congrEquiv_symm (σ : F' ≃ₐ[K] F') (w : Place K F') (g : F') :
    (Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c) w).ord g = w.ord (σ.symm g) := by
  have h := Place.ord_congrRingEquiv σ.toRingEquiv (fun c => σ.commutes c) w (σ.symm g)
  rw [Place.congrEquiv_apply]
  have e : σ.toRingEquiv (σ.symm g) = g := σ.apply_symm_apply g
  rw [e] at h
  exact h

theorem ramificationIndexAlong_congrEquiv (φ : F →ₐ[K] F') (σ : F' ≃ₐ[K] F') (w : Place K F') :
    Place.ramificationIndexAlong φ (Place.congrEquiv σ.toRingEquiv (fun c => σ.commutes c) w) =
      Place.ramificationIndexAlong (σ.symm.toAlgHom.comp φ) w := by
  unfold Place.ramificationIndexAlong Place.ramificationIndex
  simp only [AlgHom.toRingHom_eq_coe, RingHom.algebraMap_toAlgebra, RingHom.coe_coe, AlgHom.coe_comp,
    Function.comp_apply, ord_congrEquiv_symm]
  rfl

theorem ramificationIndexAlong_congr {φ φ' : F →ₐ[K] F'} (h : φ = φ') (w : Place K F') :
    Place.ramificationIndexAlong φ w = Place.ramificationIndexAlong φ' w := by
  subst h
  rfl

theorem ramificationIndexAlong_pos (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F') :
    0 < Place.ramificationIndexAlong φ w := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.ramificationIndex_pos (F := F) w

theorem inertiaDegAlong_eq_one_of_isRational (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (w : Place K F')
    (hw : w.IsRational) (hv : (w.restrictAlong φ hφ).IsRational) : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  exact Place.inertiaDeg_eq_one_of_isRational w hw hv

end PlaceCalculus

section Datum

variable {p : ℕ} [Fact p.Prime] {K : Type} [Field K] [CharP K p] [DecidableEq K] {M s : ℕ} [NeZero M] [NeZero s]
  (X : SSLevelDatum p K M s)

theorem atkinLehnerAut_symm_comp_levelAlphaC :
    X.atkinLehnerAut.symm.toAlgHom.comp (levelAlphaC K M s X.mem_M) = levelBetaC K M s X.mem_s := by
  obtain ⟨h1, h2, h3, h4⟩ := X.isAtkinLehner
  refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ({jqModC K, jqNModC K M} : Set (LaurentSeries K))) rfl ?_
  intro x hx
  rcases hx with rfl | hx
  · have e1 : levelAlphaC K M s X.mem_M ⟨jqModC K, jqModC_mem K M⟩ = jGeomGen K (M * s) :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    apply Subtype.ext
    change ((X.atkinLehnerAut.symm (levelAlphaC K M s X.mem_M ⟨jqModC K, _⟩) : modularFunctionFieldC K (M * s)) :
        LaurentSeries K) =
      ((levelBetaC K M s X.mem_s ⟨jqModC K, _⟩ : modularFunctionFieldC K (M * s)) : LaurentSeries K)
    rw [coe_levelBetaC, e1, ← h2, AlgEquiv.symm_apply_apply]
    rfl
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have e1 : levelAlphaC K M s X.mem_M ⟨jqNModC K M, jqNModC_mem K M⟩ = ⟨jqNModC K M, X.mem_M⟩ :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    apply Subtype.ext
    change ((X.atkinLehnerAut.symm (levelAlphaC K M s X.mem_M ⟨jqNModC K M, _⟩) : modularFunctionFieldC K (M * s)) :
        LaurentSeries K) =
      ((levelBetaC K M s X.mem_s ⟨jqNModC K M, _⟩ : modularFunctionFieldC K (M * s)) : LaurentSeries K)
    rw [coe_levelBetaC, e1, ← h3, AlgEquiv.symm_apply_apply]
    show jqNModC K (M * s) = qExpand K s (jqNModC K M)
    unfold jqNModC
    rw [qExpand_qExpand]
    simp only [Nat.mul_comm s M]

theorem atkinLehnerAut_symm_comp_levelBetaC :
    X.atkinLehnerAut.symm.toAlgHom.comp (levelBetaC K M s X.mem_s) = levelAlphaC K M s X.mem_M := by
  obtain ⟨h1, h2, h3, h4⟩ := X.isAtkinLehner
  refine IntermediateField.algHom_ext_of_eq_adjoin K (s := ({jqModC K, jqNModC K M} : Set (LaurentSeries K))) rfl ?_
  intro x hx
  rcases hx with rfl | hx
  · have e1 : levelBetaC K M s X.mem_s ⟨jqModC K, jqModC_mem K M⟩ = ⟨jqNModC K s, X.mem_s⟩ :=
      Subtype.ext (coe_levelBetaC K M s X.mem_s _)
    have e2 : levelAlphaC K M s X.mem_M ⟨jqModC K, jqModC_mem K M⟩ = jGeomGen K (M * s) :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    change X.atkinLehnerAut.symm (levelBetaC K M s X.mem_s ⟨jqModC K, _⟩) = levelAlphaC K M s X.mem_M ⟨jqModC K, _⟩
    rw [e1, e2, ← h1, AlgEquiv.symm_apply_apply]
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    have e1 : levelBetaC K M s X.mem_s ⟨jqNModC K M, jqNModC_mem K M⟩ = jNGeomGen K (M * s) := by
      apply Subtype.ext
      rw [coe_levelBetaC]
      show qExpand K s (jqNModC K M) = jqNModC K (M * s)
      unfold jqNModC
      rw [qExpand_qExpand]
      simp only [Nat.mul_comm s M]
    have e2 : levelAlphaC K M s X.mem_M ⟨jqNModC K M, jqNModC_mem K M⟩ = ⟨jqNModC K M, X.mem_M⟩ :=
      Subtype.ext (coe_levelAlphaC K M s X.mem_M _)
    change X.atkinLehnerAut.symm (levelBetaC K M s X.mem_s ⟨jqNModC K M, _⟩) = levelAlphaC K M s X.mem_M ⟨jqNModC K M, _⟩
    rw [e1, e2, ← h4, AlgEquiv.symm_apply_apply]

theorem eq_top_of_inv_mem_of_generators (Z : IntermediateField K (LaurentSeries K)) (A : Subalgebra K Z)
    (hinv : ∀ a ∈ A, a⁻¹ ∈ A) (S₀ : Set (LaurentSeries K)) (hZ : Z ≤ IntermediateField.adjoin K S₀)
    (hS₀ : ∀ t ∈ S₀, ∃ a ∈ A, (a : LaurentSeries K) = t) : A = ⊤ := by
  let E : IntermediateField K Z := A.toIntermediateField hinv
  have hmap : IntermediateField.adjoin K S₀ ≤ E.map Z.val := by
    refine IntermediateField.adjoin_le_iff.mpr ?_
    intro t ht
    obtain ⟨a, ha, rfl⟩ := hS₀ t ht
    exact ⟨a, ha, rfl⟩
  have hE : E = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    obtain ⟨e, he, hez⟩ := hmap (hZ z.2)
    exact (Subtype.ext hez : e = z) ▸ he
  have := congrArg IntermediateField.toSubalgebra hE
  simpa [E] using this

theorem atkinLehnerAut_atkinLehnerAut (x : ↥(modularFunctionFieldC K (M * s))) :
    X.atkinLehnerAut (X.atkinLehnerAut x) = x := by
  obtain ⟨h1, h2, h3, h4⟩ := X.isAtkinLehner
  let A : Subalgebra K ↥(modularFunctionFieldC K (M * s)) :=
    AlgHom.equalizer
      ((X.atkinLehnerAut : ↥(modularFunctionFieldC K (M * s)) →ₐ[K] ↥(modularFunctionFieldC K (M * s))).comp
        X.atkinLehnerAut)
      (AlgHom.id K _)
  have hmem : ∀ y, y ∈ A ↔ X.atkinLehnerAut (X.atkinLehnerAut y) = y := fun y => Iff.rfl
  have hinv : ∀ a ∈ A, a⁻¹ ∈ A := fun a ha => by
    rw [hmem] at ha ⊢
    rw [map_inv₀, map_inv₀, ha]
  have hA : A = ⊤ := by
    refine eq_top_of_inv_mem_of_generators (modularFunctionFieldC K (M * s)) A hinv
      {jqModC K, jqNModC K (M * s)} le_rfl ?_
    intro t ht
    rcases ht with rfl | ht
    · refine ⟨jGeomGen K (M * s), ?_, coe_jGeomGen K (M * s)⟩
      rw [hmem, h1, h2]
    · rw [Set.mem_singleton_iff] at ht
      subst ht
      refine ⟨jNGeomGen K (M * s), ?_, coe_jNGeomGen K (M * s)⟩
      rw [hmem, h3, h4]
  have hx : x ∈ A := hA ▸ Algebra.mem_top
  exact (hmem x).mp hx

theorem atkinLehnerPerm_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) : X.atkinLehnerPerm (X.atkinLehnerPerm e) = e := by
  refine Subtype.ext ?_
  show autOnPlaces K M s X.atkinLehnerAut (autOnPlaces K M s X.atkinLehnerAut e.1) = e.1
  have hsymm : ∀ y, X.atkinLehnerAut.toRingEquiv.symm y = X.atkinLehnerAut y := fun y => by
    conv_lhs => rw [← atkinLehnerAut_atkinLehnerAut (X := X) y]
    exact X.atkinLehnerAut.toRingEquiv.symm_apply_apply _
  ext1
  refine SetLike.ext fun y => ?_
  simp only [autOnPlaces, Place.congrEquiv_apply, Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
  show X.atkinLehnerAut.toRingEquiv.symm (X.atkinLehnerAut.toRingEquiv.symm y) ∈ _ ↔ _
  rw [hsymm, hsymm, atkinLehnerAut_atkinLehnerAut]

theorem fst_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) : X.fst (X.atkinLehnerPerm e) = X.snd e :=
  (SSLevelDatum.degeneracyData_b_eq_a_atkinLehnerPerm p K M s X e).symm

theorem snd_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) : X.snd (X.atkinLehnerPerm e) = X.fst e := by
  rw [← fst_atkinLehnerPerm, atkinLehnerPerm_atkinLehnerPerm]

theorem ramificationIndexAlong_levelAlphaC_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) :
    Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) (X.atkinLehnerPerm e).1 =
      Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) e.1 := by
  show Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) (autOnPlaces K M s X.atkinLehnerAut e.1) = _
  rw [autOnPlaces, ramificationIndexAlong_congrEquiv,
    ramificationIndexAlong_congr (atkinLehnerAut_symm_comp_levelAlphaC X)]

theorem ramificationIndexAlong_levelBetaC_atkinLehnerPerm (e : ↥(ssPlaces p (M * s) K)) :
    Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) (X.atkinLehnerPerm e).1 =
      Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) e.1 := by
  show Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) (autOnPlaces K M s X.atkinLehnerAut e.1) = _
  rw [autOnPlaces, ramificationIndexAlong_congrEquiv,
    ramificationIndexAlong_congr (atkinLehnerAut_symm_comp_levelBetaC X)]

theorem natCast_ne_zero_of_prime_ne {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : (ℓ : K) ≠ 0 := fun h =>
  hℓp (((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) hℓ).mp ((CharP.cast_eq_zero_iff K p ℓ).mp h)).symm)

theorem natCast_ne_zero_of_not_dvd {n : ℕ} (hn : ¬ p ∣ n) : (n : K) ≠ 0 := fun h =>
  hn ((CharP.cast_eq_zero_iff K p n).mp h)

theorem not_dvd_mul (hs : s.Prime) (hpM : ¬ p ∣ M) (hsp : s ≠ p) : ¬ p ∣ M * s := by
  have hp : p.Prime := Fact.out
  intro h
  rcases hp.dvd_mul.mp h with h | h
  · exact hpM h
  · exact hsp ((Nat.prime_dvd_prime_iff_eq hp hs).mp h).symm

theorem hasPrincipalDivisors_roof (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M) :
    HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s) :=
  haveI : Fact s.Prime := ⟨hs⟩
  hasPrincipalDivisors_charLDegeneracyRoof K (M * s) s (natCast_ne_zero_of_not_dvd (not_dvd_mul hs hpM hsp))
    (natCast_ne_zero_of_prime_ne hs hsp)

theorem edgeHecke_apply (hs : s.Prime) (hsp : s ≠ p) [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s)]
    (y x : ↥(ssPlaces p (M * s) K)) :
    X.edgeHecke ⟨s, hs⟩ y x =
      Divisor.correspondence (heckeBetaC K (M * s) s) (heckeAlphaC K (M * s) s)
        (X.legsIntegral (M * s) s).2 (X.legsIntegral (M * s) s).1 (Finsupp.single x.1 1) y.1 := by
  classical
  have hne : ((⟨s, hs⟩ : Nat.Primes) : ℕ) ≠ p := hsp
  unfold SSLevelDatum.edgeHecke ssHeckeFamilyC
  rw [if_neg hne]
  unfold ssHeckeMatrixC
  rw [Matrix.of_apply, Divisor.correspondence_apply, Divisor.pullbackAlong_single, map_sum, Finsupp.finsetSum_apply]
  show (∑ᶠ W : Place K (charLDegeneracyRoof K (M * s) s), _) = _
  rw [finsum_eq_sum_of_support_subset _
    (s := Place.fiberAlong (heckeBetaC K (M * s) s) (X.legsIntegral (M * s) s).2 x.1) ?_]
  · refine Finset.sum_congr rfl fun W hW => ?_
    rw [Place.mem_fiberAlong] at hW
    rw [Divisor.pushforwardAlong_single, Finsupp.single_apply, one_mul]
    by_cases hy : Place.restrictAlong (heckeAlphaC K (M * s) s) (X.legsIntegral (M * s) s).1 W = y.1
    · rw [if_pos ⟨hW, hy⟩, if_pos hy]
    · rw [if_neg (fun h => hy h.2), if_neg hy]
  · intro W hW
    rw [Function.mem_support] at hW
    rw [Finset.mem_coe, Place.mem_fiberAlong]
    by_contra hx
    exact hW (if_neg fun h => hx h.1)

theorem edgeHecke_entry [DecidableEq ↥(ssPlaces p (M * s) K)] [DecidableEq ↥(ssPlaces p M K)] (hs : s.Prime) (hsp : s ≠ p) (hpM : ¬ p ∣ M)
    (hsM : ¬ s ∣ M) [HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s)]
    [HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s))] (y x : ↥(ssPlaces p (M * s) K)) :
    X.edgeHecke ⟨s, hs⟩ y x =
      (Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) y.1 : ℤ) * (if X.snd y = X.fst x then 1 else 0)
        - (if X.atkinLehnerPerm x = y then 1 else 0) := by
  classical
  have h := correspondence_heckeBetaC_heckeAlphaC_single_add_single_autOnPlaces_eq_pullbackAlong_pushforwardAlong M s
    hs hsM (k := K) p (not_dvd_mul hs hpM hsp) X.mem_M X.mem_s X.atkinLehnerAut X.isAtkinLehner
    (X.legsIntegral (M * s) s).1 (X.legsIntegral (M * s) s).2 X.fstIntegral X.sndIntegral x.1
  have hpush : Divisor.pushforwardAlong (levelAlphaC K M s X.mem_M) X.fstIntegral (Finsupp.single x.1 1)
      = Finsupp.single (X.fst x).1 1 := by
    rw [Divisor.pushforwardAlong_single, one_mul,
      inertiaDegAlong_eq_one_of_isRational _ _ x.1 x.2.1 (X.fst x).2.1]
    rfl
  rw [hpush] at h
  have h' := congrArg (fun D => D y.1) h
  simp only [Finsupp.add_apply, Divisor.pullbackAlong_apply] at h'
  have hS : Finsupp.single (autOnPlaces K M s X.atkinLehnerAut x.1) (1 : ℤ) y.1
      = if X.atkinLehnerPerm x = y then 1 else 0 := by
    rw [Finsupp.single_apply]
    by_cases hπ : X.atkinLehnerPerm x = y
    · rw [if_pos hπ, if_pos]
      exact congrArg Subtype.val hπ
    · rw [if_neg hπ, if_neg]
      exact fun h'' => hπ (Subtype.ext h'')
  have hA : Finsupp.single (X.fst x).1 (1 : ℤ) (Place.restrictAlong (levelBetaC K M s X.mem_s) X.sndIntegral y.1)
      = if X.snd y = X.fst x then 1 else 0 := by
    rw [Finsupp.single_apply]
    by_cases hab : X.snd y = X.fst x
    · rw [if_pos hab, if_pos]
      exact (congrArg Subtype.val hab).symm
    · rw [if_neg hab, if_neg]
      exact fun h'' => hab (Subtype.ext h''.symm)
  rw [hS, hA, ← edgeHecke_apply X hs hsp y x] at h'
  linear_combination h'

def levelPair : Fin 2 → (↥(modularFunctionFieldC K M) →ₐ[K] ↥(modularFunctionFieldC K (M * s))) :=
  ![levelAlphaC K M s X.mem_M, levelBetaC K M s X.mem_s]

theorem levelPair_integral : ∀ i, (levelPair X i).toRingHom.IsIntegral := by
  intro i
  fin_cases i
  · exact X.fstIntegral
  · exact X.sndIntegral

section Closed

variable [IsAlgClosed K]

theorem dvd_of_mem (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) :
    placeRamificationJ (M * s) W.1 ∣ jWidth (W.1.evalAt (jGeomGen K (M * s))) :=
  placeRamificationJ_dvd_jWidth_of_mem_ssPlaces (q := p) hp5 (not_dvd_mul hs hpM hsp) W.2

theorem ram_mul_placeWidth_fst (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) :
    Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) W.1 * placeWidth (M * s) W.1
      = placeWidth M (X.fst W).1 :=
  ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le M s p hs hp5 hsp hpM
    (levelPair X) (levelPair_integral X) (fun x => coe_levelAlphaC K M s X.mem_M x) (fun x => coe_levelBetaC K M s X.mem_s x)
    0 W.1 (dvd_of_mem hs hp5 hsp hpM W)

theorem ram_mul_placeWidth_snd (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) :
    Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) W.1 * placeWidth (M * s) W.1
      = placeWidth M (X.snd W).1 :=
  ramificationIndexAlong_mul_placeWidth_eq_placeWidth_restrictAlong_of_five_le M s p hs hp5 hsp hpM
    (levelPair X) (levelPair_integral X) (fun x => coe_levelAlphaC K M s X.mem_M x) (fun x => coe_levelBetaC K M s X.mem_s x)
    1 W.1 (dvd_of_mem hs hp5 hsp hpM W)

theorem placeWidth_atkinLehnerPerm (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) :
    placeWidth (M * s) (X.atkinLehnerPerm W).1 = placeWidth (M * s) W.1 := by
  have h1 := ram_mul_placeWidth_fst X hs hp5 hsp hpM (X.atkinLehnerPerm W)
  rw [fst_atkinLehnerPerm, ← ram_mul_placeWidth_snd X hs hp5 hsp hpM W,
    ramificationIndexAlong_levelAlphaC_atkinLehnerPerm] at h1
  exact Nat.eq_of_mul_eq_mul_left (ramificationIndexAlong_pos _ X.sndIntegral W.1) h1

theorem placeWidth_pos (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) : 0 < placeWidth (M * s) W.1 := by
  have hd := dvd_of_mem hs hp5 hsp hpM W
  have hj := jWidth_pos (W.1.evalAt (jGeomGen K (M * s)))
  have hr : placeRamificationJ (M * s) W.1 ≠ 0 := by
    intro h0
    rw [h0] at hd
    exact hj.ne' (Nat.eq_zero_of_zero_dvd hd)
  exact Nat.div_pos (Nat.le_of_dvd hj hd) (Nat.pos_of_ne_zero hr)

theorem coe_w (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) : ((X.degeneracyData.w W : ℕ+) : ℕ) = placeWidth (M * s) W.1 :=
  PNat.toPNat'_coe (placeWidth_pos hs hp5 hsp hpM W)

theorem w_atkinLehnerPerm (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (W : ↥(ssPlaces p (M * s) K)) :
    X.degeneracyData.w (X.atkinLehnerPerm W) = X.degeneracyData.w W := by
  show Nat.toPNat' (placeWidth (M * s) (X.atkinLehnerPerm W).1) = Nat.toPNat' (placeWidth (M * s) W.1)
  rw [placeWidth_atkinLehnerPerm X hs hp5 hsp hpM W]

theorem adjoint [Fintype ↥(ssPlaces p (M * s) K)] [DecidableEq ↥(ssPlaces p (M * s) K)] [DecidableEq ↥(ssPlaces p M K)]
    (hs : s.Prime) (hp5 : 5 ≤ p) (hsp : s ≠ p) (hpM : ¬ p ∣ M) (hsM : ¬ s ∣ M) (W W' : ↥(ssPlaces p (M * s) K)) :
    ((X.degeneracyData.w W : ℕ+) : ℤ) * X.edgeHecke ⟨s, hs⟩ (X.atkinLehnerPerm W) (X.atkinLehnerPerm W') =
      ((X.degeneracyData.w W' : ℕ+) : ℤ) * X.edgeHecke ⟨s, hs⟩ W' W := by
  classical
  haveI : HasPrincipalDivisors K ↥(charLDegeneracyRoof K (M * s) s) := hasPrincipalDivisors_roof hs hsp hpM
  haveI : HasPrincipalDivisors K ↥(modularFunctionFieldC K (M * s)) :=
    hasPrincipalDivisors_modularFunctionFieldC_of_perfectField K (M * s)
  have hwW : ((X.degeneracyData.w W : ℕ+) : ℤ) = (placeWidth (M * s) W.1 : ℤ) := by
    rw [← coe_w X hs hp5 hsp hpM W]
  have hwW' : ((X.degeneracyData.w W' : ℕ+) : ℤ) = (placeWidth (M * s) W'.1 : ℤ) := by
    rw [← coe_w X hs hp5 hsp hpM W']
  rw [edgeHecke_entry X hs hsp hpM hsM, edgeHecke_entry X hs hsp hpM hsM, snd_atkinLehnerPerm, fst_atkinLehnerPerm,
    atkinLehnerPerm_atkinLehnerPerm, ramificationIndexAlong_levelBetaC_atkinLehnerPerm, hwW, hwW']

  have hmain : (placeWidth (M * s) W.1 : ℤ) * ((Place.ramificationIndexAlong (levelAlphaC K M s X.mem_M) W.1 : ℤ)
        * (if X.fst W = X.snd W' then 1 else 0))
      = (placeWidth (M * s) W'.1 : ℤ) * ((Place.ramificationIndexAlong (levelBetaC K M s X.mem_s) W'.1 : ℤ)
        * (if X.snd W' = X.fst W then 1 else 0)) := by
    by_cases hv : X.fst W = X.snd W'
    · rw [if_pos hv, if_pos hv.symm, mul_one, mul_one]
      have hA := ram_mul_placeWidth_fst X hs hp5 hsp hpM W
      have hB := ram_mul_placeWidth_snd X hs hp5 hsp hpM W'
      rw [hv, ← hB] at hA
      have hA' := congrArg (fun n : ℕ => (n : ℤ)) hA
      push_cast at hA'
      linear_combination hA'
    · rw [if_neg hv, if_neg (fun h => hv h.symm), mul_zero, mul_zero, mul_zero, mul_zero]

  have hperm' : (placeWidth (M * s) W.1 : ℤ) * (if W' = X.atkinLehnerPerm W then (1 : ℤ) else 0)
      = (placeWidth (M * s) W'.1 : ℤ) * (if X.atkinLehnerPerm W = W' then (1 : ℤ) else 0) := by
    by_cases hπ : W' = X.atkinLehnerPerm W
    · rw [if_pos hπ, if_pos hπ.symm, hπ, placeWidth_atkinLehnerPerm X hs hp5 hsp hpM W]
    · rw [if_neg hπ, if_neg (fun h => hπ h.symm), mul_zero, mul_zero]
  rw [mul_sub, mul_sub, hmain, hperm']

end Closed

end Datum

end C3bis

end

open AlgebraicCurve ModularCurve C3bis in
theorem solution
    (M s q' : ℕ) [NeZero M] [NeZero s] [Fact q'.Prime] (hs : s.Prime)
    (hq5 : 5 ≤ q') (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), X.fst (X.atkinLehnerPerm W) = X.snd W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)), X.snd (X.atkinLehnerPerm W) = X.fst W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        X.atkinLehnerPerm (X.atkinLehnerPerm W) = W) ∧
    (∀ W : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        X.degeneracyData.w (X.atkinLehnerPerm W) = X.degeneracyData.w W) ∧
    (∀ W W' : ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A)),
        (X.degeneracyData.w W : ℤ) * X.edgeHecke ⟨s, hs⟩ (X.atkinLehnerPerm W) (X.atkinLehnerPerm W') =
          (X.degeneracyData.w W' : ℤ) * X.edgeHecke ⟨s, hs⟩ W' W) := by
  haveI : IsAlgClosed (IsLocalRing.ResidueField ↥A) := ValuationSubring.isAlgClosed_residueField A
  refine ⟨fun W => fst_atkinLehnerPerm X W, fun W => snd_atkinLehnerPerm X W, fun W => atkinLehnerPerm_atkinLehnerPerm X W,
    fun W => w_atkinLehnerPerm X hs hq5 hsq' hq'M W, fun W W' => adjoint X hs hq5 hsq' hq'M hsM W W'⟩

end S_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint
end P2MW
export P2MW.S_ModularCurve_SSLevelDatum_atkinLehnerPerm_swap_degeneracy_and_width_and_edgeHecke_adjoint (solution)
