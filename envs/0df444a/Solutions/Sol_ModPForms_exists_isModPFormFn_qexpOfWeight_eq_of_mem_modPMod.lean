-- Prove2me | solution 1 for ModPForms.exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a8b6b885-ff6e-514c-8dbf-33fe23256e4c

import Mathlib
import Definitions.Def_CuspForm_ModPForms
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification
import Theorems.Thm_ModPForms_exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod
import Theorems.Thm_ModularCurve_isModPFormFn_zero_and_add_and_smul
import Theorems.Thm_ModularCurve_IsModPFormFn_coeffMap
import Theorems.Thm_ModularCurve_IsModPFormFn_of_coeffMap_algebraMap
import Theorems.Thm_ModularCurve_ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_coeffEmb_jq
import Theorems.Thm_ModularCurve_thetaL_coeffMap_eq_coeffMap_single_mul_derivative
import Theorems.Thm_ModularCurve_coeff_jqModC_neg_one
import Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_of_coeffMap_mul_thetaL_pow_eq_qExpansion
import Theorems.Thm_ModularCurve_isIntegral_adjoin_coeffEmb_jq_inv_of_coeffMap_mul_thetaL_pow_eq_qExpansion
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jqModC_inv_coeffMap_residue_of_isIntegral_of_not_dvd
import Theorems.Thm_ValuationSubring_exists_liesOverPrime_algebraicClosure_rat
import Theorems.Thm_ValuationSubring_nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime
import Theorems.Thm_ValuationSubring_residueField_charP_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
p2m_attr_erase "instance" "GaloisRep.ratLocalizedAt.span_isPrime GaloisRep.instAlgebraRatLocalizedAtZMod GaloisRepAdic.instAddCommGroup GaloisRepAdic.instFree GaloisRepAdic.instFinite GaloisRepAdic.instModule ResidualGaloisRep.instModule ResidualGaloisRep.instModuleFinite ResidualGaloisRep.instAddCommGroup ModularCurve.instIsElliptic_tateLaurent ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions ModularCurve.instAlgebraJLineBar ModularCurve.instModuleJLineBar AlgebraicCurve.instHasLocalResidue_of_hasCanonicalLocalResidueK AlgebraicCurve.instHasCanonicalLocalResidueK_of_hasCanonicalLocalResidueKStar AlgebraicCurve.Place.kw_ffgc_finiteDimensional_adicCompletion instAlgebraSubtypeMemValuationSubring_definitions AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersIntegersCompletion ModularCurve.KwF4gRRTate.instAlgebraKAdicCompletionIntegers AlgebraicCurve.Place.kw_ffgc_continuousSMul_adicCompletionComap AlgebraicCurve.Place.kw_ffgc_isScalarTower_integersCompletionCompletion IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions AlgebraicCurve.instHasCanonicalLocalResidueK AlgebraicCurve.Place.instAlgebra_restrictResidueField AlgebraicCurve.Place.instIsScalarTower_restrictResidueField"
p2m_attr_erase "instance" "AlgebraicCurve.instHasLocalResidue AlgebraicCurve.HasSeparableResidue.of_perfectField_of_isCurveOver AlgebraicCurve.HasSeparableResidue.of_perfectField AlgebraicCurve.Place.instIsLocalHom_restrictSubringHom AlgebraicCurve.instHasCanonicalLocalResidueKStar ModularCurve.KwNo6Pin.isLocalRing_completion WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral ModularCurve.TatePoint.instIsElliptic_nearCurve ModularCurve.B3.instIsElliptic_goodModel ModularCurve.instIsScalarTowerJAdjoin WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "GaloisRepAdic.mk.injEq GaloisRepAdic.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.sizeOf_spec GaloisRepAdic.Equiv.mk.injEq ResidualGaloisRep.mk.sizeOf_spec ResidualGaloisRep.mk.injEq ResidualGaloisRep.Equiv.mk.sizeOf_spec ResidualGaloisRep.Equiv.mk.injEq ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single"
p2m_attr_erase "simp" "ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.ProjectiveLine.map_mk ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL AlgebraicCurve.ConstantReduction.toRegularProlongation_residue"
p2m_attr_erase "simp" "AlgebraicCurve.RegularProlongation.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.toRegularProlongation_integers AlgebraicCurve.RegularProlongation.mk.injEq AlgebraicCurve.ConstantReduction.mk.injEq AlgebraicCurve.ConstantReduction.mk.sizeOf_spec AlgebraicCurve.ConstantReduction.divMap_apply AlgebraicCurve.ConstantReduction.coe_degZeroMap AlgebraicCurve.Place.differentialCoeff_zero AlgebraicCurve.Place.differentialCoeff_dCoord ModularCurve.cuspCount_one AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.sizeOf_spec AlgebraicCurve.Place.CanonicalLocalResidueDataK.mk.injEq AlgebraicCurve.adeleSingle_coe AlgebraicCurve.kaehlerResidueTermKFam_apply AlgebraicCurve.Place.LocalResidueData.mk.injEq AlgebraicCurve.Place.LocalResidueData.mk.sizeOf_spec AlgebraicCurve.Place.kw_ffgc_adicCompletionComapIntegers_coe AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.sizeOf_spec AlgebraicCurve.Place.mem_simplePoleSubmodule AlgebraicCurve.Place.coe_uniformizerSubring ModularCurve.Lg37.Lg37CompletionSection.mk.injEq AlgebraicCurve.Place.CoefficientFieldSection.mk.injEq AlgebraicCurve.Place.CanonicalLocalResidueDataS.mk.injEq ModularCurve.Lg37.Lg37CompletionSection.mk.sizeOf_spec AlgebraicCurve.Place.CoefficientFieldSection.mk.sizeOf_spec AlgebraicCurve.Place.poleSubmodule_one AlgebraicCurve.Place.mem_poleSubmodule HahnSeries.ramScale_apply WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual"
p2m_attr_erase "simp" "AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.veluQuotientOfSums_a₂ WeierstrassCurve.veluQuotientOfSums_a₁ WeierstrassCurve.veluQuotientOfSums_a₃ ModularCurve.B3.cycOfCongr_apply_coe ModularCurve.B3.cycOfTorsionBy_symm_apply_coe ModularCurve.B3.redPoint_zero ModularCurve.B3.pointAddEquivOfEq_rfl ModularCurve.B3.vcAddEquiv_apply ModularCurve.B3.scaleAddEquiv_apply ModularCurve.B3.cycOfTorsionBy_apply_coe ModularCurve.B3.val_inv_sU ModularCurve.B3.val_sU ModularCurve.B3.resO_apply HahnSeries.coeff_hahnTwist ModularCurve.HahnSpecialise.coe_specialiseCycSub CycSubOf.coe_map ModularCurve.HahnSpecialise.algebraMap_Qbar_apply ModularCurve.HahnSpecialise.resH_apply ModularCurve.HahnSpecialise.liftModel_map_subtype ModularCurve.HahnSpecialise.specialise_zero WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton"
p2m_attr_erase "simp" "WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right"
p2m_attr_erase "simp" "FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

open ModularCurve UpperHalfPlane

noncomputable section

namespace EasyAssembly

open HahnSeries

def thetaZ : LaurentSeries ℤ := single (1 : ℤ) (1 : ℤ) * LaurentSeries.derivative ℤ (jqModC ℤ)

theorem coeff_thetaZ (n : ℤ) : thetaZ.coeff n = n * (jqModC ℤ).coeff n := by
  rw [thetaZ, coeff_single_mul, one_mul, LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff,
    show n - 1 + ((1 : ℕ) : ℤ) = n by push_cast; ring, Ring.choose_one_right, zsmul_eq_mul, Int.cast_id]

theorem coeff_thetaZ_neg_one : thetaZ.coeff (-1) = -1 := by
  rw [coeff_thetaZ, coeff_jqModC_neg_one]; ring

theorem coeff_thetaZ_of_lt {n : ℤ} (hn : n < -1) : thetaZ.coeff n = 0 := by
  rw [coeff_thetaZ, coeff_jqModC_of_lt ℤ hn, mul_zero]

theorem thetaZ_ne_zero : thetaZ ≠ 0 := fun h => by
  have := coeff_thetaZ_neg_one; rw [h] at this; simp at this

theorem order_thetaZ : thetaZ.order = -1 := by
  apply le_antisymm (order_le_of_coeff_ne_zero (by rw [coeff_thetaZ_neg_one]; norm_num))
  by_contra hlt
  exact HahnSeries.coeff_order_eq_zero.not.mpr thetaZ_ne_zero (coeff_thetaZ_of_lt (not_le.1 hlt))

theorem isUnit_thetaZ : IsUnit thetaZ := by
  rw [HahnSeries.isUnit_iff, leadingCoeff_eq, order_thetaZ, coeff_thetaZ_neg_one]
  exact isUnit_one.neg

theorem coeffMap_thetaZ {K : Type*} [Field K] (f : ℤ →+* K) : coeffMap f thetaZ = thetaL K (jqModC K) := by
  rw [thetaZ, ← thetaL_coeffMap_eq_coeffMap_single_mul_derivative, coeffMap_jqModC]

def yZ (a : ℕ → ℤ) (m : ℕ) : LaurentSeries ℤ :=
  ofPowerSeries ℤ ℤ (PowerSeries.mk a) * ((isUnit_thetaZ.unit⁻¹ ^ m : (LaurentSeries ℤ)ˣ) : LaurentSeries ℤ)

theorem map_mk {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ → R) :
    (PowerSeries.mk a).map f = PowerSeries.mk (fun n => f (a n)) := by
  ext n; simp [PowerSeries.coeff_map]

theorem coeffMap_yZ {K : Type*} [Field K] (f : ℤ →+* K) (a : ℕ → ℤ) (m : ℕ) :
    coeffMap f (yZ a m) = ofPowerSeries ℤ K (PowerSeries.mk fun n => (a n : K)) *
      (thetaL K (jqModC K))⁻¹ ^ m := by
  rw [yZ, map_mul, coeffMap_ofPowerSeries, map_mk, Units.val_pow_eq_pow_val, map_pow, map_units_inv,
    IsUnit.unit_spec, coeffMap_thetaZ]
  congr 1
  ext n; simp

theorem coeffMap_yZ_mul {K : Type*} [Field K] (f : ℤ →+* K) (a : ℕ → ℤ) (m : ℕ)
    (hT : thetaL K (jqModC K) ≠ 0) :
    coeffMap f (yZ a m) * thetaL K (jqModC K) ^ m = ofPowerSeries ℤ K (PowerSeries.mk fun n => (a n : K)) := by
  rw [coeffMap_yZ, mul_assoc, ← mul_pow, inv_mul_cancel₀ hT, one_pow, mul_one]

theorem thetaL_ne' (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp only [HahnSeries.coeff_zero] at this
  rw [← coeffMap_thetaZ (Int.castRingHom K), coeffMap_coeff, coeff_thetaZ_neg_one] at this
  simp at this

def XZ (a : ℕ → ℤ) (m : ℕ) : LaurentSeries ℤ := yZ a m ^ 6 * jqModC ℤ ^ (4 * m) * (jqModC ℤ - 1728) ^ (3 * m)
def XZ' (a : ℕ → ℤ) (m : ℕ) : LaurentSeries ℤ := yZ a m ^ 2 * jqModC ℤ ^ m * (jqModC ℤ - 1728) ^ m

theorem coeffMap_XZ {R : Type*} [CommRing R] (g : ℤ →+* R) (a : ℕ → ℤ) (m : ℕ) :
    coeffMap g (XZ a m) = coeffMap g (yZ a m) ^ 6 * jqModC R ^ (4 * m) * (jqModC R - 1728) ^ (3 * m) := by
  simp only [XZ, map_mul, map_pow, map_sub, map_ofNat, coeffMap_jqModC]

theorem coeffMap_XZ' {R : Type*} [CommRing R] (g : ℤ →+* R) (a : ℕ → ℤ) (m : ℕ) :
    coeffMap g (XZ' a m) = coeffMap g (yZ a m) ^ 2 * jqModC R ^ m * (jqModC R - 1728) ^ m := by
  simp only [XZ', map_mul, map_pow, map_sub, map_ofNat, coeffMap_jqModC]

theorem yQ_mem (N : ℕ) [NeZero N] (m : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)))
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    coeffMap (Int.castRingHom ℚ) (yZ a m) ∈ modularFunctionFieldFull N := by
  rw [← modularFunctionField_eq_full]
  have h1 := ofPowerSeries_mul_thetaL_jq_zpow_neg_mem_modularFunctionField N m f a ha
  rw [zpow_neg, zpow_natCast, ← inv_pow] at h1
  rw [coeffMap_yZ]
  exact h1

theorem mem_bar (N : ℕ) [NeZero N] (m : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)))
    (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) (e r s : ℕ) :
    coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (yZ a m) ^ e * jqModC (AlgebraicClosure ℚ) ^ r
      * (jqModC (AlgebraicClosure ℚ) - 1728) ^ s ∈ modularFunctionFieldBar N := by
  have hy : coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (yZ a m) ∈ modularFunctionFieldBar N := by
    have := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (yQ_mem N m f a ha)
    rw [coeffEmb, coeffMap_coeffMap] at this
    rwa [coeffMap_congr (RingHom.ext_int _ _)] at this
  have hj : jqModC (AlgebraicClosure ℚ) ∈ modularFunctionFieldBar N := by
    have := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionField_le_full N (jq_mem N))
    rwa [coeffEmb_jq] at this
  refine mul_mem (mul_mem (pow_mem hy e) (pow_mem hj r)) (pow_mem (sub_mem hj ?_) s)
  exact natCast_mem _ 1728

section Red

variable (N : ℕ) [NeZero N] (m : ℕ) (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ)))
  (a : ℕ → ℤ) (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ))
  {p : ℕ} [Fact p.Prime] (hpN : ¬ p ∣ N) (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)

scoped instance : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ

def sigma : AlgebraicClosure ℚ →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := AlgebraicClosure ℚ)).toRingHom

include ha in
theorem hY_complex : coeffMap sigma (coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) (yZ a m))
      * thetaL ℂ (coeffEmb ℂ jq) ^ m = ((qExpansion 1 (f : ℍ → ℂ) : PowerSeries ℂ) : LaurentSeries ℂ) := by
  rw [coeffMap_coeffMap, coeffMap_congr (RingHom.ext_int _ (Int.castRingHom ℂ)), coeffEmb_jq,
    coeffMap_yZ_mul (Int.castRingHom ℂ) a m (thetaL_ne' ℂ)]
  congr 1
  ext n
  rw [PowerSeries.coeff_mk]
  exact (ha n).symm

theorem coeffMap_subtype_int (x : LaurentSeries ℤ) :
    coeffMap A.subtype (coeffMap (Int.castRingHom A) x) = coeffMap (Int.castRingHom (AlgebraicClosure ℚ)) x := by
  rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) _

theorem coeffMap_residue_int (x : LaurentSeries ℤ) :
    coeffMap (IsLocalRing.residue A) (coeffMap (Int.castRingHom A) x)
      = coeffMap (Int.castRingHom (IsLocalRing.ResidueField A)) x := by
  rw [coeffMap_coeffMap]; exact coeffMap_congr (RingHom.ext_int _ _) _

include ha hA hpN in
theorem red_h1 : IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) ({jqModC (IsLocalRing.ResidueField A)} : Set _))
    ((coeffMap (Int.castRingHom (IsLocalRing.ResidueField A)) (yZ a m)) ^ 6 * jqModC _ ^ (4 * m)
      * (jqModC _ - algebraMap (IsLocalRing.ResidueField A) _ 1728) ^ (3 * m)) := by
  have hint := isIntegral_adjoin_coeffEmb_jq_of_coeffMap_mul_thetaL_pow_eq_qExpansion sigma N m f _
    (hY_complex N m f a ha)
  rw [coeffEmb_jq, map_ofNat] at hint
  have hred := isIntegral_adjoin_jqModC_coeffMap_residue_of_isIntegral_of_not_dvd N hpN A hA
    (coeffMap (Int.castRingHom A) (XZ a m))
    (by rw [coeffMap_subtype_int, coeffMap_XZ]; exact mem_bar N m f a ha 6 (4 * m) (3 * m))
    (by rw [coeffEmb_jq, coeffMap_subtype_int, coeffMap_XZ]; exact hint)
  rw [coeffMap_residue_int, coeffMap_XZ] at hred
  rwa [map_ofNat]

include ha hA hpN in
theorem red_h2 : IsIntegral (Algebra.adjoin (IsLocalRing.ResidueField A) ({(jqModC (IsLocalRing.ResidueField A))⁻¹} : Set _))
    ((coeffMap (Int.castRingHom (IsLocalRing.ResidueField A)) (yZ a m)) ^ 2 * jqModC _ ^ m
      * (jqModC _ - algebraMap (IsLocalRing.ResidueField A) _ 1728) ^ m) := by
  have hint := isIntegral_adjoin_coeffEmb_jq_inv_of_coeffMap_mul_thetaL_pow_eq_qExpansion sigma N m f _
    (hY_complex N m f a ha)
  rw [coeffEmb_jq, map_ofNat] at hint
  have hred := isIntegral_adjoin_jqModC_inv_coeffMap_residue_of_isIntegral_of_not_dvd N hpN A hA
    (coeffMap (Int.castRingHom A) (XZ' a m))
    (by rw [coeffMap_subtype_int, coeffMap_XZ']; exact mem_bar N m f a ha 2 m m)
    (by rw [coeffEmb_jq, coeffMap_subtype_int, coeffMap_XZ']; exact hint)
  rw [coeffMap_residue_int, coeffMap_XZ'] at hred
  rwa [map_ofNat]

end Red

theorem isModPFormFn_generator (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ)
    (f : ModularForm (CongruenceSubgroup.Gamma0 N) (2 * (m : ℤ))) (a : ℕ → ℤ)
    (ha : ∀ n : ℕ, ModularFormClass.qCoeff f n = (a n : ℂ)) :
    IsModPFormFn K m (coeffMap (Int.castRingHom K) (yZ a m)) := by

  obtain ⟨A, hA⟩ := ValuationSubring.exists_liesOverPrime_algebraicClosure_rat ⟨p, hp.out⟩
  haveI : CharP (IsLocalRing.ResidueField A) p := ValuationSubring.residueField_charP_of_liesOverPrime A hp.out hA

  have hy : ∀ (L : Type) [Field L], coeffMap (Int.castRingHom L) (yZ a m) * thetaL L (jqModC L) ^ m
      = ofPowerSeries ℤ L (PowerSeries.mk fun n => (a n : L)) := fun L _ =>
    coeffMap_yZ_mul (Int.castRingHom L) a m (thetaL_ne' L)

  have hk : IsModPFormFn (IsLocalRing.ResidueField A) m (coeffMap (Int.castRingHom _) (yZ a m)) :=
    ⟨red_h1 N m f a ha hpN A hA, red_h2 N m f a ha hpN A hA⟩

  letI : Algebra (ZMod p) (IsLocalRing.ResidueField A) := ZMod.algebra _ p
  haveI : Algebra.IsAlgebraic (ZMod p) (IsLocalRing.ResidueField A) := by
    obtain ⟨e⟩ := ValuationSubring.nonempty_residueField_ringEquiv_algebraicClosure_zmod_of_liesOverPrime A hA
    have hcomm : e.toRingHom.comp (algebraMap (ZMod p) (IsLocalRing.ResidueField A))
        = algebraMap (ZMod p) (AlgebraicClosure (ZMod p)) := Subsingleton.elim _ _
    refine ⟨fun x => ?_⟩
    obtain ⟨P, hPm, hPx⟩ := (Algebra.IsIntegral.isIntegral (R := ZMod p) (e x))
    have hx : IsIntegral (ZMod p) x := by
      refine ⟨P, hPm, ?_⟩
      apply e.injective
      rw [map_zero, show (e : IsLocalRing.ResidueField A → AlgebraicClosure (ZMod p)) = e.toRingHom from rfl,
        Polynomial.hom_eval₂, hcomm]
      exact hPx
    exact hx.isAlgebraic
  have hFp : IsModPFormFn (ZMod p) m (coeffMap (Int.castRingHom (ZMod p)) (yZ a m)) := by
    apply ModularCurve.IsModPFormFn.of_coeffMap_algebraMap (K := IsLocalRing.ResidueField A)
    rw [coeffMap_coeffMap, coeffMap_congr (RingHom.ext_int _ (Int.castRingHom _))]
    exact hk
  have hK := ModularCurve.IsModPFormFn.coeffMap (ZMod.castHom (dvd_refl p) K) m _ hFp
  rwa [coeffMap_coeffMap, coeffMap_congr (RingHom.ext_int _ (Int.castRingHom K))] at hK

theorem thetaL_ne (K : Type*) [Field K] : thetaL K (jqModC K) ≠ 0 := by
  intro h
  have := congrArg (fun x : LaurentSeries K => x.coeff (-1)) h
  simp only [HahnSeries.coeff_zero] at this
  rw [← coeffMap_thetaZ (Int.castRingHom K), coeffMap_coeff, coeff_thetaZ_neg_one] at this
  simp at this

theorem C_eq_algebraMap' {F : Type*} [Field F] (a : F) :
    (HahnSeries.C a : LaurentSeries F) = algebraMap F (LaurentSeries F) a := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem main (p : ℕ) [hp : Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ) (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    ∃ G : ↥(modularFunctionFieldC K N),
      IsModPFormFn K m (G : LaurentSeries K) ∧
      qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ := by
  have hT := thetaL_ne' K
  obtain ⟨h0, hadd, hsmul⟩ := ModularCurve.isModPFormFn_zero_and_add_and_smul K m

  suffices H : ∃ G : ↥(modularFunctionFieldC K N), IsModPFormFn K m (G : LaurentSeries K) ∧
      (G : LaurentSeries K) * thetaL K (jqModC K) ^ m = HahnSeries.ofPowerSeries ℤ K φ by
    obtain ⟨G, hG, hq⟩ := H
    exact ⟨G, hG, by simpa [qexpOfWeight, thetaJ, zpow_natCast] using hq⟩
  induction hφ using Submodule.span_induction with
  | mem φ hφ =>
    obtain ⟨f, a, ha, rfl⟩ := hφ

    obtain ⟨G, hG⟩ := ModPForms.exists_coe_mul_thetaL_jqModC_pow_eq_ofPowerSeries_of_mem_modPMod p N hpN K m
      (PowerSeries.mk fun n => ((a n : ℤ) : K)) (Submodule.subset_span ⟨f, a, ha, rfl⟩)
    have hy := coeffMap_yZ_mul (Int.castRingHom K) a m hT
    have hGy : (G : LaurentSeries K) = coeffMap (Int.castRingHom K) (yZ a m) := by
      apply mul_right_cancel₀ (pow_ne_zero m hT)
      rw [hG, ← hy]
    refine ⟨G, ?_, hG⟩
    rw [hGy]
    exact isModPFormFn_generator p N hpN K m f a ha
  | zero => exact ⟨0, by simpa using h0, by simp⟩
  | add φ ψ _ _ hφ hψ =>
    obtain ⟨G, hG, hGq⟩ := hφ
    obtain ⟨H, hH, hHq⟩ := hψ
    exact ⟨G + H, by simpa using hadd _ _ hG hH, by rw [IntermediateField.coe_add, add_mul, hGq, hHq, map_add]⟩
  | smul c φ _ hφ =>
    obtain ⟨G, hG, hGq⟩ := hφ
    refine ⟨algebraMap K _ c * G, ?_, ?_⟩
    · have : ((algebraMap K _ c * G : ↥(modularFunctionFieldC K N)) : LaurentSeries K) = c • (G : LaurentSeries K) := by
        rw [IntermediateField.coe_mul, ← HahnSeries.C_mul_eq_smul, C_eq_algebraMap']; rfl
      rw [this]; exact hsmul c _ hG
    · rw [IntermediateField.coe_mul, mul_assoc, hGq, PowerSeries.smul_eq_C_mul, map_mul, HahnSeries.ofPowerSeries_C,
        C_eq_algebraMap']
      rfl

end EasyAssembly
p2m_reactivate "P2MW.S_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod.EasyAssembly"

end
p2m_reactivate "P2MW.S_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod.EasyAssembly"

theorem solution
    (p : ℕ) [Fact p.Prime] (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] (m : ℕ)
    (φ : PowerSeries K) (hφ : φ ∈ ModPForms.modPMod N (2 * (m : ℤ)) K) :
    ∃ G : ↥(modularFunctionFieldC K N),
      IsModPFormFn K m (G : LaurentSeries K) ∧
      qexpOfWeight K (m : ℤ) (G : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K φ :=
  EasyAssembly.main p N hpN K m φ hφ

end S_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod
end P2MW
export P2MW.S_ModPForms_exists_isModPFormFn_qexpOfWeight_eq_of_mem_modPMod (solution)
