-- Prove2me | solution 1 for ModularCurve.stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/1cbf8eaa-c4d7-58c7-ac41-19eb254ad13e

import Mathlib
import Definitions.Def_ModularCurve_PlaceWidth
import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_ModPFormFn
import Definitions.Def_SwdAlgebra
import Theorems.Thm_ModularCurve_exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq
import Theorems.Thm_ModularCurve_qP_mul_thetaL_jqModC_zpow_mul_eq
import Theorems.Thm_ModularCurve_thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC
import Theorems.Thm_ModularCurve_placeRamificationJ_dvd_jWidth_of_mem_ssPlaces
import Theorems.Thm_ModularCurve_jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div
import Theorems.Thm_AlgebraicCurve_Place_evalAt_mul
import Theorems.Thm_AlgebraicCurve_Place_evalAt_inv
import Theorems.Thm_AlgebraicCurve_Place_evalAt_algebraMap
import Theorems.Thm_P2M_Dup_AlgebraicCurve_Place_mem_of_ord_nonneg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces
p2m_attr_erase "instance" "ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions WeierstrassCurve.Affine.CoordinateRing.moduleFinite WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4 ModularCurve.ElevenA1.instDecidableEquation ModularCurve.ElevenA1.instDecidableNonsingular"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero"
p2m_attr_erase "simp" "TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec"
p2m_attr_erase "simp" "WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero"
p2m_attr_erase "simp" "ModularForm.val_upperTriangularGL ModularCurve.qExpandAlgHomC_apply WeierstrassCurve.twoVeluCurve_a₁ WeierstrassCurve.twoVeluCurve_a₂ WeierstrassCurve.twoVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₃ WeierstrassCurve.xVeluCurve_a₂ WeierstrassCurve.xVeluCurve_a₁ WeierstrassCurve.veluWSum_empty WeierstrassCurve.veluQuotient_a₁ WeierstrassCurve.veluQuotient_a₃ WeierstrassCurve.veluQuotient_empty WeierstrassCurve.veluTSum_empty WeierstrassCurve.veluQuotient_a₂ WeierstrassCurve.veluQuotient2_a₂ WeierstrassCurve.veluQuotient2_a₃ WeierstrassCurve.veluQuotient2_a₁ WeierstrassCurve.veluPointMap2_zero WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero WeierstrassCurve.veluY_empty WeierstrassCurve.veluX_empty WeierstrassCurve.map_veluU WeierstrassCurve.map_veluT WeierstrassCurve.map_veluW WeierstrassCurve.map_veluGy WeierstrassCurve.map_veluGx WeierstrassCurve.map_veluWSum_singleton WeierstrassCurve.map_veluTSum_singleton WeierstrassCurve.veluPointMap3_zero WeierstrassCurve.vcInvEmbedding_apply ModularCurve.ProjectiveLine.map_mk WeierstrassCurve.Affine.IsogenyEndDatum.mk.injEq WeierstrassCurve.Affine.IsogenyHomDatum.mk.sizeOf_spec WeierstrassCurve.Affine.IsogenyHomDatum.mk.injEq WeierstrassCurve.Affine.IsogenyEndDatum.mk.sizeOf_spec AlgebraicCurve.Pic0.coe_pushforwardAlongDegZero WeierstrassCurve.Affine.pointMapOfPushforward_apply WeierstrassCurve.Affine.pointClass_zero WeierstrassCurve.Affine.pic0ToPoint_pointClass"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.deg_placeOfPoint WeierstrassCurve.Affine.coe_pointDivisor WeierstrassCurve.Affine.pointEquivPlace_symm_placeOfPoint WeierstrassCurve.Affine.pointEquivPlace_apply WeierstrassCurve.Affine.genusOnePic0Equiv_symm_apply WeierstrassCurve.Affine.pointDivisor_zero WeierstrassCurve.Affine.pic0ToPoint_mk WeierstrassCurve.Affine.divisorSum_single WeierstrassCurve.Affine.genusOnePic0Equiv_apply AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal WeierstrassCurve.Affine.ratFuncToFunctionField_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_C WeierstrassCurve.Affine.Point.yc_some WeierstrassCurve.Affine.Point.xc_some WeierstrassCurve.Affine.pointPull_algebraMap WeierstrassCurve.Affine.pointHom_mk_C_X WeierstrassCurve.Affine.pointHom_mk_Y WeierstrassCurve.Affine.placeOf_asIdeal WeierstrassCurve.reducePoint_zero WeierstrassCurve.Affine.Point.galoisRep_apply PeriodPair.weierstrassCurve_a₆ PeriodPair.weierstrassCurve_a₃ PeriodPair.weierstrassCurve_a₁ PeriodPair.ofTau_ω₂ PeriodPair.scale_ω₂ PeriodPair.ofTau_ω₁ PeriodPair.toPoint_zero PeriodPair.toPoint_of_mem PeriodPair.weierstrassCurve_a₂ PeriodPair.ofTau_lattice PeriodPair.scale_ω₁ PeriodPair.weierstrassCurve_a₄ AddMonoid.End.DualEndData.symm_trace AddMonoid.End.dualEndData_intCast_norm AddMonoid.End.DualEndData.ofCharPoly_norm AddMonoid.End.DualEndData.mk.sizeOf_spec"
p2m_attr_erase "simp" "AddMonoid.End.DualEndData.mk.injEq AddMonoid.End.DualEndData.ofCharPoly_dual AddMonoid.End.dualEndData_intCast_dual AddMonoid.End.DualEndData.intLinComb_norm AddMonoid.End.DualEndData.ofCharPoly_trace AddMonoid.End.DualEndData.intLinComb_dual AddMonoid.End.DualEndData.symm_dual AddMonoid.End.DualEndData.intLinComb_trace AddMonoid.End.dualEndData_intCast_trace AddMonoid.End.DualEndData.symm_norm WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero FormalCoordinates.mk.injEq WeierstrassCurve.formalParam_zero WeierstrassCurve.SmoothLocusReductionData.reduceHom₀_apply WeierstrassCurve.formalParam_some FormalCoordinates.mk.sizeOf_spec WeierstrassCurve.SmoothLocusReductionData.mk.injEq WeierstrassCurve.reducePointSmooth_zero WeierstrassCurve.SmoothLocusReductionData.mk.sizeOf_spec WeierstrassCurve.mem_zeroComponentSubgroup_iff"
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces.AlgebraicCurve ModularCurve P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces.ModularCurve"

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.residueInv_algebraMap Place.evalAt_of_mem"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring mem_of_ord_nonneg IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_algebraMap evalAt_mul evalAt_inv"
namespace RobertB
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem isUnit_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    IsUnit (⟨f, hf⟩ : v.toValuationSubring) := by
  by_contra hu
  apply h
  rw [Place.evalAt_of_mem v hf, (IsLocalRing.residue_eq_zero_iff _).mpr ((IsLocalRing.mem_maximalIdeal _).mpr hu),
    ← map_zero (algebraMap K v.ResidueField), Place.residueInv_algebraMap]

theorem ne_zero_and_ord_eq_zero_of_evalAt_ne_zero {f : F} (hf : f ∈ v.toValuationSubring) (h : v.evalAt f ≠ 0) :
    f ≠ 0 ∧ v.ord f = 0 := by
  obtain ⟨u, hu⟩ := isUnit_of_evalAt_ne_zero v hf h
  have hcoe : ((u : v.toValuationSubring) : F) = f := by rw [hu]
  refine ⟨?_, ?_⟩
  · rw [← hcoe]; simp [ne_eq, ZeroMemClass.coe_eq_zero]
  · rw [← hcoe]; exact v.ord_coe_unit u

theorem inv_mem_and_evalAt_inv (hv : v.IsRational) {f : F} (hf : f ∈ v.toValuationSubring)
    (h : v.evalAt f ≠ 0) : f⁻¹ ∈ v.toValuationSubring ∧ v.evalAt f⁻¹ = (v.evalAt f)⁻¹ := by
  obtain ⟨hf0, hord⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hf h
  exact ⟨v.mem_of_ord_nonneg (inv_ne_zero hf0) (by rw [v.ord_inv, hord, neg_zero]), v.evalAt_inv hv hf0 hord⟩

theorem evalAt_sub (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f - g) = v.evalAt f - v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_sub, v.algebraMap_evalAt hv (sub_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, ← map_sub]
  rfl

theorem evalAt_add (hv : v.IsRational) {f g : F} (hf : f ∈ v.toValuationSubring) (hg : g ∈ v.toValuationSubring) :
    v.evalAt (f + g) = v.evalAt f + v.evalAt g := by
  apply v.algebraMap_residueField_injective
  rw [map_add, v.algebraMap_evalAt hv (add_mem hf hg), v.algebraMap_evalAt hv hf, v.algebraMap_evalAt hv hg, ← map_add]
  rfl

theorem ord_div {f g : F} (hf : f ≠ 0) (hg : g ≠ 0) : v.ord (f / g) = v.ord f - v.ord g := by
  rw [div_eq_mul_inv, v.ord_mul hf (inv_ne_zero hg), v.ord_inv, sub_eq_add_neg]

theorem robert_quotient_generic (hv : v.IsRational) {J A Φ : F} (hJ : J ∈ v.toValuationSubring)
    (hA : A ∈ v.toValuationSubring)
    (hE : Φ * J * (J - algebraMap K F 1728) = algebraMap K F 12 * A * J * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F (v.evalAt J)))
    (h0 : v.evalAt J ≠ 0) (h1 : v.evalAt J ≠ 1728) :
    Φ ∈ v.toValuationSubring ∧ v.evalAt Φ = 12 * v.evalAt A := by
  have hc : ∀ a : K, algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem'
  set j0 := v.evalAt J with hj0
  have hJm : J - algebraMap K F 1728 ∈ v.toValuationSubring := sub_mem hJ (hc _)
  have hJmv : v.evalAt (J - algebraMap K F 1728) = j0 - 1728 := by
    rw [evalAt_sub v hv hJ (hc _), v.evalAt_algebraMap]
  have hJmv0 : v.evalAt (J - algebraMap K F 1728) ≠ 0 := by rw [hJmv]; exact sub_ne_zero.mpr h1
  obtain ⟨hJi, hJiv⟩ := inv_mem_and_evalAt_inv v hv hJ h0
  obtain ⟨hJmi, hJmiv⟩ := inv_mem_and_evalAt_inv v hv hJm hJmv0
  obtain ⟨hJ0, -⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hJ h0
  obtain ⟨hJm0, -⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hJm hJmv0
  have hJc : J - algebraMap K F j0 ∈ v.toValuationSubring := sub_mem hJ (hc _)
  have hJcv : v.evalAt (J - algebraMap K F j0) = 0 := by
    rw [evalAt_sub v hv hJ (hc _), v.evalAt_algebraMap, hj0, sub_self]

  have hT1 : algebraMap K F 12 * A * J * (J - algebraMap K F 1728) ∈ v.toValuationSubring :=
    mul_mem (mul_mem (mul_mem (hc _) hA) hJ) hJm
  have hL : algebraMap K F 14 * J - algebraMap K F 13824 ∈ v.toValuationSubring :=
    sub_mem (mul_mem (hc _) hJ) (hc _)
  have hT2 : algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F j0)
      ∈ v.toValuationSubring := mul_mem (mul_mem (hc _) hL) hJc
  have hPm : Φ * J * (J - algebraMap K F 1728) ∈ v.toValuationSubring := by rw [hE]; exact sub_mem hT1 hT2
  have hPv : v.evalAt (Φ * J * (J - algebraMap K F 1728)) = 12 * v.evalAt A * j0 * (j0 - 1728) := by
    rw [hE, evalAt_sub v hv hT1 hT2, v.evalAt_mul hv (mul_mem (hc _) hL) hJc, hJcv, mul_zero, sub_zero,
      v.evalAt_mul hv (mul_mem (mul_mem (hc _) hA) hJ) hJm, v.evalAt_mul hv (mul_mem (hc _) hA) hJ,
      v.evalAt_mul hv (hc _) hA, v.evalAt_algebraMap, hJmv]
  have hΦ : Φ = Φ * J * (J - algebraMap K F 1728) * (J - algebraMap K F 1728)⁻¹ * J⁻¹ := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hΦ]; exact mul_mem (mul_mem hPm hJmi) hJi
  · rw [hΦ, v.evalAt_mul hv (mul_mem hPm hJmi) hJi, v.evalAt_mul hv hPm hJmi, hPv, hJmiv, hJiv, hJmv, ← hj0,
      mul_inv_cancel_right₀ (sub_ne_zero.mpr h1), mul_inv_cancel_right₀ h0]

theorem robert_quotient_zero (hv : v.IsRational) {J A Φ : F} (hJ : J ∈ v.toValuationSubring)
    (hA : A ∈ v.toValuationSubring) (hJ0 : J ≠ 0)
    (hE : Φ * J * (J - algebraMap K F 1728) = algebraMap K F 12 * A * J * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F (v.evalAt J)))
    (h0 : v.evalAt J = 0) (h1728 : (1728 : K) ≠ 0) (h2 : (2 : K) ≠ 0) :
    Φ ∈ v.toValuationSubring ∧ v.evalAt Φ = 12 * v.evalAt A - 4 := by
  have hc : ∀ a : K, algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem'
  rw [h0, map_zero, sub_zero] at hE

  have hE' : Φ * (J - algebraMap K F 1728) = algebraMap K F 12 * A * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) := by
    apply mul_left_cancel₀ hJ0
    linear_combination hE
  have hJm : J - algebraMap K F 1728 ∈ v.toValuationSubring := sub_mem hJ (hc _)
  have hJmv : v.evalAt (J - algebraMap K F 1728) = -1728 := by
    rw [evalAt_sub v hv hJ (hc _), v.evalAt_algebraMap, h0, zero_sub]
  have hJmv0 : v.evalAt (J - algebraMap K F 1728) ≠ 0 := by rw [hJmv]; exact neg_ne_zero.mpr h1728
  obtain ⟨hJmi, hJmiv⟩ := inv_mem_and_evalAt_inv v hv hJm hJmv0
  obtain ⟨hJm0, -⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hJm hJmv0
  have hT1 : algebraMap K F 12 * A * (J - algebraMap K F 1728) ∈ v.toValuationSubring :=
    mul_mem (mul_mem (hc _) hA) hJm
  have hL : algebraMap K F 14 * J - algebraMap K F 13824 ∈ v.toValuationSubring :=
    sub_mem (mul_mem (hc _) hJ) (hc _)
  have hT2 : algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) ∈ v.toValuationSubring :=
    mul_mem (hc _) hL
  have hPm : Φ * (J - algebraMap K F 1728) ∈ v.toValuationSubring := by rw [hE']; exact sub_mem hT1 hT2
  have hPv : v.evalAt (Φ * (J - algebraMap K F 1728)) = 12 * v.evalAt A * (-1728) - 2⁻¹ * (-13824) := by
    rw [hE', evalAt_sub v hv hT1 hT2, v.evalAt_mul hv (hc _) hL, evalAt_sub v hv (mul_mem (hc _) hJ) (hc _),
      v.evalAt_mul hv (hc _) hJ, h0, v.evalAt_algebraMap, v.evalAt_algebraMap, v.evalAt_algebraMap,
      v.evalAt_mul hv (mul_mem (hc _) hA) hJm, v.evalAt_mul hv (hc _) hA, v.evalAt_algebraMap, hJmv]
    ring
  have hΦ : Φ = Φ * (J - algebraMap K F 1728) * (J - algebraMap K F 1728)⁻¹ := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hΦ]; exact mul_mem hPm hJmi
  · rw [hΦ, v.evalAt_mul hv hPm hJmi, hPv, hJmiv, hJmv]
    field_simp
    ring

theorem robert_quotient_1728 (hv : v.IsRational) {J A Φ : F} (hJ : J ∈ v.toValuationSubring)
    (hA : A ∈ v.toValuationSubring) (hJ1728 : J - algebraMap K F 1728 ≠ 0)
    (hE : Φ * J * (J - algebraMap K F 1728) = algebraMap K F 12 * A * J * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F (v.evalAt J)))
    (h0 : v.evalAt J = 1728) (h1728 : (1728 : K) ≠ 0) (h2 : (2 : K) ≠ 0) :
    Φ ∈ v.toValuationSubring ∧ v.evalAt Φ = 12 * v.evalAt A - 3 := by
  have hc : ∀ a : K, algebraMap K F a ∈ v.toValuationSubring := v.algebraMap_mem'
  rw [h0] at hE

  have hE' : Φ * J = algebraMap K F 12 * A * J - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) := by
    apply mul_right_cancel₀ hJ1728
    linear_combination hE
  have hJv0 : v.evalAt J ≠ 0 := by rw [h0]; exact h1728
  obtain ⟨hJi, hJiv⟩ := inv_mem_and_evalAt_inv v hv hJ hJv0
  obtain ⟨hJ0, -⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero v hJ hJv0
  have hT1 : algebraMap K F 12 * A * J ∈ v.toValuationSubring := mul_mem (mul_mem (hc _) hA) hJ
  have hL : algebraMap K F 14 * J - algebraMap K F 13824 ∈ v.toValuationSubring :=
    sub_mem (mul_mem (hc _) hJ) (hc _)
  have hT2 : algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) ∈ v.toValuationSubring :=
    mul_mem (hc _) hL
  have hPm : Φ * J ∈ v.toValuationSubring := by rw [hE']; exact sub_mem hT1 hT2
  have hPv : v.evalAt (Φ * J) = 12 * v.evalAt A * 1728 - 2⁻¹ * (14 * 1728 - 13824) := by
    rw [hE', evalAt_sub v hv hT1 hT2, v.evalAt_mul hv (hc _) hL, evalAt_sub v hv (mul_mem (hc _) hJ) (hc _),
      v.evalAt_mul hv (hc _) hJ, h0, v.evalAt_algebraMap, v.evalAt_algebraMap, v.evalAt_algebraMap,
      v.evalAt_mul hv (mul_mem (hc _) hA) hJ, v.evalAt_mul hv (hc _) hA, v.evalAt_algebraMap, h0]
  have hΦ : Φ = Φ * J * J⁻¹ := by
    field_simp
  refine ⟨?_, ?_⟩
  · rw [hΦ]; exact mul_mem hPm hJi
  · rw [hΦ, v.evalAt_mul hv hPm hJi, hPv, hJiv, h0]
    field_simp
    ring

end AlgebraicCurve.Place.RobertB

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "Place Place.residueInv_algebraMap Place.evalAt_of_mem"
namespace Place
p2m_export "AlgebraicCurve.Place" "ext ResidueField ord ord_mul ord_inv ord_coe_unit algebraMap_mem' toValuationSubring mem_of_ord_nonneg IsRational algebraMap_residueField_injective residueInv_algebraMap evalAt evalAt_of_mem algebraMap_evalAt evalAt_algebraMap evalAt_mul evalAt_inv"
namespace RobertB
p2m_open "AlgebraicCurve.Place AlgebraicCurve"

p2m_open "ModularCurve P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces.ModularCurve"

variable {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F)

theorem quotient_identity {b h g J : F} (hh : h ≠ 0) (a : K)
    (hid : b * J * (J - algebraMap K F 1728) = algebraMap K F 12 * g * J * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * h) :
    (J - algebraMap K F a) * b / h * J * (J - algebraMap K F 1728)
      = algebraMap K F 12 * ((J - algebraMap K F a) * g / h) * J * (J - algebraMap K F 1728)
        - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F a) := by
  have e1 : (J - algebraMap K F a) * b / h * J * (J - algebraMap K F 1728)
      = (J - algebraMap K F a) / h * (b * J * (J - algebraMap K F 1728)) := by ring
  rw [e1, hid]
  field_simp

theorem quotient_mem_and_evalAt_ne_zero [DecidableEq K] (hv : v.IsRational) {J A Φ : F}
    (hJ : J ∈ v.toValuationSubring) (hA : A ∈ v.toValuationSubring)
    (hJ0 : J ≠ 0) (hJ1728 : J - algebraMap K F 1728 ≠ 0)
    (hE : Φ * J * (J - algebraMap K F 1728) = algebraMap K F 12 * A * J * (J - algebraMap K F 1728)
      - algebraMap K F 2⁻¹ * (algebraMap K F 14 * J - algebraMap K F 13824) * (J - algebraMap K F (v.evalAt J)))
    (u e k : ℕ) (n : ℤ) (hAval : v.evalAt A = ((n : ℤ) : K) / ((e : ℕ) : K))
    (hhasse : (u : ℤ) * n + k * ((jWidth (v.evalAt J) : ℤ) - 1) = 1) (hue : u * e = jWidth (v.evalAt J))
    (hkK : 2 * (k : K) = -1) (heK : ((e : ℕ) : K) ≠ 0)
    (h2 : (2 : K) ≠ 0) (h12 : (12 : K) ≠ 0) (h24 : (24 : K) ≠ 0) (h1728 : (1728 : K) ≠ 0) :
    Φ ∈ v.toValuationSubring ∧ v.evalAt Φ ≠ 0 := by
  set j0 := v.evalAt J with hj0
  by_cases hz : j0 = 0
  · have hW : jWidth j0 = 3 := jWidth_of_eq_zero hz
    obtain ⟨hmem, hval⟩ := robert_quotient_zero v hv hJ hA hJ0 hE hz h1728 h2
    refine ⟨hmem, ?_⟩
    rw [hval, hAval]
    rw [hW] at hhasse hue
    have hun : ((u : ℕ) : K) * ((n : ℤ) : K) = 2 := by
      have : ((((u : ℤ) * n + k * ((3 : ℕ) - 1 : ℤ) : ℤ)) : K) = ((1 : ℤ) : K) := by rw [hhasse]
      push_cast at this
      linear_combination this - hkK
    have hueK : ((u : ℕ) : K) * ((e : ℕ) : K) = 3 := by
      have := congrArg (Nat.cast (R := K)) hue; push_cast at this; exact this
    intro h0
    have : (12 * (((n : ℤ) : K) / ((e : ℕ) : K)) - 4) * ((e : ℕ) : K) * ((u : ℕ) : K) = 0 := by
      rw [h0, zero_mul, zero_mul]
    field_simp at this
    apply h12
    linear_combination this - 12 * hun + 4 * hueK
  by_cases hsv : j0 = 1728
  · have hW : jWidth j0 = 2 := jWidth_of_eq_1728 hsv hz
    obtain ⟨hmem, hval⟩ := robert_quotient_1728 v hv hJ hA hJ1728 hE hsv h1728 h2
    refine ⟨hmem, ?_⟩
    rw [hval, hAval]
    rw [hW] at hhasse hue
    have hun : 2 * (((u : ℕ) : K) * ((n : ℤ) : K)) = 3 := by
      have : ((((u : ℤ) * n + k * ((2 : ℕ) - 1 : ℤ) : ℤ)) : K) = ((1 : ℤ) : K) := by rw [hhasse]
      push_cast at this
      linear_combination 2 * this - hkK
    have hueK : ((u : ℕ) : K) * ((e : ℕ) : K) = 2 := by
      have := congrArg (Nat.cast (R := K)) hue; push_cast at this; exact this
    intro h0
    have : (12 * (((n : ℤ) : K) / ((e : ℕ) : K)) - 3) * ((e : ℕ) : K) * ((u : ℕ) : K) * 2 = 0 := by
      rw [h0, zero_mul, zero_mul, zero_mul]
    field_simp at this
    apply h24
    linear_combination this - 12 * hun + 6 * hueK
  · have hW : jWidth j0 = 1 := jWidth_of_ne hz hsv
    obtain ⟨hmem, hval⟩ := robert_quotient_generic v hv hJ hA hE hz hsv
    refine ⟨hmem, ?_⟩
    rw [hval, hAval]
    rw [hW] at hhasse hue
    have hun : ((u : ℕ) : K) * ((n : ℤ) : K) = 1 := by
      have : ((((u : ℤ) * n + k * ((1 : ℕ) - 1 : ℤ) : ℤ)) : K) = ((1 : ℤ) : K) := by rw [hhasse]
      push_cast at this
      linear_combination this
    intro h0
    have : (12 * (((n : ℤ) : K) / ((e : ℕ) : K))) * ((e : ℕ) : K) * ((u : ℕ) : K) = 0 := by
      rw [h0, zero_mul, zero_mul]
    field_simp at this
    apply h12
    linear_combination this - 12 * hun

end AlgebraicCurve.Place.RobertB

namespace ModularCurve
p2m_export "ModularCurve" "placeRamificationJ placeWidth IsSupersingularPlace ssPlaces jGeomGen coe_jGeomGen jGeomGen_sub_algebraMap_ne_zero IsAffineGeomPlace ord_sub_evalAt_pos_of_isRational jqModC modularFunctionFieldC coeff_jqModC_neg_one jWidth jWidth_of_eq_zero jWidth_of_eq_1728 jWidth_of_ne jWidth_pos jWidth_eq_one_or thetaL thetaL_apply stackOrd exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq qP_mul_thetaL_jqModC_zpow_mul_eq thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC placeRamificationJ_dvd_jWidth_of_mem_ssPlaces jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div"
namespace RobertB
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces.AlgebraicCurve"

section Laurent
variable {L : Type*} [Field L]

theorem coeff_thetaL_eq_mul (f : LaurentSeries L) (n : ℤ) :
    (thetaL L f).coeff n = (n : L) * f.coeff n := by
  rw [thetaL_apply, LaurentSeries.derivative_apply, HahnSeries.coeff_single_mul, one_mul,
    LaurentSeries.hasseDeriv_coeff, Nat.cast_one, sub_add_cancel, Ring.choose_one_right, zsmul_eq_mul]

theorem thetaL_jqModC_ne_zero : thetaL L (jqModC L) ≠ 0 := by
  intro h
  have hc := congrArg (fun s : LaurentSeries L => s.coeff (-1)) h
  simp only [coeff_thetaL_eq_mul, coeff_jqModC_neg_one] at hc
  simp at hc

theorem C_eq_algebraMap (c : L) : (HahnSeries.C c : LaurentSeries L) = algebraMap L (LaurentSeries L) c := by
  rw [HahnSeries.algebraMap_apply']
  simp

theorem ofPowerSeries_qP_ne_zero (K : Type) [Field K] :
    HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) ≠ 0 := by
  intro h
  have h0 := congrArg (fun s : LaurentSeries K => s.coeff ((0 : ℕ) : ℤ)) h
  simp only [HahnSeries.ofPowerSeries_apply_coeff, SwdAlgebra.qP, PowerSeries.coeff_map, PowerSeries.coeff_mk,
    if_true] at h0
  simp at h0

end Laurent

section Numerals
variable (p : ℕ) [hp : Fact p.Prime] (K : Type*) [Field K] [CharP K p]

theorem natCast_two_pow_mul_three_pow_ne_zero (hp5 : 5 ≤ p) (a b : ℕ) : ((2 ^ a * 3 ^ b : ℕ) : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  rcases (Nat.Prime.dvd_mul hp.out).mp h with h2 | h3
  · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h2); omega
  · have := Nat.le_of_dvd (by norm_num) (hp.out.dvd_of_dvd_pow h3); omega

theorem two_ne_zero' (hp5 : 5 ≤ p) : (2 : K) ≠ 0 := by
  simpa using natCast_two_pow_mul_three_pow_ne_zero p K hp5 1 0
theorem twelve_ne_zero (hp5 : 5 ≤ p) : (12 : K) ≠ 0 := by
  have := natCast_two_pow_mul_three_pow_ne_zero p K hp5 2 1; norm_num at this; exact this
theorem twentyfour_ne_zero (hp5 : 5 ≤ p) : (24 : K) ≠ 0 := by
  have := natCast_two_pow_mul_three_pow_ne_zero p K hp5 3 1; norm_num at this; exact this
theorem ofNat1728_ne_zero (hp5 : 5 ≤ p) : (1728 : K) ≠ 0 := by
  have := natCast_two_pow_mul_three_pow_ne_zero p K hp5 6 3; norm_num at this; exact this

omit hp in

theorem natCast_ne_zero_of_lt {n : ℕ} (h0 : 0 < n) (hn : n < p) : (n : K) ≠ 0 := by
  intro h
  rw [CharP.cast_eq_zero_iff K p] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

end Numerals

section Field
variable (p : ℕ) [Fact p.Prime] (K : Type) [Field K] [CharP K p] (N : ℕ) [NeZero N]

theorem robert_identity (hp5 : 5 ≤ p) (b h g : ↥(modularFunctionFieldC K N))
    (hb : (b : LaurentSeries K) = HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)))
    (hh : (h : LaurentSeries K) = thetaL K (jqModC K) ^ (-(((p : ℤ) - 1) / 2)))
    (hg : (g : LaurentSeries K) = thetaL K (h : LaurentSeries K) / thetaL K (jqModC K)) :
    b * jGeomGen K N * (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 1728) =
      algebraMap K (modularFunctionFieldC K N) 12 * g * jGeomGen K N
          * (jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 1728)
        - algebraMap K (modularFunctionFieldC K N) 2⁻¹
          * (algebraMap K (modularFunctionFieldC K N) 14 * jGeomGen K N - algebraMap K (modularFunctionFieldC K N) 13824)
          * h := by
  have hθ := thetaL_jqModC_ne_zero (L := K)
  have face := qP_mul_thetaL_jqModC_zpow_mul_eq p hp5 K
  rw [← hb, ← hh] at face
  have hgθ : thetaL K (h : LaurentSeries K) = (g : LaurentSeries K) * thetaL K (jqModC K) := by
    rw [hg, div_mul_cancel₀ _ hθ]
  rw [hgθ, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul, ← HahnSeries.C_mul_eq_smul,
    C_eq_algebraMap, C_eq_algebraMap, C_eq_algebraMap,
    ← map_ofNat (algebraMap K (LaurentSeries K)) 1728, ← map_ofNat (algebraMap K (LaurentSeries K)) 13824] at face
  apply Subtype.ext
  simp only [IntermediateField.coe_mul, AddSubgroupClass.coe_sub, coe_jGeomGen]
  apply mul_left_cancel₀ hθ
  linear_combination face

variable {K N}

theorem natCast_placeRamificationJ {x : Place K ↥(modularFunctionFieldC K N)} (hrat : x.IsRational)
    (haff : IsAffineGeomPlace K N x) :
    (placeRamificationJ N x : ℤ) = x.ord (jGeomGen K N -
      algebraMap K ↥(modularFunctionFieldC K N) (x.evalAt (jGeomGen K N))) := by
  unfold placeRamificationJ
  exact Int.toNat_of_nonneg (ord_sub_evalAt_pos_of_isRational hrat haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N _)).le

theorem placeRamificationJ_pos {x : Place K ↥(modularFunctionFieldC K N)} (hrat : x.IsRational)
    (haff : IsAffineGeomPlace K N x) : 0 < placeRamificationJ N x := by
  have h := ord_sub_evalAt_pos_of_isRational hrat haff.1
    (jGeomGen_sub_algebraMap_ne_zero K N (x.evalAt (jGeomGen K N)))
  have h2 := natCast_placeRamificationJ hrat haff
  omega

end Field

end ModularCurve.RobertB

open ModularCurve.RobertB AlgebraicCurve.Place.RobertB in
theorem solution
    (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (N : ℕ) [NeZero N] (hpN : ¬ p ∣ N)
    (K : Type) [Field K] [CharP K p] [IsAlgClosed K] [DecidableEq K]
    (hb : HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) ∈
      modularFunctionFieldC K N)
    (x : Place K (modularFunctionFieldC K N)) (hx : IsAffineGeomPlace K N x) (hss : x ∈ ssPlaces p N K) :
    stackOrd N (((p : ℤ) + 1) / 2)
      ⟨HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)), hb⟩ x = 0 := by
  have hprime : p.Prime := Fact.out

  obtain ⟨h, hh, hstack, -⟩ := exists_coe_eq_thetaL_jqModC_zpow_and_stackOrd_eq p hp5 N hpN K
  have hhasse : stackOrd N (((p : ℤ) - 1) / 2) h x = 1 := (hstack x hx).1 hss

  set b : ↥(modularFunctionFieldC K N) :=
    ⟨HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)), hb⟩ with hbdef
  have hbcoe : (b : LaurentSeries K) =
      HahnSeries.ofPowerSeries ℤ K (SwdAlgebra.qP K) * thetaL K (jqModC K) ^ (-(((p : ℤ) + 1) / 2)) := rfl
  have hgmem := thetaL_div_thetaL_jqModC_mem_modularFunctionFieldC K p N hpN (h : LaurentSeries K) h.2
  set g : ↥(modularFunctionFieldC K N) := ⟨_, hgmem⟩ with hgdef
  have hgcoe : (g : LaurentSeries K) = thetaL K (h : LaurentSeries K) / thetaL K (jqModC K) := rfl

  have hθ := thetaL_jqModC_ne_zero (L := K)
  have hh0 : h ≠ 0 := by
    intro h0
    have : (h : LaurentSeries K) = 0 := by rw [h0, ZeroMemClass.coe_zero]
    rw [hh] at this
    exact zpow_ne_zero _ hθ this
  have hb0 : b ≠ 0 := by
    intro h0
    have : (b : LaurentSeries K) = 0 := by rw [h0, ZeroMemClass.coe_zero]
    rw [hbcoe] at this
    exact mul_ne_zero (ofPowerSeries_qP_ne_zero K) (zpow_ne_zero _ hθ) this

  have hss' : IsSupersingularPlace p N K x := hss
  have hxr : x.IsRational := hss'.1
  have hJmem : jGeomGen K N ∈ x.toValuationSubring := hx.1
  have hJc0 : jGeomGen K N - algebraMap K _ (x.evalAt (jGeomGen K N)) ≠ 0 := jGeomGen_sub_algebraMap_ne_zero K N _
  have hJ0 : jGeomGen K N ≠ 0 := by
    have := jGeomGen_sub_algebraMap_ne_zero K N 0; rwa [map_zero, sub_zero] at this
  have hecast := natCast_placeRamificationJ (N := N) hxr hx
  have hepos : 0 < placeRamificationJ N x := placeRamificationJ_pos hxr hx
  have hdvd : placeRamificationJ N x ∣ jWidth (x.evalAt (jGeomGen K N)) :=
    placeRamificationJ_dvd_jWidth_of_mem_ssPlaces hp5 hpN hss
  have hue : placeWidth N x * placeRamificationJ N x = jWidth (x.evalAt (jGeomGen K N)) := by
    unfold placeWidth; exact Nat.div_mul_cancel hdvd
  have hw3 : jWidth (x.evalAt (jGeomGen K N)) ≤ 3 := by
    rcases jWidth_eq_one_or (x.evalAt (jGeomGen K N)) with h1 | h2 | h3 <;> omega
  have he3 : placeRamificationJ N x ≤ 3 := (Nat.le_of_dvd (jWidth_pos _) hdvd).trans hw3
  have hupos : 0 < placeWidth N x := by
    rcases Nat.eq_zero_or_pos (placeWidth N x) with h0 | h0
    · rw [h0, zero_mul] at hue; exact absurd hue.symm (jWidth_pos _).ne'
    · exact h0
  have hu3 : placeWidth N x ≤ 3 := by
    have : placeWidth N x ≤ placeWidth N x * placeRamificationJ N x := Nat.le_mul_of_pos_right _ hepos
    omega
  have heK : ((placeRamificationJ N x : ℕ) : K) ≠ 0 := natCast_ne_zero_of_lt p K hepos (by omega)

  obtain ⟨k, hk⟩ : ∃ k, p = 2 * k + 1 := by
    rcases hprime.eq_two_or_odd' with h2 | hodd
    · omega
    · exact hodd
  have hm : ((p : ℤ) - 1) / 2 = k := by omega
  have hm' : ((p : ℤ) + 1) / 2 = k + 1 := by omega
  have hkK : 2 * (k : K) = -1 := by
    have : ((2 * k + 1 : ℕ) : K) = 0 := by rw [← hk]; exact CharP.cast_eq_zero K p
    push_cast at this
    linear_combination this

  have hhasseZ : (placeWidth N x : ℤ) * x.ord h + k * ((jWidth (x.evalAt (jGeomGen K N)) : ℤ) - 1) = 1 := by
    rw [← hm]; unfold stackOrd at hhasse; exact hhasse

  obtain ⟨hAmem, hAval⟩ := jGeomGen_sub_mul_div_mem_and_evalAt_eq_of_coe_eq_thetaL_div p hp5 N hpN K x hxr hx
    h g hh0 hgcoe
  have hE := quotient_identity hh0 (x.evalAt (jGeomGen K N)) (robert_identity p K N hp5 b h g hbcoe hh hgcoe)

  obtain ⟨hΦmem, hΦne⟩ := quotient_mem_and_evalAt_ne_zero x hxr hJmem hAmem hJ0
    (jGeomGen_sub_algebraMap_ne_zero K N 1728) hE (placeWidth N x) (placeRamificationJ N x) k (x.ord h) hAval
    hhasseZ hue hkK heK (two_ne_zero' p K hp5) (twelve_ne_zero p K hp5) (twentyfour_ne_zero p K hp5)
    (ofNat1728_ne_zero p K hp5)
  obtain ⟨-, hordΦ⟩ := ne_zero_and_ord_eq_zero_of_evalAt_ne_zero x hΦmem hΦne

  have hordb : x.ord b = x.ord h - (placeRamificationJ N x : ℤ) := by
    rw [ord_div x (mul_ne_zero hJc0 hb0) hh0, x.ord_mul hJc0 hb0, ← hecast] at hordΦ
    linarith

  have hueZ : (placeWidth N x : ℤ) * (placeRamificationJ N x : ℤ) = (jWidth (x.evalAt (jGeomGen K N)) : ℤ) := by
    exact_mod_cast hue
  unfold stackOrd
  rw [hm', hordb]
  linear_combination hhasseZ - hueZ

end S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces
end P2MW
export P2MW.S_ModularCurve_stackOrd_qP_mul_thetaL_jqModC_zpow_eq_zero_of_mem_ssPlaces (solution)
