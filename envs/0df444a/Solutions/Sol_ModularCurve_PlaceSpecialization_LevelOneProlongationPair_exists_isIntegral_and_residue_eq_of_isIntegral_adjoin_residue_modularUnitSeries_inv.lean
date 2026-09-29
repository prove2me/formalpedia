-- Prove2me | solution 1 for ModularCurve.PlaceSpecialization.LevelOneProlongationPair.exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/d4ac10db-6fd3-565b-ae65-af036e1b7e1c

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_ModularUnit
import Theorems.Thm_ModularCurve_modularUnitSeries_mem_modularFunctionFieldFull
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_X_sub_C
import Theorems.Thm_ModularCurve_finrank_adjoin_coeffEmb_modularUnitSeries_inv
import Theorems.Thm_ModularCurve_hasPrincipalDivisors_modularFunctionFieldBar_unconditional
import Theorems.Thm_ModularCurve_isCusp_iff_ord_neg
import Theorems.Thm_ModularCurve_eq_cuspInftyBar_or_eq_cuspZeroBar
import Theorems.Thm_ModularCurve_isCusp_cuspInftyBar
import Theorems.Thm_ModularCurve_isCusp_cuspZeroBar
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_cuspZeroBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_ord_coeffEmb_modularUnitSeries_of_not_isCusp
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_jq
import Theorems.Thm_ModularCurve_ord_cuspInftyBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_frickeInvolutionBar_frickeInvolutionBar
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_AlgebraicCurve_isIntegral_adjoin_of_forall_ord_nonneg
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver"
p2m_attr_erase "simp" "AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄ ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero"
p2m_attr_erase "simp" "TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec"
p2m_attr_erase "simp" "EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "HahnSeries ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace N1Glue
p2m_open "ModularCurve~coeffMap_injective"

theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (N : ℕ) [NeZero N]
    (x : LaurentSeries R) : coeffMap f (qExpand R N x) = qExpand S N (coeffMap f x) := by
  ext n
  rw [coeffMap_coeff]
  by_cases hdvd : (N : ℤ) ∣ n
  · obtain ⟨k, rfl⟩ := hdvd
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [qExpand_coeff_of_not_dvd N _ hdvd, qExpand_coeff_of_not_dvd N _ hdvd, map_zero]

theorem coeffMap_ofPowerSeries {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (u : PowerSeries R) :
    coeffMap f (ofPowerSeries ℤ R u) = ofPowerSeries ℤ S (PowerSeries.map f u) := by
  ext n
  rw [coeffMap_coeff]
  rcases lt_or_ge n 0 with hn | hn
  · rw [ofPowerSeries_coeff_of_neg _ hn, ofPowerSeries_coeff_of_neg _ hn, map_zero]
  · obtain ⟨k, hk⟩ := Int.le.dest hn
    rw [show n = (k : ℤ) by omega, HahnSeries.ofPowerSeries_apply_coeff, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_map]

theorem coeffMap_injective {R S : Type*} [CommRing R] [CommRing S] {f : R →+* S} (hf : Function.Injective f) :
    Function.Injective (coeffMap f) := by
  intro x y h
  ext n
  exact hf (by rw [← coeffMap_coeff, ← coeffMap_coeff, h])

def deltaSeriesZ : LaurentSeries ℤ :=
  HahnSeries.single (1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit

def deltaSeriesZInv : LaurentSeries ℤ :=
  HahnSeries.single (-1 : ℤ) 1 * HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv

theorem deltaSeriesZ_mul_inv : deltaSeriesZ * deltaSeriesZInv = 1 := by
  have hη : HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnit *
      HahnSeries.ofPowerSeries ℤ ℤ dedekindEtaUnitInv = 1 := by
    rw [← map_mul, dedekindEtaUnit_mul_inv]; exact map_one _
  have hs : (HahnSeries.single (1 : ℤ) 1 * HahnSeries.single (-1 : ℤ) 1 : LaurentSeries ℤ) = 1 := by
    rw [HahnSeries.single_mul_single, add_neg_cancel, one_mul]; rfl
  unfold deltaSeriesZ deltaSeriesZInv
  rw [mul_mul_mul_comm, hs, hη, one_mul]

def modularUnitSeriesZ (p : ℕ) [NeZero p] : LaurentSeries ℤ :=
  deltaSeriesZ * qExpand ℤ p deltaSeriesZInv

theorem coeffMap_rat_deltaSeriesZ : coeffMap (Int.castRingHom ℚ) deltaSeriesZ = deltaSeries := by
  rw [deltaSeriesZ, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries]
  rfl

theorem coeffMap_rat_modularUnitSeriesZ (p : ℕ) [NeZero p] :
    coeffMap (Int.castRingHom ℚ) (modularUnitSeriesZ p) = modularUnitSeries p := by
  have h1 : coeffMap (Int.castRingHom ℚ) (qExpand ℤ p deltaSeriesZ) = deltaSeriesN p := by
    rw [coeffMap_qExpand', coeffMap_rat_deltaSeriesZ]; rfl
  have hinv : coeffMap (Int.castRingHom ℚ) (qExpand ℤ p deltaSeriesZInv) * deltaSeriesN p = 1 := by
    rw [← h1, ← map_mul, ← map_mul, mul_comm, deltaSeriesZ_mul_inv, map_one, map_one]
  rw [modularUnitSeriesZ, map_mul, coeffMap_rat_deltaSeriesZ, modularUnitSeries,
    ← one_mul (deltaSeriesN p)⁻¹, ← hinv, mul_assoc,
    mul_inv_cancel₀ (deltaSeriesN_ne_zero p), mul_one, mul_comm]

theorem coeffEmb_modularUnitSeries_eq (L : Type*) [Field L] [Algebra ℚ L] (p : ℕ) [NeZero p] :
    coeffEmb L (modularUnitSeries p) = coeffMap (Int.castRingHom L) (modularUnitSeriesZ p) := by
  rw [← coeffMap_rat_modularUnitSeriesZ, coeffEmb, coeffMap_coeffMap]
  exact coeffMap_congr (RingHom.ext_int _ _) _

theorem coeffMap_deltaSeriesZ (K : Type*) [CommRing K] :
    coeffMap (Int.castRingHom K) deltaSeriesZ
      = ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) := by
  rw [deltaSeriesZ, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries, map_mul, PowerSeries.map_X, map_mul,
    HahnSeries.ofPowerSeries_X]

theorem deltaBar_ne_zero (K : Type*) [CommRing K] [Nontrivial K] :
    ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) ≠ 0 := by
  rw [← coeffMap_deltaSeriesZ]
  intro h
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff 1) h
  simp only [coeffMap_coeff, deltaSeriesZ, HahnSeries.coeff_single_mul, one_mul, sub_self,
    HahnSeries.coeff_zero] at h1
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, constantCoeff_dedekindEtaUnit, map_one] at h1
  exact one_ne_zero h1

theorem coeffMap_intCast_modularUnitSeriesZ (K : Type*) [Field K] (p ℓ : ℕ) [NeZero p] [Fact ℓ.Prime] [CharP K ℓ]
    (hp : p = ℓ) :
    coeffMap (Int.castRingHom K) (modularUnitSeriesZ p)
      = ((ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit))) ^ (ℓ - 1))⁻¹ := by
  subst hp
  set Δ := ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) with hΔdef
  have hΔ : coeffMap (Int.castRingHom K) deltaSeriesZ = Δ := coeffMap_deltaSeriesZ K
  have hΔ0 : Δ ≠ 0 := deltaBar_ne_zero K
  have hinv : coeffMap (Int.castRingHom K) deltaSeriesZInv = Δ⁻¹ := by
    have h1 : Δ * coeffMap (Int.castRingHom K) deltaSeriesZInv = 1 := by
      rw [← hΔ, ← map_mul, deltaSeriesZ_mul_inv, map_one]
    exact eq_inv_of_mul_eq_one_right h1
  have hfrob : qExpand K p Δ = Δ ^ p := by
    rw [← hΔ]
    exact (map_intCast_pow_char_eq_qExpand p deltaSeriesZ).symm
  have hpow : Δ ^ p = Δ * Δ ^ (p - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le]
  rw [modularUnitSeriesZ, map_mul, hΔ, coeffMap_qExpand', hinv, map_inv₀, hfrob, hpow, mul_inv, ← mul_assoc,
    mul_inv_cancel₀ hΔ0, one_mul]

end ModularCurve.N1Glue

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace N1Glue
p2m_open "ModularCurve~coeffMap_injective"

open Polynomial

theorem coeffMap_deltaSeriesZInv (K : Type*) [Field K] :
    coeffMap (Int.castRingHom K) deltaSeriesZInv
      = (ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)))⁻¹ := by
  have h1 : ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)) *
      coeffMap (Int.castRingHom K) deltaSeriesZInv = 1 := by
    rw [← coeffMap_deltaSeriesZ, ← map_mul, deltaSeriesZ_mul_inv, map_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem map_eisenstein4_eq_one (K : Type*) [CommRing K] (h240 : ((240 : ℤ) : K) = 0) :
    PowerSeries.map (Int.castRingHom K) eisenstein4 = 1 := by
  ext n
  rw [PowerSeries.coeff_map, eisenstein4, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  split_ifs with hn
  · exact map_one _
  · rw [map_mul, eq_intCast, h240, zero_mul]

theorem jqModC_eq_deltaBar_inv (K : Type*) [Field K] (h240 : ((240 : ℤ) : K) = 0) :
    jqModC K = (ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit)))⁻¹ := by
  rw [← coeffMap_deltaSeriesZInv, deltaSeriesZInv, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries,
    jqModC, jNum, map_mul, map_pow, map_eisenstein4_eq_one K h240, one_pow, one_mul]

section JqModCPow
variable (K : Type*) [CommRing K]

theorem jqModC_pow' (n : ℕ) :
    (jqModC K) ^ n = HahnSeries.single (-(n : ℤ)) 1 *
      HahnSeries.ofPowerSeries ℤ K ((jNum.map (Int.castRingHom K)) ^ n) := by
  have h : n • (-1 : ℤ) = -(n : ℤ) := by simp
  rw [jqModC, mul_pow, HahnSeries.single_pow, one_pow, h, ← map_pow]

theorem constantCoeff_jNum_map' : PowerSeries.constantCoeff (jNum.map (Int.castRingHom K)) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_map, PowerSeries.coeff_zero_eq_constantCoeff,
    constantCoeff_jNum, map_one]

theorem coeff_jqModC_pow_self' (n : ℕ) : ((jqModC K) ^ n).coeff (-(n : ℤ)) = 1 := by
  rw [jqModC_pow', HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add, neg_add_cancel,
    show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, HahnSeries.ofPowerSeries_apply_coeff,
    PowerSeries.coeff_zero_eq_constantCoeff, map_pow, constantCoeff_jNum_map', one_pow]

theorem coeff_jqModC_pow_of_lt' {n : ℕ} {m : ℤ} (hm : m < -(n : ℤ)) : ((jqModC K) ^ n).coeff m = 0 := by
  rw [jqModC_pow', HahnSeries.coeff_single_mul, one_mul]
  exact ofPowerSeries_coeff_of_neg _ (by omega)

end JqModCPow

theorem coeff_aeval_jqModC_neg_natDegree (K : Type*) [Field K] (P : K[X]) :
    (aeval (jqModC K) P).coeff (-(P.natDegree : ℤ)) = P.leadingCoeff := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum,
    Finset.sum_eq_single P.natDegree]
  · rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jqModC_pow_self', mul_one,
      Polynomial.coeff_natDegree]
  · intro i hi hin
    have hilt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hin
    rw [algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_zero_mul, coeff_jqModC_pow_of_lt', mul_zero]
    omega
  · intro hn'
    exact absurd (Finset.self_mem_range_succ _) hn'

theorem exists_monic_deltaBar_pow_inv_eq_aeval (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] [CharP K q]
    [IsAlgClosed K] [DecidableEq K] :
    ∃ P : K[X], P.Monic ∧ (∀ b : K, P.IsRoot b → b ∈ ssJSet q K) ∧
      ((ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹
        = aeval (jqModC K) P := by
  by_cases hq : 5 ≤ q
  · obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset K, ∀ a, a ∈ S₀ ↔ a ∈ ssJSet q K :=
      ⟨(ssJSet_finite q K).toFinset, fun a => Set.Finite.mem_toFinset _⟩
    have hid := delta_pow_mul_prod_jqModC_sub_pow_eq_one q hq K S₀ hS₀
    refine ⟨∏ a ∈ S₀, (X - Polynomial.C a) ^ (12 / jWidth a), ?_, ?_, ?_⟩
    · exact monic_prod_of_monic _ _ fun a _ => (monic_X_sub_C a).pow _
    · intro b hb
      rw [IsRoot.def, eval_prod, Finset.prod_eq_zero_iff] at hb
      obtain ⟨a, ha, h0⟩ := hb
      rw [eval_pow, eval_sub, eval_X, eval_C] at h0
      have hn : 12 / jWidth a ≠ 0 := by
        rcases jWidth_eq_one_or a with h | h | h <;> simp [h]
      have hba : b = a := sub_eq_zero.mp ((pow_eq_zero_iff hn).mp h0)
      rw [hba]; exact (hS₀ a).mp ha
    · have e : aeval (jqModC K) (∏ a ∈ S₀, (X - Polynomial.C a) ^ (12 / jWidth a))
          = ∏ a ∈ S₀, (jqModC K - HahnSeries.C a) ^ (12 / jWidth a) := by
        rw [map_prod]
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [map_pow, map_sub, aeval_X, aeval_C, algebraMap_laurentSeries_eq_single]
        rfl
      rw [e]
      exact (eq_inv_of_mul_eq_one_right hid).symm
  · have hq2 := (Fact.out : q.Prime).two_le
    have hlt : q < 5 := not_le.mp hq
    have hdvd : q ∣ 240 := by interval_cases q <;> norm_num
    have h240 : ((240 : ℤ) : K) = 0 := by exact_mod_cast (CharP.cast_eq_zero_iff K q 240).mpr hdvd
    refine ⟨X ^ (q - 1), monic_X_pow _, ?_, ?_⟩
    · intro b hb
      rw [IsRoot.def, eval_pow, eval_X] at hb
      rw [(pow_eq_zero_iff (by omega)).mp hb]
      exact zero_mem_ssJSet_of_lt_five hlt
    · rw [map_pow, aeval_X, jqModC_eq_deltaBar_inv K h240, inv_pow]

theorem natDegree_le_of_deltaBar_pow_inv_eq_aeval (q : ℕ) (K : Type*) [Field K] (P : K[X]) (hP : P.Monic)
    (h : ((ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹
        = aeval (jqModC K) P) :
    P.natDegree ≤ q - 1 := by
  by_contra hlt
  rw [not_le] at hlt
  have hc := coeff_aeval_jqModC_neg_natDegree K P
  rw [hP.leadingCoeff, ← h, ← inv_pow, ← coeffMap_deltaSeriesZInv, ← map_pow, deltaSeriesZInv, mul_pow,
    HahnSeries.single_pow, one_pow, ← map_pow, map_mul, coeffMap_single, map_one, coeffMap_ofPowerSeries,
    HahnSeries.coeff_single_mul, one_mul, ofPowerSeries_coeff_of_neg] at hc
  · exact zero_ne_one hc
  · simp only [smul_neg, nsmul_eq_mul, mul_one]
    omega

end ModularCurve.N1Glue

section N1RFsec
open Polynomial
namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace N1RF
p2m_open "ModularCurve~coeffMap_injective"

variable {K : Type*} [Field K]

noncomputable def clearCoeff (P : K[X]) (d : ℕ) (b : K[X]) : K[X] :=
  ∑ k ∈ Finset.range (d + 1), Polynomial.C (b.coeff k) * P ^ (d - k)

theorem natDegree_clearCoeff_le (P : K[X]) (d : ℕ) (b : K[X]) :
    (clearCoeff P d b).natDegree ≤ d * P.natDegree := by
  unfold clearCoeff
  refine natDegree_sum_le_of_forall_le _ _ fun k _ => ?_
  refine (natDegree_C_mul_le _ _).trans ?_
  refine natDegree_pow_le.trans ?_
  exact Nat.mul_le_mul_right _ (Nat.sub_le d k)

theorem aeval_inv_mul_pow_eq_clearCoeff (P : K[X]) (hP : P ≠ 0) (d : ℕ) (b : K[X]) (hb : b.natDegree ≤ d) :
    aeval ((algebraMap K[X] (RatFunc K) P)⁻¹) b * (algebraMap K[X] (RatFunc K) P) ^ d
      = algebraMap K[X] (RatFunc K) (clearCoeff P d b) := by
  set ιP := algebraMap K[X] (RatFunc K) P with hιP
  have hιP0 : ιP ≠ 0 := by
    rw [hιP]; exact (map_ne_zero_iff _ (IsFractionRing.injective K[X] (RatFunc K))).mpr hP
  rw [aeval_eq_sum_range' (Nat.lt_succ_of_le hb), Finset.sum_mul, clearCoeff, map_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  rw [map_mul, map_pow, ← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply, Algebra.smul_def,
    mul_assoc]
  congr 1
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkd
  rw [Nat.add_sub_cancel_left, _root_.pow_add, inv_pow, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hιP0), one_mul]

theorem exists_eq_pow_mul_of_aeval_inv (P : K[X]) (hP : P ≠ 0) (r : RatFunc K) (n d : ℕ) (b : Fin n → K[X])
    (hb : ∀ i, (b i).natDegree ≤ d)
    (H : r ^ n + ∑ i : Fin n, aeval ((algebraMap K[X] (RatFunc K) P)⁻¹) (b i) * r ^ (i : ℕ) = 0) :
    ∃ g : K[X], g.natDegree ≤ d * P.natDegree ∧
      algebraMap K[X] (RatFunc K) g = (algebraMap K[X] (RatFunc K) P) ^ d * r := by
  classical
  set ι := algebraMap K[X] (RatFunc K) with hι
  have hιinj : Function.Injective ι := IsFractionRing.injective K[X] (RatFunc K)

  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · subst hn0
    simp at H
  set s := ι P ^ d * r with hs

  let m : Fin n → ℕ := fun i => n - 1 - i
  have hm : ∀ i : Fin n, n = (i : ℕ) + m i + 1 := fun i => by have := i.2; simp only [m]; omega
  let a : Fin n → K[X] := fun i => clearCoeff P d (b i) * P ^ (d * m i)
  have ha_deg : ∀ i, (a i).natDegree ≤ d * (n - i) * P.natDegree := by
    intro i
    refine (natDegree_mul_le).trans ?_
    refine (Nat.add_le_add (natDegree_clearCoeff_le P d (b i)) natDegree_pow_le).trans ?_
    have : n - i = m i + 1 := by have := hm i; omega
    rw [this]
    nlinarith

  have hs_eq : s ^ n + ∑ i : Fin n, ι (a i) * s ^ (i : ℕ) = 0 := by
    have key : ∀ i : Fin n, ι (a i) * s ^ (i : ℕ) = ι P ^ (d * n) * (aeval (ι P)⁻¹ (b i) * r ^ (i : ℕ)) := by
      intro i
      simp only [a, hs]
      rw [map_mul, ← aeval_inv_mul_pow_eq_clearCoeff P hP d (b i) (hb i), map_pow, mul_pow, ← pow_mul]
      have e : d * n = d + d * m i + d * (i : ℕ) := by
        conv_lhs => rw [hm i]
        ring
      rw [e, _root_.pow_add, _root_.pow_add]
      ring
    have h2 : s ^ n = ι P ^ (d * n) * r ^ n := by rw [hs, mul_pow, ← pow_mul]
    rw [h2, Finset.sum_congr rfl fun i _ => key i, ← Finset.mul_sum, ← mul_add, H, mul_zero]

  have hint : IsIntegral K[X] s := by
    refine ⟨X ^ n + ∑ i : Fin n, Polynomial.C (a i) * X ^ (i : ℕ), ?_, ?_⟩
    · exact monic_X_pow_add ((degree_sum_fin_lt a).trans_le le_rfl)
    · rw [eval₂_add, eval₂_X_pow, eval₂_finset_sum]
      simp only [eval₂_mul, eval₂_C, eval₂_X_pow]
      exact hs_eq
  obtain ⟨g, hg⟩ := (IsIntegrallyClosed.isIntegral_iff (R := K[X]) (K := RatFunc K)).mp hint
  refine ⟨g, ?_, hg⟩

  have hgeq : g ^ n + ∑ i : Fin n, a i * g ^ (i : ℕ) = 0 := by
    apply hιinj
    rw [map_add, map_pow, map_sum, map_zero]
    simp only [map_mul, map_pow]
    rw [hg]; exact hs_eq
  by_contra hlt
  rw [not_le] at hlt
  have hg0 : g ≠ 0 := by rintro rfl; simp at hlt
  set D := g.natDegree with hD
  set e := d * P.natDegree with he
  have hpow : (g ^ n).natDegree = n * D := by rw [natDegree_pow]
  have hsum : (∑ i : Fin n, a i * g ^ (i : ℕ)).natDegree ≤ n * D - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    refine natDegree_mul_le.trans ?_
    refine (Nat.add_le_add (ha_deg i) natDegree_pow_le).trans ?_
    rw [← hD]
    have hk : 1 ≤ n - (i : ℕ) := by have := i.2; omega
    have hn' : (n - (i : ℕ)) + (i : ℕ) = n := by have := i.2; omega
    set k := n - (i : ℕ) with hkdef

    have h1 : d * k * P.natDegree = k * e := by rw [he]; ring
    rw [h1]
    have h2 : k * e + (i : ℕ) * D + 1 ≤ (k + (i : ℕ)) * D := by
      nlinarith [Nat.mul_le_mul_left k (Nat.succ_le_of_lt hlt), hk]
    rw [hn'] at h2
    omega
  have hnD : 1 ≤ n * D := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero hn.ne' (by omega))
  have : (g ^ n).natDegree ≤ n * D - 1 := by
    have e2 : g ^ n = -∑ i : Fin n, a i * g ^ (i : ℕ) := eq_neg_of_add_eq_zero_left hgeq
    rw [e2, natDegree_neg]
    exact hsum
  omega

end ModularCurve.N1RF

end N1RFsec

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
p2m_open "ModularCurve~coeffMap_injective"

private theorem pinN_ratFuncEquivCharLOneC_X (k : Type*) [Field k] :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

private theorem pinN_ord_charLGeomPlaceEquiv (k : Type*) [Field k] (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_coeffMap redBar ι_coe ι R₁ coeffEmb_modularUnitSeries_mem_integersFst"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

noncomputable def uFun : ↥(modularFunctionFieldBar (1 * q)) :=
  ⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
    coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
      (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩

def UInvFinite (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) : Prop :=
  ∃ a : A, ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))
      - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ W.toValuationSubring.nonunits

private def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.ReducesOnUInvChart (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)) : Prop :=
  ∀ h : R.R₁.integers,
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))}) (h : ↥(modularFunctionFieldBar (1 * q))) →
    ∀ a : A, (h : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)
        ∈ W.toValuationSubring.nonunits →
      R.R₁.residue h - algebraMap (ResidueField A) _ (IsLocalRing.residue A a) ∈ Q.toValuationSubring.nonunits

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "ReducesOnUInvChart"
set_option maxHeartbeats 16000000 in

theorem residue_sub_mem_nonunits_of_reducesOnUInvChart
    (hu : (uFun (q := q)) ∈ R.R₁.integers) (hu' : (uFun (q := q))⁻¹ ∈ R.R₁.integers)
    (hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (hfin : UInvFinite (A := A) W) (hred : R.ReducesOnUInvChart W Q)
    (hūQ : Q.ord (R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) = 0)
    (h : ↥(modularFunctionFieldBar (1 * q))) (hh : h ∈ R.R₁.integers) (m : ℕ)
    (hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      (h * ((uFun (q := q))⁻¹) ^ m))
    (c : A) (hc : h - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring.nonunits) :
    R.R₁.residue ⟨h, hh⟩ - algebraMap (ResidueField A) _ (IsLocalRing.residue A c) ∈ Q.toValuationSubring.nonunits := by
  classical
  obtain ⟨a₀, ha₀⟩ := hfin
  have hu_ne : (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
    intro h0
    apply hu0
    have hz : (⟨uFun, hu⟩ : R.R₁.integers) = 0 := Subtype.ext h0
    rw [hz, map_zero]
  have hconst_eq : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c * a₀ ^ m : A) : AlgebraicClosure ℚ)
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ)
        * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a₀ : AlgebraicClosure ℚ)) ^ m := by
    rw [MulMemClass.coe_mul, SubmonoidClass.coe_pow, map_mul, map_pow]

  have hcW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
    W.algebraMap_mem' _
  have ha₀W : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a₀ : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
    W.algebraMap_mem' _
  obtain ⟨hhc_mem, hhc_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hc
  obtain ⟨hxa_mem, hxa_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ha₀
  have hhW : h ∈ W.toValuationSubring := by
    have := add_mem hhc_mem hcW
    simpa using this
  have hxW : (uFun (q := q))⁻¹ ∈ W.toValuationSubring := by
    have := add_mem hxa_mem ha₀W
    simpa using this
  have e1 : IsLocalRing.residue W.toValuationSubring ⟨h, hhW⟩
      = IsLocalRing.residue W.toValuationSubring ⟨_, hcW⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨h, hhW⟩ - ⟨_, hcW⟩ : W.toValuationSubring) = ⟨_, hhc_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hhc_max)
  have e2 : IsLocalRing.residue W.toValuationSubring ⟨(uFun (q := q))⁻¹, hxW⟩
      = IsLocalRing.residue W.toValuationSubring ⟨_, ha₀W⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨(uFun (q := q))⁻¹, hxW⟩ - ⟨_, ha₀W⟩ : W.toValuationSubring) = ⟨_, hxa_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hxa_max)
  have hprod_mem : h * ((uFun (q := q))⁻¹) ^ m ∈ W.toValuationSubring := mul_mem hhW (pow_mem hxW m)
  have hconst_mem : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c * a₀ ^ m : A) : AlgebraicClosure ℚ)
      ∈ W.toValuationSubring := W.algebraMap_mem' _
  have hprodW : h * ((uFun (q := q))⁻¹) ^ m
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c * a₀ ^ m : A) : AlgebraicClosure ℚ)
        ∈ W.toValuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨sub_mem hprod_mem hconst_mem, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have e3 : (⟨h * ((uFun (q := q))⁻¹) ^ m
        - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c * a₀ ^ m : A) : AlgebraicClosure ℚ),
          sub_mem hprod_mem hconst_mem⟩ : W.toValuationSubring)
        = ⟨h, hhW⟩ * ⟨(uFun (q := q))⁻¹, hxW⟩ ^ m - ⟨_, hcW⟩ * ⟨_, ha₀W⟩ ^ m := by
      apply Subtype.ext
      simp [hconst_eq]
    show IsLocalRing.residue W.toValuationSubring _ = 0
    rw [e3, map_sub, map_mul, map_pow, map_mul, map_pow, e1, e2, sub_self]

  have hxint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))})
      ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) := by
    have := @isIntegral_algebraMap (Algebra.adjoin (AlgebraicClosure ℚ) {((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))}) ↥(modularFunctionFieldBar (1 * q)) _ _ _
      ⟨(uFun (q := q))⁻¹, Algebra.self_mem_adjoin_singleton _ _⟩
    simpa using this
  have hQx := hred ⟨(uFun (q := q))⁻¹, hu'⟩ hxint a₀ ha₀
  have hQp := hred ⟨h * ((uFun (q := q))⁻¹) ^ m, mul_mem hh (pow_mem hu' m)⟩ hint (c * a₀ ^ m) hprodW

  have hux : (⟨uFun, hu⟩ : R.R₁.integers) * ⟨(uFun (q := q))⁻¹, hu'⟩ = 1 := by
    apply Subtype.ext
    push_cast
    exact mul_inv_cancel₀ hu_ne
  have hρux : R.R₁.residue ⟨uFun, hu⟩ * R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ = 1 := by
    rw [← map_mul, hux, map_one]
  have hρp : R.R₁.residue ⟨h * ((uFun (q := q))⁻¹) ^ m, mul_mem hh (pow_mem hu' m)⟩
      = R.R₁.residue ⟨h, hh⟩ * R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ ^ m := by
    rw [← map_pow, ← map_mul]
    congr 1

  have hcQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have ha₀Q : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A a₀) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have hca₀Q : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A (c * a₀ ^ m)) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  obtain ⟨hxq_mem, hxq_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hQx
  obtain ⟨hpq_mem, hpq_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hQp
  have hρxQ : R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ ∈ Q.toValuationSubring := by
    have := add_mem hxq_mem ha₀Q
    simpa using this
  have hρpQ : R.R₁.residue ⟨h * ((uFun (q := q))⁻¹) ^ m, mul_mem hh (pow_mem hu' m)⟩ ∈ Q.toValuationSubring := by
    have := add_mem hpq_mem hca₀Q
    simpa using this
  obtain ⟨hρuQ, huunit⟩ := Q.exists_isUnit_of_ord_eq_zero hu0 hūQ
  have hxu_pow : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ^ m * (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ^ m = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hu_ne, one_pow]
  have key0 : (⟨h, hh⟩ : R.R₁.integers)
      = ⟨h * ((uFun (q := q))⁻¹) ^ m, mul_mem hh (pow_mem hu' m)⟩ * ⟨uFun, hu⟩ ^ m := by
    apply Subtype.ext
    push_cast
    rw [mul_assoc, hxu_pow, mul_one]
  have hρhQ : R.R₁.residue ⟨h, hh⟩ ∈ Q.toValuationSubring := by
    have key : R.R₁.residue ⟨h, hh⟩
        = R.R₁.residue ⟨h * ((uFun (q := q))⁻¹) ^ m, mul_mem hh (pow_mem hu' m)⟩
          * R.R₁.residue ⟨uFun, hu⟩ ^ m := by
      rw [← map_pow, ← map_mul, ← key0]
    rw [key]
    exact mul_mem hρpQ (pow_mem hρuQ m)

  have f1 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρxQ⟩
      = IsLocalRing.residue Q.toValuationSubring ⟨_, ha₀Q⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρxQ⟩ - ⟨_, ha₀Q⟩ : Q.toValuationSubring) = ⟨_, hxq_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hxq_max)
  have f2 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρpQ⟩
      = IsLocalRing.residue Q.toValuationSubring ⟨_, hca₀Q⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρpQ⟩ - ⟨_, hca₀Q⟩ : Q.toValuationSubring) = ⟨_, hpq_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hpq_max)

  have hxunit : IsUnit (⟨_, hρxQ⟩ : Q.toValuationSubring) := by
    refine isUnit_iff_exists_inv.mpr ⟨⟨_, hρuQ⟩, Subtype.ext ?_⟩
    push_cast
    rw [mul_comm]; exact hρux
  have hā₀ : IsLocalRing.residue Q.toValuationSubring ⟨_, ha₀Q⟩ ≠ 0 := by
    rw [← f1]
    exact (IsLocalRing.residue_ne_zero_iff_isUnit _).mpr hxunit

  have g1 : (⟨_, hρpQ⟩ : Q.toValuationSubring) = ⟨_, hρhQ⟩ * ⟨_, hρxQ⟩ ^ m := by
    apply Subtype.ext
    push_cast
    exact hρp
  have g2 : (⟨_, hca₀Q⟩ : Q.toValuationSubring) = ⟨_, hcQ⟩ * ⟨_, ha₀Q⟩ ^ m := by
    apply Subtype.ext
    push_cast
    rw [map_mul, map_pow, map_mul, map_pow]
  rw [g1, g2, map_mul, map_pow, map_mul, map_pow, f1] at f2
  have f3 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρhQ⟩
      = IsLocalRing.residue Q.toValuationSubring ⟨_, hcQ⟩ :=
    mul_right_cancel₀ (pow_ne_zero m hā₀) f2

  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨sub_mem hρhQ hcQ, ?_⟩
  have ee : (⟨_, sub_mem hρhQ hcQ⟩ : Q.toValuationSubring) = ⟨_, hρhQ⟩ - ⟨_, hcQ⟩ := Subtype.ext rfl
  rw [ee]
  exact Ideal.Quotient.eq.mp f3

theorem pinN_uInv_regular_cases (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hv : 0 ≤ v.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))) :
    (¬ IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) v ∧ v.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) = 0)
      ∨ (v = cuspInftyBar (1 * q) ∧ v.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) = ((1 * q : ℕ) : ℤ) - 1) := by
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  by_cases hc : IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) v
  · right
    rcases ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (1 * q) v hc with rfl | rfl
    · refine ⟨rfl, ?_⟩
      rw [Place.ord_inv, show (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
        ModularCurve.ord_cuspInftyBar_coeffEmb_modularUnitSeries (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))]
      ring
    · exfalso
      rw [Place.ord_inv, show (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
        ModularCurve.ord_cuspZeroBar_coeffEmb_modularUnitSeries (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))] at hv
      have h2 : (2 : ℤ) ≤ ((1 * q : ℕ) : ℤ) := by
        have := (Fact.out : q.Prime).two_le
        push_cast; omega
      omega
  · left
    refine ⟨hc, ?_⟩
    rw [Place.ord_inv, show (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
      ModularCurve.ord_coeffEmb_modularUnitSeries_of_not_isCusp (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q)) v hc, neg_zero]

theorem pinN_uInv_ne_zero : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
  intro h0
  have h := ModularCurve.ord_cuspInftyBar_coeffEmb_modularUnitSeries (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))
  change (cuspInftyBar (1 * q)).ord (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = _ at h
  rw [← inv_inv (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))), h0, inv_zero, Place.ord_zero] at h
  have := (Fact.out : q.Prime).two_le
  push_cast at h
  omega

theorem pinN_jFun_ne_zero : (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
  intro h0
  have h := ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * q)
  change (cuspInftyBar (1 * q)).ord (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = _ at h
  rw [h0, Place.ord_zero] at h
  omega

theorem pinN_jqFun_ne_zero : (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 := by
  intro h0
  have h := ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (1 * q) (1 * q) (dvd_refl _)
  change (cuspInftyBar (1 * q)).ord (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = _ at h
  rw [h0, Place.ord_zero] at h
  have := (Fact.out : q.Prime).pos
  push_cast at h
  omega

theorem pinN_transcendental_uInv : Transcendental (AlgebraicClosure ℚ) ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) := by
  refine Place.transcendental_of_ord_ne_zero (cuspInftyBar (1 * q)) ?_
  rw [Place.ord_inv, show (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
    ModularCurve.ord_cuspInftyBar_coeffEmb_modularUnitSeries (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))]
  have := (Fact.out : q.Prime).two_le
  push_cast
  omega

theorem pinN_finiteDimensional_adjoin_uInv :
    FiniteDimensional (IntermediateField.adjoin (AlgebraicClosure ℚ) ({((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))} : Set ↥(modularFunctionFieldBar (1 * q)))) ↥(modularFunctionFieldBar (1 * q)) := by
  apply Module.finite_of_finrank_pos
  rw [show (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl, ModularCurve.finrank_adjoin_coeffEmb_modularUnitSeries_inv (q := q)]
  have := (Fact.out : q.Prime).two_le
  omega

theorem pinN_ord_jqFun_nonneg_of_not_isCusp (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hc : ¬ IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) v) : 0 ≤ v.ord (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) := by
  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  set σ := frickeInvolutionBar (1 * q) with hσ
  have hσσ : σ * σ = 1 := AlgEquiv.ext fun y => ModularCurve.frickeInvolutionBar_frickeInvolutionBar (1 * q) y
  have hwjq : σ (jqFun (q := q)) = jFun (q := q) :=
    ModularCurve.frickeInvolutionBar_coeffEmb_qExpand (1 * q)
        (isFrickeAutFull_frickeInvolutionFull _ (ModularCurve.exists_isFrickeAutFull_of_neZero (1 * q))) (1 * q) 1 (mul_one _)
      |>.trans (Subtype.ext (congrArg (fun x => coeffEmb (AlgebraicClosure ℚ) x) (qExpand_one_apply jq)))
  have hwj : σ (jFun (q := q)) = jqFun (q := q) := by
    rw [← hwjq, ← AlgEquiv.mul_apply, hσσ, AlgEquiv.one_apply]

  have hv : v = σ • (σ • v) := by rw [smul_smul, hσσ, one_smul]
  rw [hv, ← hwj, Place.ord_smul]

  have hc' : ¬ IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) (σ • v) := by
    intro h
    apply hc
    have hh := isFrickeAutFull_frickeInvolutionFull _ (ModularCurve.exists_isFrickeAutFull_of_neZero (1 * q))
    rcases ModularCurve.eq_cuspInftyBar_or_eq_cuspZeroBar (1 * q) (σ • v) h with h1 | h1
    · rw [hv, h1, hσ, ← cuspZeroBar_def]
      exact ModularCurve.isCusp_cuspZeroBar (1 * q) hh
    · rw [hv, h1, cuspZeroBar_def, smul_smul, ← hσ, hσσ, one_smul]
      exact ModularCurve.isCusp_cuspInftyBar (1 * q)
  exact not_lt.mp fun hlt => hc' ((ModularCurve.isCusp_iff_ord_neg _ _).mpr hlt)

theorem isIntegral_adjoin_uInv_jFun_mul :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      ((jFun (q := q)) * ((uFun (q := q))⁻¹) ^ 1) := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  haveI := pinN_finiteDimensional_adjoin_uInv (q := q)
  refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg _ (pinN_transcendental_uInv (q := q)) _ fun v hv => ?_
  have hmul : v.ord (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) * (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))))
      = v.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) + v.ord (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) := by
    first
    | exact Place.ord_mul v (pinN_uInv_ne_zero (q := q)) (pinN_jFun_ne_zero (q := q))
    | exact (Place.ord_mul v (pinN_jFun_ne_zero (q := q)) (pinN_uInv_ne_zero (q := q))).trans (add_comm _ _)
  rw [pow_one, mul_comm (jFun (q := q)) ((uFun (q := q))⁻¹), hmul]
  rcases pinN_uInv_regular_cases (q := q) v hv with ⟨hc, h0⟩ | ⟨rfl, h1⟩
  · rw [h0]
    simp only [add_zero, zero_add]
    exact not_lt.mp fun hlt => hc ((ModularCurve.isCusp_iff_ord_neg _ _).mpr hlt)
  · rw [h1, show (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl, ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * q)]
    have := (Fact.out : q.Prime).two_le
    push_cast
    omega

theorem isIntegral_adjoin_uInv_jqFun_mul :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      ((jqFun (q := q)) * ((uFun (q := q))⁻¹) ^ 2) := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  haveI := pinN_finiteDimensional_adjoin_uInv (q := q)
  refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg _ (pinN_transcendental_uInv (q := q)) _ fun v hv => ?_
  have hmul : v.ord ((((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ^ 2) * (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))))
      = v.ord (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ^ 2) + v.ord (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) := by
    first
    | exact Place.ord_mul v (pow_ne_zero 2 (pinN_uInv_ne_zero (q := q))) (pinN_jqFun_ne_zero (q := q))
    | exact (Place.ord_mul v (pinN_jqFun_ne_zero (q := q)) (pow_ne_zero 2 (pinN_uInv_ne_zero (q := q)))).trans (add_comm _ _)
  have hpow2 : v.ord (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ^ 2) = 2 * v.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) := by
    rw [← zpow_natCast, Place.ord_zpow]; rfl
  rw [mul_comm (jqFun (q := q)) (((uFun (q := q))⁻¹) ^ 2), hmul, hpow2]
  rcases pinN_uInv_regular_cases (q := q) v hv with ⟨hc, h0⟩ | ⟨rfl, h1⟩
  · rw [h0, mul_zero]
    simp only [add_zero, zero_add]
    exact pinN_ord_jqFun_nonneg_of_not_isCusp (q := q) v hc
  · rw [h1, show (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
      ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (1 * q) (1 * q) (dvd_refl _)]
    have := (Fact.out : q.Prime).two_le
    push_cast
    omega

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
p2m_open "ModularCurve~coeffMap_injective"

theorem pinN_G5 {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q]
    (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data) (a : k) :
    frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a) = charLGeomPlaceOfPoint k (a ^ q) := by
  letI := Classical.decEq (RatFunc k)
  haveI : CharP ↥(modularFunctionFieldC k 1) q :=
    charP_of_injective_algebraMap (algebraMap k ↥(modularFunctionFieldC k 1)).injective q
  set J : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hJ

  have hord1 : (charLGeomPlaceOfPoint k a).ord (J - algebraMap k _ a) = 1 := by
    classical
    have e1 : (charLGeomPlaceOfPoint k a).ord (J - algebraMap k _ a)
        = (AlgebraicCurve.RationalFunctionField.placeOfPoint k a).ord
            (RatFunc.X - algebraMap k (RatFunc k) a) := by
      have hJX : (J - algebraMap k _ a) = ratFuncEquivCharLOneC k (RatFunc.X - algebraMap k (RatFunc k) a) := by
        rw [map_sub, ModularCurve.pinN_ratFuncEquivCharLOneC_X, AlgEquiv.commutes]
      rw [hJX, show charLGeomPlaceOfPoint k a
          = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeOfPoint k a) from rfl,
        ModularCurve.pinN_ord_charLGeomPlaceEquiv]
    rw [e1]
    have hXa : (RatFunc.X - algebraMap k (RatFunc k) a)
        = algebraMap (Polynomial k) (RatFunc k) (Polynomial.X - Polynomial.C a) := by
      rw [map_sub, RatFunc.algebraMap_X, RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
    rw [hXa, AlgebraicCurve.RationalFunctionField.ord_X_sub_C k a, Finsupp.add_apply,
      Finsupp.single_eq_same, Finsupp.single_apply, if_neg]
    · rfl
    ·
      intro h
      have hX : (RatFunc.X : RatFunc k) ∈ (AlgebraicCurve.RationalFunctionField.placeOfPoint k a).toValuationSubring := by
        rw [AlgebraicCurve.RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
        have := AlgebraicCurve.RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum k
          (AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible k (Polynomial.irreducible_X_sub_C a))
          Polynomial.X
        rwa [RatFunc.algebraMap_X] at this
      rw [← h, AlgebraicCurve.RationalFunctionField.placeInfty_toValuationSubring,
        Valuation.mem_valuationSubring_iff, RatFunc.inftyValuation.X, ← WithZero.exp_zero,
        WithZero.exp_le_exp] at hX
      norm_num at hX

  have hfrob : frobeniusGeomLevel k 1 data hKr (J - algebraMap k _ (a ^ q))
      = (J - algebraMap k _ a) ^ q := by
    rw [map_sub, hJ, frobeniusGeomLevel_jq, AlgHom.commutes, sub_pow_char, ← map_pow]
  have hJa_mem : (J - algebraMap k _ a) ∈ (charLGeomPlaceOfPoint k a).toValuationSubring :=
    Place.mem_of_ord_nonneg _ (by intro h0; rw [h0, Place.ord_zero] at hord1; exact zero_ne_one hord1)
      (by rw [hord1]; exact zero_le_one)
  apply ModularCurve.eq_charLGeomPlaceOfPoint_of_ord_pos

  have hmem : (J - algebraMap k _ (a ^ q))
      ∈ (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)).toValuationSubring := by
    rw [mem_frobOnPlacesGeomLevel_iff, hfrob]
    exact pow_mem hJa_mem q
  have hne : (J - algebraMap k _ (a ^ q)) ≠ 0 := by
    intro h0
    have := congrArg (frobeniusGeomLevel k 1 data hKr) h0
    rw [hfrob, map_zero] at this
    have h1 := congrArg ((charLGeomPlaceOfPoint k a).ord) this
    rw [← zpow_natCast, Place.ord_zpow, hord1, Place.ord_zero] at h1
    simp at h1
    exact (Fact.out : q.Prime).ne_zero h1
  rcases (Place.ord_nonneg_of_mem _ hmem).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso

    have hinv_mem : (J - algebraMap k _ (a ^ q))⁻¹
        ∈ (frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)).toValuationSubring :=
      Place.mem_of_ord_nonneg _ (inv_ne_zero hne) (by rw [Place.ord_inv, ← heq, neg_zero])
    rw [mem_frobOnPlacesGeomLevel_iff, map_inv₀, hfrob] at hinv_mem
    have h2 := Place.ord_nonneg_of_mem _ hinv_mem
    rw [Place.ord_inv, ← zpow_natCast, Place.ord_zpow, hord1, mul_one] at h2
    have : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
    omega

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_coeffMap redBar ι_coe ι R₁ coeffEmb_modularUnitSeries_mem_integersFst"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

theorem pinN_mem_nonunits_of_ord_pos {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {f : F} (h : 0 < v.ord f) : f ∈ v.toValuationSubring.nonunits := by
  have hf0 : f ≠ 0 := by
    intro h0; rw [h0, Place.ord_zero] at h; exact lt_irrefl _ h
  have hmem : f ∈ v.toValuationSubring := Place.mem_of_ord_nonneg _ hf0 h.le
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  refine ⟨hmem, (IsLocalRing.mem_maximalIdeal _).mpr fun hunit => ?_⟩
  have h0 := v.ord_coe_unit hunit.unit
  rw [IsUnit.unit_spec] at h0
  change v.ord f = 0 at h0
  omega

theorem pinN_eq_zero_of_algebraMap_mem_maximalIdeal {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) (e : K)
    (h : (⟨algebraMap K F e, v.algebraMap_mem' e⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _) :
    e = 0 := by
  by_contra he
  apply (IsLocalRing.mem_maximalIdeal _).mp h
  refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F e⁻¹, v.algebraMap_mem' _⟩, Subtype.ext ?_⟩
  show algebraMap K F e * algebraMap K F e⁻¹ = 1
  rw [← map_mul, mul_inv_cancel₀ he, map_one]

theorem pinN_exists_jFun_mem_integers₁ : ∃ h : jFun (q := q) ∈ R.R₁.integers,
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A) := by
  have hc : coeffMap A.subtype (jqModC A) = coeffEmb (AlgebraicClosure ℚ) jq := by
    rw [coeffMap_jqModC, coeffEmb, ← jqModC_rat, coeffMap_jqModC]
  have hy : coeffMap A.subtype (jqModC A) ∈ modularFunctionFieldBar (1 * q) := by
    rw [hc]; exact (jFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (jqModC A) hy
  have hj : (⟨coeffMap A.subtype (jqModC A), hy⟩ : modularFunctionFieldBar (1 * q)) = jFun (q := q) :=
    Subtype.ext hc
  have key : ∀ (z : modularFunctionFieldBar (1 * q)) (hz : z ∈ R.R₁.integers), z = jFun (q := q) →
      ((R.R₁.residue ⟨z, hz⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (jqModC A) →
      ∃ h : jFun (q := q) ∈ R.R₁.integers,
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = jqModC (ResidueField A) := by
    rintro z hz rfl e'
    exact ⟨hz, e'.trans (coeffMap_jqModC _)⟩
  exact key _ h hj e

theorem pinN_exists_jqFun_mem_integers₁ : ∃ h : jqFun (q := q) ∈ R.R₁.integers,
    ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
  have hc : coeffMap A.subtype (qExpand A (1 * q) (jqModC A))
      = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq) := by
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC, coeffEmb, ModularCurve.coeffMap_qExpand, ← jqModC_rat,
      coeffMap_jqModC]
  have hy : coeffMap A.subtype (qExpand A (1 * q) (jqModC A)) ∈ modularFunctionFieldBar (1 * q) := by
    rw [hc]; exact (jqFun (q := q)).2
  obtain ⟨h, e⟩ := R.residue₁_coeffMap (qExpand A (1 * q) (jqModC A)) hy
  have hj : (⟨coeffMap A.subtype (qExpand A (1 * q) (jqModC A)), hy⟩ : modularFunctionFieldBar (1 * q))
      = jqFun (q := q) :=
    Subtype.ext hc
  have key : ∀ (z : modularFunctionFieldBar (1 * q)) (hz : z ∈ R.R₁.integers), z = jqFun (q := q) →
      ((R.R₁.residue ⟨z, hz⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
        = coeffMap (IsLocalRing.residue A) (qExpand A (1 * q) (jqModC A)) →
      ∃ h : jqFun (q := q) ∈ R.R₁.integers,
        ((R.R₁.residue ⟨_, h⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
          = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)) := by
    rintro z hz rfl e'
    refine ⟨hz, e'.trans ?_⟩
    rw [ModularCurve.coeffMap_qExpand, coeffMap_jqModC]
  exact key _ h hj e

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
p2m_open "ModularCurve~coeffMap_injective"

theorem n1N_modularFunctionFieldFullC_one (K : Type*) [Field K] :
    modularFunctionFieldFullC K 1 = modularFunctionFieldC K 1 := by
  refine le_antisymm ?_ (modularFunctionFieldC_le_full K 1)
  rw [modularFunctionFieldFullC, IntermediateField.adjoin_le_iff]
  rintro x ⟨d, hne, hdvd, rfl⟩
  haveI := hne
  obtain rfl : d = 1 := Nat.dvd_one.mp hdvd
  rw [qExpand_one_apply]
  exact jqModC_mem K 1

theorem n1N_ratFuncEquivCharLOneC_X (K : Type*) [Field K] :
    ratFuncEquivCharLOneC K RatFunc.X = ⟨jqModC K, jqModC_mem K 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC K) (h := transcendental_jqModC K)

noncomputable def n1N_inclC (K : Type*) [Field K] : ↥(modularFunctionFieldC K 1) ≃ₐ[K] ↥(modularFunctionFieldFullC K 1) :=
  AlgEquiv.ofBijective (IntermediateField.inclusion (modularFunctionFieldC_le_full K 1))
    ⟨((IntermediateField.inclusion (modularFunctionFieldC_le_full K 1) :
          ↥(modularFunctionFieldC K 1) →ₐ[K] ↥(modularFunctionFieldFullC K 1)) :
          ↥(modularFunctionFieldC K 1) →+* ↥(modularFunctionFieldFullC K 1)).injective,
     fun y => ⟨⟨(y : LaurentSeries K), (n1N_modularFunctionFieldFullC_one K).le y.2⟩, Subtype.ext rfl⟩⟩

theorem n1N_inclC_coe (K : Type*) [Field K] (x : ↥(modularFunctionFieldC K 1)) :
    ((n1N_inclC K x : ↥(modularFunctionFieldFullC K 1)) : LaurentSeries K) = (x : LaurentSeries K) := by
  rw [n1N_inclC, AlgEquiv.ofBijective_apply]
  rfl

noncomputable def n1N_theta (K : Type*) [Field K] : RatFunc K ≃ₐ[K] ↥(modularFunctionFieldFullC K 1) :=
  (ratFuncEquivCharLOneC K).trans (n1N_inclC K)

theorem n1N_theta_X (K : Type*) [Field K] :
    n1N_theta K RatFunc.X = ⟨jqModC K, jqModC_mem_full K 1⟩ := by
  apply Subtype.ext
  rw [n1N_theta, AlgEquiv.trans_apply, n1N_inclC_coe, n1N_ratFuncEquivCharLOneC_X]

theorem n1N_theta_algebraMap (K : Type*) [Field K] (p : Polynomial K) :
    n1N_theta K (algebraMap (Polynomial K) (RatFunc K) p)
      = Polynomial.aeval (⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) p := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) p = Polynomial.aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h1]
  change (n1N_theta K : RatFunc K →ₐ[K] ↥(modularFunctionFieldFullC K 1)) (Polynomial.aeval RatFunc.X p) = _
  rw [← Polynomial.aeval_algHom_apply]
  have h2 : (n1N_theta K : RatFunc K →ₐ[K] ↥(modularFunctionFieldFullC K 1)) RatFunc.X = ⟨jqModC K, jqModC_mem_full K 1⟩ :=
    n1N_theta_X K
  rw [h2]

theorem n1N_coe_aeval_jFull (K : Type*) [Field K] (p : Polynomial K) :
    ((Polynomial.aeval (⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) p :
        ↥(modularFunctionFieldFullC K 1)) : LaurentSeries K) = Polynomial.aeval (jqModC K) p := by
  have h := Polynomial.aeval_algHom_apply (modularFunctionFieldFullC K 1).val
    (⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) p
  exact h.symm

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "PlaceSpecialization.LevelOneProlongationPair modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jqd_mem_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization HeckeAlphaBarIntegral HeckeBetaBarIntegral frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint transcendental_jqModC ssJSet frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_coeffMap redBar ι_coe ι R₁ coeffEmb_modularUnitSeries_mem_integersFst"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

include R in
theorem n1N_charP_residueField : CharP (ResidueField A) q :=
  (RingHom.charP_iff_charP R.redBar q).mpr inferInstance

theorem n1N_coeffMap_subtype_modularUnitSeriesZ :
    coeffMap A.subtype (coeffMap (Int.castRingHom A) (N1Glue.modularUnitSeriesZ (1 * q)))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)) := by
  rw [coeffMap_coeffMap, N1Glue.coeffEmb_modularUnitSeries_eq]
  exact coeffMap_congr (RingHom.ext_int _ _) _

theorem n1N_residue_uFun_coe (hu : (uFun (q := q)) ∈ R.R₁.integers) :
    ((R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) : LaurentSeries (ResidueField A))
      = ((HahnSeries.ofPowerSeries ℤ (ResidueField A)
          (PowerSeries.map (Int.castRingHom (ResidueField A)) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹ := by
  haveI : CharP (ResidueField A) q := n1N_charP_residueField R
  have hy : coeffMap A.subtype (coeffMap (Int.castRingHom A) (N1Glue.modularUnitSeriesZ (1 * q)))
      ∈ modularFunctionFieldBar (1 * q) := by
    rw [n1N_coeffMap_subtype_modularUnitSeriesZ]
    exact (uFun (q := q)).2
  obtain ⟨h, hh⟩ := R.residue₁_coeffMap _ hy
  have e : (⟨⟨_, hy⟩, h⟩ : R.R₁.integers) = ⟨uFun, hu⟩ :=
    Subtype.ext (Subtype.ext (n1N_coeffMap_subtype_modularUnitSeriesZ (q := q)))
  rw [← e, hh, coeffMap_coeffMap, coeffMap_congr (RingHom.ext_int _ (Int.castRingHom (ResidueField A))),
    N1Glue.coeffMap_intCast_modularUnitSeriesZ (ResidueField A) (1 * q) q (one_mul q)]

theorem n1N_residue₁_uFun_coe (hu : (uFun (q := q)) ∈ R.R₁.integers) :
    ((R.residue₁ ⟨uFun, hu⟩ : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
      = ((HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹ := by
  rw [residue₁_apply, R.ι_coe, n1N_residue_uFun_coe, map_inv₀, map_pow, ← N1Glue.coeffMap_deltaSeriesZ, coeffMap_coeffMap,
    coeffMap_congr (RingHom.ext_int _ (Int.castRingHom k)), N1Glue.coeffMap_deltaSeriesZ]

theorem n1N_uFun_ne_zero : (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) ≠ 0 :=
  fun h0 => pinN_uInv_ne_zero (q := q) (by rw [h0, inv_zero])

theorem n1N_residue_uInv (hu : (uFun (q := q)) ∈ R.R₁.integers) (hx : (uFun (q := q))⁻¹ ∈ R.R₁.integers) :
    R.R₁.residue ⟨(uFun (q := q))⁻¹, hx⟩ = (R.R₁.residue ⟨uFun, hu⟩)⁻¹ := by
  have h1 : (⟨(uFun (q := q))⁻¹, hx⟩ : R.R₁.integers) * ⟨uFun, hu⟩ = 1 :=
    Subtype.ext (inv_mul_cancel₀ (n1N_uFun_ne_zero (q := q)))
  have h2 := congrArg R.R₁.residue h1
  rw [map_mul, map_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem n1N_isIntegral_adjoin_uInv_jFun_pow_mul (i d : ℕ) (hid : i ≤ d * (q - 1)) :
    IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      ((jFun (q := q)) ^ i * ((uFun (q := q))⁻¹) ^ d) := by
  haveI := ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)
  haveI := pinN_finiteDimensional_adjoin_uInv (q := q)
  refine AlgebraicCurve.isIntegral_adjoin_of_forall_ord_nonneg _ (pinN_transcendental_uInv (q := q)) _ fun v hv => ?_
  have hj0 := pinN_jFun_ne_zero (q := q)
  have hx0 := pinN_uInv_ne_zero (q := q)
  rw [Place.ord_mul v (pow_ne_zero _ hj0) (pow_ne_zero _ hx0), ← zpow_natCast, Place.ord_zpow, ← zpow_natCast,
    Place.ord_zpow]
  rcases pinN_uInv_regular_cases (q := q) v hv with ⟨hc, h0⟩ | ⟨rfl, h1⟩
  · rw [h0, mul_zero, add_zero]
    have hj : 0 ≤ v.ord (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) :=
      not_lt.mp fun hlt => hc ((ModularCurve.isCusp_iff_ord_neg _ _).mpr hlt)
    positivity
  · rw [h1, show (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
      ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * q)]
    have h2 := (Fact.out : q.Prime).two_le
    have hid' : (i : ℤ) ≤ (d : ℤ) * ((q : ℤ) - 1) := by
      have : ((q - 1 : ℕ) : ℤ) = (q : ℤ) - 1 := by omega
      rw [← this]; exact_mod_cast hid
    push_cast
    nlinarith

private noncomputable def _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.n1N_constHom : A →+* R.R₁.integers :=
  RingHom.codRestrict ((algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))).comp A.subtype)
    R.R₁.integers (fun a => (R.R₁.algebraMap_mem_iff (a : AlgebraicClosure ℚ)).mpr a.2)

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "n1N_constHom"
theorem n1N_constHom_coe (a : A) :
    ((R.n1N_constHom a : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) := rfl

theorem n1N_residue_constHom (a : A) :
    R.R₁.residue (R.n1N_constHom a) = algebraMap (ResidueField A) _ (IsLocalRing.residue A a) := by
  have h := R.R₁.residue_algebraMap a
  exact h

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

p2m_open "ModularCurve~coeffMap_injective" in open _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.ModularCurve _root_.ModularCurve.PlaceSpecialization _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.ModularCurve.PlaceSpecialization _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair _root_.P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv.ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial in
set_option maxHeartbeats 16000000 in

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : P.LevelOneProlongationPair)
    (hx : ((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q))))⁻¹ ∈ R.R₁.integers)
    (h : ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (hh : IsIntegral (Algebra.adjoin (ResidueField A)
      {(R.R₁.residue ⟨_, hx⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1))}) h) :
    ∃ f : R.R₁.integers,
      IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        {(((⟨coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries (1 * q)),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))⟩ :
        ↥(modularFunctionFieldBar (1 * q))))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))})
        (f : ↥(modularFunctionFieldBar (1 * q))) ∧
      R.R₁.residue f = h := by
  classical
  haveI : CharP (ResidueField A) q := n1N_charP_residueField R
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A

  change ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers at hx
  obtain ⟨hu, -⟩ := coeffEmb_modularUnitSeries_mem_integersFst R
  change (uFun (q := q)) ∈ R.R₁.integers at hu
  set ubar : ↥(modularFunctionFieldFullC (ResidueField A) 1) := R.R₁.residue ⟨uFun, hu⟩ with hubar_def
  set xbar : ↥(modularFunctionFieldFullC (ResidueField A) 1) := R.R₁.residue ⟨(uFun (q := q))⁻¹, hx⟩ with hxbar_def
  change IsIntegral (Algebra.adjoin (ResidueField A) {xbar}) h at hh
  have hxbar : xbar = ubar⁻¹ := n1N_residue_uInv R hu hx

  obtain ⟨Pq, hPmonic, -, hPid⟩ := N1Glue.exists_monic_deltaBar_pow_inv_eq_aeval q (ResidueField A)
  have hPdeg : Pq.natDegree ≤ q - 1 := N1Glue.natDegree_le_of_deltaBar_pow_inv_eq_aeval q (ResidueField A) Pq hPmonic hPid
  have hubar_eq : ubar = aeval (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) Pq := by
    apply Subtype.ext
    rw [hubar_def, n1N_residue_uFun_coe R hu, n1N_coe_aeval_jFull, ← hPid]
  have hubar0 : ubar ≠ 0 := by
    intro h0
    have h0' := congrArg Subtype.val h0
    rw [hubar_def, n1N_residue_uFun_coe R hu] at h0'
    exact (inv_ne_zero (pow_ne_zero _ (N1Glue.deltaBar_ne_zero (ResidueField A)))) h0'

  set θ := n1N_theta (ResidueField A) with hθ_def
  have hθP : θ (algebraMap (ResidueField A)[X] (RatFunc (ResidueField A)) Pq) = ubar := by
    rw [hθ_def, n1N_theta_algebraMap, ← hubar_eq]
  have hPq0 : Pq ≠ 0 := hPmonic.ne_zero
  have hθy : θ.symm xbar = (algebraMap (ResidueField A)[X] (RatFunc (ResidueField A)) Pq)⁻¹ := by
    rw [hxbar, map_inv₀, ← hθP, AlgEquiv.symm_apply_apply]

  obtain ⟨p, hpmonic, hp⟩ := hh
  set n := p.natDegree with hn_def
  have hcoef : ∀ i : ℕ, ∃ b : (ResidueField A)[X], aeval xbar b = ((p.coeff i : Algebra.adjoin (ResidueField A) {xbar}) : ↥(modularFunctionFieldFullC (ResidueField A) 1)) := by
    intro i
    have hm : ((p.coeff i : Algebra.adjoin (ResidueField A) {xbar}) : ↥(modularFunctionFieldFullC (ResidueField A) 1)) ∈ Algebra.adjoin (ResidueField A) {xbar} := (p.coeff i).2
    have hm' := (SetLike.ext_iff.mp (Algebra.adjoin_singleton_eq_range_aeval (ResidueField A) xbar) _).mp hm
    exact (AlgHom.mem_range _).mp hm'
  choose b hb using hcoef
  have heq : h ^ n + ∑ i ∈ Finset.range n, aeval xbar (b i) * h ^ i = 0 := by
    have h1 : p.eval₂ (algebraMap (Algebra.adjoin (ResidueField A) {xbar}) ↥(modularFunctionFieldFullC (ResidueField A) 1)) h = 0 := hp
    rw [eval₂_eq_sum_range, Finset.sum_range_succ, ← hn_def] at h1
    have hlead : (algebraMap (Algebra.adjoin (ResidueField A) {xbar}) ↥(modularFunctionFieldFullC (ResidueField A) 1)) (p.coeff n) = 1 := by
      rw [hn_def, Polynomial.coeff_natDegree, hpmonic.leadingCoeff, map_one]
    rw [hlead, one_mul, add_comm] at h1
    rw [← h1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb i]
    rfl

  set r := θ.symm h with hr_def
  have hmap : ∀ bb : (ResidueField A)[X], θ.symm (aeval xbar bb) = aeval (θ.symm xbar) bb := fun bb =>
    (Polynomial.aeval_algHom_apply (θ.symm : ↥(modularFunctionFieldFullC (ResidueField A) 1) →ₐ[(ResidueField A)] RatFunc (ResidueField A)) xbar bb).symm
  have heq' : r ^ n + ∑ i : Fin n, aeval ((algebraMap (ResidueField A)[X] (RatFunc (ResidueField A)) Pq)⁻¹) (b i) * r ^ (i : ℕ) = 0 := by
    have h2 := congrArg θ.symm heq
    rw [map_add, map_pow, map_sum, map_zero, Finset.sum_range] at h2
    simp only [map_mul, map_pow, hmap, hθy] at h2
    exact h2

  set d := (Finset.range n).sup fun i => (b i).natDegree with hd_def
  have hbd : ∀ i : Fin n, (b i).natDegree ≤ d := fun i =>
    Finset.le_sup (f := fun i => (b i).natDegree) (Finset.mem_range.mpr i.2)
  obtain ⟨g, hgdeg, hg⟩ := N1RF.exists_eq_pow_mul_of_aeval_inv Pq hPq0 r n d (fun i => b i) hbd heq'
  have hgd : g.natDegree ≤ d * (q - 1) := hgdeg.trans (Nat.mul_le_mul_left d hPdeg)

  have hh_eq : h = aeval (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) g * xbar ^ d := by
    have h3 := congrArg θ hg
    rw [map_mul, map_pow, hθP, hr_def, AlgEquiv.apply_symm_apply, hθ_def, n1N_theta_algebraMap] at h3
    rw [hxbar, h3, inv_pow, mul_assoc, mul_comm h, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hubar0), one_mul]

  have hres_surj : Function.Surjective (IsLocalRing.residue A) := Ideal.Quotient.mk_surjective
  obtain ⟨G, hGmap, hGdeg⟩ : ∃ G : A[X], G.map (IsLocalRing.residue A) = g ∧ G.degree = g.degree :=
    Polynomial.mem_lifts_and_degree_eq ((Polynomial.mem_lifts g).mpr (Polynomial.map_surjective _ hres_surj g))
  have hGnat : G.natDegree = g.natDegree := natDegree_eq_of_degree_eq hGdeg

  obtain ⟨hj, hjres⟩ := pinN_exists_jFun_mem_integers₁ R
  have hjres' : R.R₁.residue ⟨jFun, hj⟩ = (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) := Subtype.ext hjres

  let f₀ : R.R₁.integers := G.eval₂ R.n1N_constHom ⟨jFun, hj⟩
  let f : R.R₁.integers := f₀ * ⟨(uFun (q := q))⁻¹, hx⟩ ^ d
  refine ⟨f, ?_, ?_⟩
  ·
    have hf₀ : ((f₀ : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q)))
        = ∑ i ∈ Finset.range (G.natDegree + 1),
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((G.coeff i : A) : AlgebraicClosure ℚ)
              * (jFun (q := q)) ^ i := by
      show R.R₁.integers.subtype (G.eval₂ R.n1N_constHom ⟨jFun, hj⟩) = _
      rw [Polynomial.hom_eval₂, eval₂_eq_sum_range]
      rfl
    have hf : ((f : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q)))
        = ∑ i ∈ Finset.range (G.natDegree + 1),
            algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((G.coeff i : A) : AlgebraicClosure ℚ)
              * ((jFun (q := q)) ^ i * ((uFun (q := q))⁻¹) ^ d) := by
      show ((f₀ : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))) * (((uFun (q := q))⁻¹) ^ d) = _
      rw [hf₀, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [hf]
    refine IsIntegral.sum _ fun i hi => ?_
    have hi' : i ≤ d * (q - 1) := by
      have := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      rw [hGnat] at this
      exact this.trans hgd
    refine IsIntegral.mul ?_ (n1N_isIntegral_adjoin_uInv_jFun_pow_mul i d hi')
    exact (isIntegral_algebraMap (R := AlgebraicClosure ℚ)).tower_top
  ·
    have hφ : (R.R₁.residue).comp R.n1N_constHom = (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)).comp (IsLocalRing.residue A) :=
      RingHom.ext fun a => n1N_residue_constHom R a
    have hres₀ : R.R₁.residue f₀ = aeval (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) g := by
      show R.R₁.residue (G.eval₂ R.n1N_constHom ⟨jFun, hj⟩) = aeval (⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) g
      rw [Polynomial.hom_eval₂, hjres', hφ, ← Polynomial.eval₂_map, hGmap, aeval_def]
    show R.R₁.residue (f₀ * ⟨(uFun (q := q))⁻¹, hx⟩ ^ d) = h
    rw [map_mul, map_pow, ← hxbar_def, hres₀, ← hh_eq]

end

end S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv
end P2MW
export P2MW.S_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv (solution)
