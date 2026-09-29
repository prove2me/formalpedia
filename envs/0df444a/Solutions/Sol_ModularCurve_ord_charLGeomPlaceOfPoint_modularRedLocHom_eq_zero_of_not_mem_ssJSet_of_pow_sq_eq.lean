-- Prove2me | solution 1 for ModularCurve.ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4e297a2b-7398-58eb-b91e-55083344e8e9

import Mathlib
import Theorems.Thm_ModularCurve_mem_ssJSet_map_of_isAlgClosed
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
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_CharPReduction
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_JWidth
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_AlgebraicCurve_RegularProlongation
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_map_intCast_pow_char_eq_qExpand
import Theorems.Thm_ModularCurve_delta_pow_mul_prod_jqModC_sub_pow_eq_one
import Theorems.Thm_ModularCurve_zero_mem_ssJSet_of_lt_five
import Theorems.Thm_ModularCurve_ssJSet_finite
import Theorems.Thm_ModularCurve_pow_q_sq_eq_self_of_mem_ssJSet
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_coeffEmb_modularUnitSeries_mem_integersFst
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_residue_coeffEmb_modularUnitSeries_ne_zero
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv
import Theorems.Thm_ModularCurve_PlaceSpecialization_LevelOneProlongationPair_exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv
import Theorems.Thm_ValuationSubring_isAlgClosed_residueField_algebraicClosure_rat
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_levelOneProlongationPair
import Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_red_surjective
import Theorems.Thm_ModularCurve_PlaceSpecialization_isAlgClosed
import Theorems.Thm_ModularCurve_restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_restrictAlong_heckeBetaBar_frickeInvolutionBar_smul
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_modularUnitSeries
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldBar
import Theorems.Thm_ModularCurve_isCurveOver_modularFunctionFieldFullC
import Theorems.Thm_AlgebraicCurve_RegularProlongation_sum_ord_eq_ord_residue_of_residue_integralClosure_surjective
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeInfty_algebraMap
import Theorems.Thm_ModularCurve_placeSpecialization_exists_level_one_residueField
import Theorems.Thm_ModularCurve_exists_kroneckerCongruence_of_prime
import Theorems.Thm_ModularCurve_heckeAlphaBarIntegral_of_prime
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_prime
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_AlgebraicCurve_RationalFunctionField_ord_placeOfPoint_algebraMap
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.RationalFunctionField.instNontrivialSubtypeUnitsWithZeroMultiplicativeIntMemSubgroupValueGroupRatFuncValuationInftyValuation_definitions AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt ModularCurve.instIsElliptic_tateLaurent ModularCurve.instIsElliptic_tateBase"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left"
p2m_attr_erase "simp" "ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ AlgebraicCurve.RationalFunctionField.placeEquivOption_placeInfty AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_some AlgebraicCurve.RationalFunctionField.placeEquivOption_placeOfPoint AlgebraicCurve.RationalFunctionField.placeEquivOption_symm_none AlgebraicCurve.mulAdele_apply AlgebraicCurve.residuePairing_apply_coe AlgebraicCurve.mem_adeleBdd AlgebraicCurve.weilSmul_one AlgebraicCurve.diagonalHom_apply AlgebraicCurve.weilSmul_apply AlgebraicCurve.adeleSpaceMul_coe AlgebraicCurve.mulAdele_one AlgebraicCurve.TranscendenceTower.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.injEq AlgebraicCurve.TranscendenceTower.mk.injEq AlgebraicCurve.PoleDivisorPackage.mk.sizeOf_spec AlgebraicCurve.IntegralBasisInLSpace.mk.sizeOf_spec AlgebraicCurve.PoleDivisorPackage.mk.injEq AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.tateLaurent_a₆ ModularCurve.tatePowerSeries_a₄"
p2m_attr_erase "simp" "ModularCurve.tatePowerSeries_a₆ ModularCurve.tateLaurent_a₄ ModularCurve.tatePowerSeries_a₁ ModularCurve.tatePowerSeries_a₂ ModularCurve.tatePowerSeries_a₃ ModularCurve.tateUnivCurve_a₂ ModularCurve.tateUnivCurve_a₃ ModularCurve.tateUnivCurve_a₆ ModularCurve.nonToricPoint_fst ModularCurve.toricPoint_snd ModularCurve.tateUnivCurve_a₁ ModularCurve.nonToricPoint_snd ModularCurve.tateUnivCurve_a₄ ModularCurve.toricPoint_fst TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero"
p2m_attr_erase "simp" "TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero ModularCurve.reductionDivAlong_apply ModularCurve.coe_reductionDegZeroAlong ModularCurve.coe_frobeniusModL ModularCurve.coe_frobeniusDegZeroPullbackModL ModularCurve.coe_frobeniusDegZeroPushforwardModL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

p2m_open "HahnSeries ModularCurve~coeffMap_injective P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
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
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
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

p2m_open "AlgebraicCurve ModularCurve~coeffMap_injective P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.ModularCurve IsLocalRing"

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
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
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
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

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue_sub_mem_nonunits_of_reducesOnUInvChart
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

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue_sub_mem_nonunits_of_reducesOnUInvChart"

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
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
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
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
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

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.pinN_exists_jFun_mem_integers₁ : ∃ h : jFun (q := q) ∈ R.R₁.integers,
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

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "pinN_exists_jFun_mem_integers₁"

private theorem _root_.ModularCurve.PlaceSpecialization.LevelOneProlongationPair.pinN_exists_jqFun_mem_integers₁ : ∃ h : jqFun (q := q) ∈ R.R₁.integers,
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

p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "pinN_exists_jqFun_mem_integers₁"
set_option maxHeartbeats 16000000 in

theorem not_isStrictTypeTwo_of_reducesOnUInvChart
    (hu : (uFun (q := q)) ∈ R.R₁.integers) (hu' : (uFun (q := q))⁻¹ ∈ R.R₁.integers)
    (hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (hfin : UInvFinite (A := A) W) (hred : R.ReducesOnUInvChart W Q)
    (hūQ : Q.ord (R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) = 0)
    (hjint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      ((jFun (q := q)) * ((uFun (q := q))⁻¹) ^ 1))
    (hjqint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      ((jqFun (q := q)) * ((uFun (q := q))⁻¹) ^ 2))
    (hjW : ∃ c : A, 0 < W.ord ((jFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ))) :
    ¬ P.IsStrictTypeTwo W := by
  intro hW2
  letI := Classical.decEq (RatFunc k)
  haveI : CharP (ResidueField A) q := (RingHom.charP_iff_charP R.redBar q).mpr inferInstance
  have hinf_fix := ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr
  have hJα : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) := Subtype.ext (coe_heckeAlphaBar 1 q _)
  have hJβ : heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jqFun (q := q) := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
    simp only [coeffEmb, ModularCurve.coeffMap_qExpand, one_mul]
  obtain ⟨hj₁, ej⟩ := R.pinN_exists_jFun_mem_integers₁
  obtain ⟨hj₂, ejq⟩ := R.pinN_exists_jqFun_mem_integers₁

  have hpow : R.R₁.residue ⟨jqFun, hj₂⟩ = R.R₁.residue ⟨jFun, hj₁⟩ ^ q := by
    apply Subtype.ext
    rw [ejq, SubmonoidClass.coe_pow, ej, ← qExpand_jqModC_eq_pow (ResidueField A) data hKr]
    simp only [one_mul]

  obtain ⟨c, hc⟩ := hjW
  have hredFst : P.redFst W = charLGeomPlaceOfPoint k (red c) :=
    P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W c (by rw [hJα]; exact hc)
  have hy : ∃ d : A, 0 < W.ord ((jqFun (q := q))
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (d : AlgebraicClosure ℚ)) := by
    by_contra hno
    push_neg at hno
    have h2 : P.redSnd W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by
      refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
      have h := hno b
      rw [← hJβ, ← (heckeBetaBar (AlgebraicClosure ℚ) 1 q).commutes (b : AlgebraicClosure ℚ), ← map_sub,
        Place.ord_restrictAlong _ hβ] at h
      have hepos : 0 < (Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W : ℤ) := by
        letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
        exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
      by_contra hpos
      push_neg at hpos
      exact absurd h (not_le.mpr (mul_pos hepos hpos))
    exact hW2.2 (by rw [h2, hinf_fix, hinf_fix])
  obtain ⟨d, hd⟩ := hy
  have hredSnd : P.redSnd W = charLGeomPlaceOfPoint k (red d) :=
    P.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos W d (by rw [hJβ]; exact hd)

  have Lj := R.residue_sub_mem_nonunits_of_reducesOnUInvChart hu hu' hu0 W Q hfin hred hūQ
    (jFun (q := q)) hj₁ 1 hjint c (pinN_mem_nonunits_of_ord_pos W hc)
  have Ljq := R.residue_sub_mem_nonunits_of_reducesOnUInvChart hu hu' hu0 W Q hfin hred hūQ
    (jqFun (q := q)) hj₂ 2 hjqint d (pinN_mem_nonunits_of_ord_pos W hd)

  obtain ⟨hLj_mem, hLj_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp Lj
  obtain ⟨hLjq_mem, hLjq_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp Ljq
  have hcQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have hdQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have hρjQ : R.R₁.residue ⟨jFun, hj₁⟩ ∈ Q.toValuationSubring := by
    have := add_mem hLj_mem hcQ; simpa using this
  have hρjqQ : R.R₁.residue ⟨jqFun, hj₂⟩ ∈ Q.toValuationSubring := by
    have := add_mem hLjq_mem hdQ; simpa using this
  have f1 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρjQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcQ⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρjQ⟩ - ⟨_, hcQ⟩ : Q.toValuationSubring) = ⟨_, hLj_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hLj_max)
  have f2 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρjqQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρjqQ⟩ - ⟨_, hdQ⟩ : Q.toValuationSubring) = ⟨_, hLjq_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hLjq_max)
  have g1 : (⟨_, hρjqQ⟩ : Q.toValuationSubring) = ⟨_, hρjQ⟩ ^ q := by
    apply Subtype.ext; push_cast; exact hpow
  have hcqQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have g2 : (⟨_, hcqQ⟩ : Q.toValuationSubring) = ⟨_, hcQ⟩ ^ q := by
    apply Subtype.ext
    show algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q)
      = (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c)) ^ q
    rw [map_pow]
  have f3 : IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcqQ⟩ :=
    calc IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩
        = IsLocalRing.residue Q.toValuationSubring ⟨_, hρjqQ⟩ := f2.symm
      _ = IsLocalRing.residue Q.toValuationSubring (⟨_, hρjQ⟩ ^ q) := congrArg _ g1
      _ = (IsLocalRing.residue Q.toValuationSubring ⟨_, hρjQ⟩) ^ q := map_pow _ _ _
      _ = (IsLocalRing.residue Q.toValuationSubring ⟨_, hcQ⟩) ^ q := by rw [f1]
      _ = IsLocalRing.residue Q.toValuationSubring (⟨_, hcQ⟩ ^ q) := (map_pow _ _ _).symm
      _ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcqQ⟩ := congrArg _ g2.symm
  have hdc : IsLocalRing.residue A d = IsLocalRing.residue A c ^ q := by
    have hdiff : (⟨_, hdQ⟩ - ⟨_, hcqQ⟩ : Q.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := Ideal.Quotient.eq.mp f3
    have ee : (⟨_, hdQ⟩ - ⟨_, hcqQ⟩ : Q.toValuationSubring)
        = ⟨algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d - IsLocalRing.residue A c ^ q),
            Q.algebraMap_mem' _⟩ := by
      apply Subtype.ext
      show algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d)
          - algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q)
        = algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d - IsLocalRing.residue A c ^ q)
      rw [map_sub]
    rw [ee] at hdiff
    exact sub_eq_zero.mp (pinN_eq_zero_of_algebraMap_mem_maximalIdeal Q _ hdiff)

  have hred_dc : red d = red c ^ q := by
    rw [← R.redBar_residue d, ← R.redBar_residue c, hdc, map_pow]

  have G5 : ∀ a : k, frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)
      = charLGeomPlaceOfPoint k (a ^ q) := pinN_G5 (k := k) data hKr

  have hcd : red c = red d ^ q := by
    have h := hW2.1
    rw [hredFst, hredSnd, G5] at h
    exact charLGeomPlaceOfPoint_injective k h

  apply hW2.2
  rw [hredSnd, G5, G5, ← pow_mul, show q * q = q ^ 2 from (sq q).symm]
  congr 1
  calc red d ^ q ^ 2 = (red d ^ q) ^ q := by rw [← pow_mul, show q * q = q ^ 2 from (sq q).symm]
    _ = red c ^ q := by rw [← hcd]
    _ = red d := hred_dc.symm

theorem exists_coords_of_isStrictTypeOne
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : P.IsStrictTypeOne W) :
    ∃ x y : A,
      0 < W.ord ((jFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (x : AlgebraicClosure ℚ)) ∧
      0 < W.ord ((jqFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (y : AlgebraicClosure ℚ)) ∧
      P.redFst W = charLGeomPlaceOfPoint k (red x) ∧
      P.redSnd W = charLGeomPlaceOfPoint k (red y) ∧
      red y = red x ^ q ∧ red x ^ (q ^ 2) ≠ red x := by
  letI := Classical.decEq (RatFunc k)

  have hinf_fix := ModularCurve.frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty k data hKr

  have hJα : heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jFun (q := q) := Subtype.ext (coe_heckeAlphaBar 1 q _)
  have hJβ : heckeBetaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) = jqFun (q := q) := by
    apply Subtype.ext
    rw [coe_heckeBetaBar]
    show qExpand (AlgebraicClosure ℚ) q (coeffEmb (AlgebraicClosure ℚ) jq) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq)
    simp only [coeffEmb, ModularCurve.coeffMap_qExpand, one_mul]

  have hx : ∃ x : A, 0 < W.ord ((jFun (q := q))
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ)) := by
    by_contra hno
    push_neg at hno
    have h1 := P.redFst_eq_placeInfty_of_forall_ord_le_zero W hno
    exact hW.2 (by rw [h1, hinf_fix, hinf_fix])
  obtain ⟨x, hx⟩ := hx
  have hredFst : P.redFst W = charLGeomPlaceOfPoint k (red x) :=
    P.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos W x (by rw [hJα]; exact hx)

  have hy : ∃ y : A, 0 < W.ord ((jqFun (q := q))
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)) := by
    by_contra hno
    push_neg at hno
    have h2 : P.redSnd W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by
      refine P.sp_eq_placeInfty_of_forall_ord_le_zero _ fun b => ?_
      have h := hno b
      rw [← hJβ, ← (heckeBetaBar (AlgebraicClosure ℚ) 1 q).commutes (b : AlgebraicClosure ℚ), ← map_sub,
        Place.ord_restrictAlong _ hβ] at h
      have hepos : 0 < (Place.ramificationIndexAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q) W : ℤ) := by
        letI := algebraAlong (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isScalarTower_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q)
        haveI := isIntegral_along (heckeBetaBar (AlgebraicClosure ℚ) 1 q) hβ
        exact_mod_cast Place.ramificationIndex_pos (F := modularFunctionFieldBar 1) W
      by_contra hpos
      push_neg at hpos
      exact absurd h (not_le.mpr (mul_pos hepos hpos))
    have h3 : P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) :=
      frobOnPlacesGeomLevel_injective k 1 data hKr (by rw [hinf_fix]; exact hW.1.trans h2)
    exact hW.2 (by rw [h3, hinf_fix, hinf_fix])
  obtain ⟨y, hy⟩ := hy
  have hredSnd : P.redSnd W = charLGeomPlaceOfPoint k (red y) :=
    P.redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos W y (by rw [hJβ]; exact hy)

  have G5 : ∀ a : k, frobOnPlacesGeomLevel k 1 data hKr (charLGeomPlaceOfPoint k a)
      = charLGeomPlaceOfPoint k (a ^ q) := pinN_G5 (k := k) data hKr

  have hyx : red y = red x ^ q := by
    have h := hW.1
    rw [hredFst, hredSnd, G5] at h
    exact (charLGeomPlaceOfPoint_injective k h).symm
  have hfix : red x ^ (q ^ 2) ≠ red x := by
    intro he
    apply hW.2
    rw [hredFst, G5, G5, ← pow_mul, show q * q = q ^ 2 from (sq q).symm, he]
  exact ⟨x, y, hx, hy, hredFst, hredSnd, hyx, hfix⟩

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
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
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
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

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

theorem asmN_redBar_surjective : Function.Surjective R.redBar := fun y => by
  obtain ⟨a, rfl⟩ := P.red_surjective y
  exact ⟨IsLocalRing.residue A a, R.redBar_residue a⟩

theorem asmN_iota_algebraMap (c : ResidueField A) :
    R.ι (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) c) = algebraMap k ↥(modularFunctionFieldC k 1) (R.redBar c) := by
  apply Subtype.ext
  rw [R.ι_coe]
  show coeffMap R.redBar (algebraMap (ResidueField A) (LaurentSeries (ResidueField A)) c)
    = algebraMap k (LaurentSeries k) (R.redBar c)
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem asmN_iota_surjective : Function.Surjective R.ι := by
  intro y
  suffices key : ∀ (z : LaurentSeries k) (hz : z ∈ modularFunctionFieldC k 1),
      (⟨z, hz⟩ : ↥(modularFunctionFieldC k 1)) ∈ R.ι.fieldRange by
    obtain ⟨x, hx⟩ := (RingHom.mem_fieldRange).mp (key y.1 y.2)
    exact ⟨x, hx⟩
  intro z hz
  induction hz using IntermediateField.adjoin_induction with
  | mem x hx =>
      rcases hx with rfl | hx
      · refine (RingHom.mem_fieldRange).mpr ⟨⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩, ?_⟩
        apply Subtype.ext
        rw [R.ι_coe]
        exact coeffMap_jqModC _
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        refine (RingHom.mem_fieldRange).mpr ⟨⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩, ?_⟩
        apply Subtype.ext
        rw [R.ι_coe]
        show coeffMap R.redBar (jqModC (ResidueField A)) = jqNModC k 1
        rw [coeffMap_jqModC, jqNModC, qExpand_one_apply]
  | algebraMap c =>
      obtain ⟨c₀, rfl⟩ := asmN_redBar_surjective R c
      refine (RingHom.mem_fieldRange).mpr ⟨algebraMap _ _ c₀, ?_⟩
      rw [asmN_iota_algebraMap]
      rfl
  | add x y hx hy ihx ihy =>
      have e : (⟨x + y, add_mem hx hy⟩ : ↥(modularFunctionFieldC k 1)) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
      rw [e]; exact R.ι.fieldRange.add_mem ihx ihy
  | inv x hx ihx =>
      have e : (⟨x⁻¹, inv_mem hx⟩ : ↥(modularFunctionFieldC k 1)) = (⟨x, hx⟩ : ↥(modularFunctionFieldC k 1))⁻¹ := rfl
      rw [e]; exact R.ι.fieldRange.inv_mem ihx
  | mul x y hx hy ihx ihy =>
      have e : (⟨x * y, mul_mem hx hy⟩ : ↥(modularFunctionFieldC k 1)) = ⟨x, hx⟩ * ⟨y, hy⟩ := rfl
      rw [e]; exact R.ι.fieldRange.mul_mem ihx ihy

theorem asmN_exists_place_comap_iota (v' : Place k ↥(modularFunctionFieldC k 1)) :
    ∃ Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1),
      (∀ g, g ∈ Q.toValuationSubring ↔ R.ι g ∈ v'.toValuationSubring) ∧
      (∀ g, Q.ord g = v'.ord (R.ι g)) := by
  letI : Algebra (ResidueField A) ↥(modularFunctionFieldC k 1) := ((algebraMap k ↥(modularFunctionFieldC k 1)).comp R.redBar).toAlgebra
  let v₀ : Place (ResidueField A) ↥(modularFunctionFieldC k 1) :=
    { toValuationSubring := v'.toValuationSubring
      algebraMap_mem' := fun c => v'.algebraMap_mem' (R.redBar c)
      ne_top' := v'.ne_top'
      isPrincipalIdealRing' := v'.isPrincipalIdealRing' }
  let ιe : ↥(modularFunctionFieldFullC (ResidueField A) 1) ≃+* ↥(modularFunctionFieldC k 1) := RingEquiv.ofBijective R.ι ⟨R.ι.injective, asmN_iota_surjective R⟩
  have he : ∀ c, ιe.symm (algebraMap (ResidueField A) ↥(modularFunctionFieldC k 1) c) = algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) c := by
    intro c
    apply ιe.injective
    rw [RingEquiv.apply_symm_apply]
    show algebraMap k ↥(modularFunctionFieldC k 1) (R.redBar c) = R.ι (algebraMap _ _ c)
    rw [asmN_iota_algebraMap]
  refine ⟨Place.congrRingEquiv ιe.symm he v₀, fun g => ?_, fun g => ?_⟩
  · rw [Place.congrRingEquiv_toValuationSubring, ValuationSubring.mem_comap]
    show ιe.symm.symm g ∈ v'.toValuationSubring ↔ _
    rw [RingEquiv.symm_symm]
    rfl
  · have h := Place.ord_congrRingEquiv ιe.symm he v₀ (R.ι g)
    have e : ιe.symm (R.ι g) = g := ιe.symm_apply_apply g
    rw [e] at h
    exact h

omit R in
theorem asmN_eq_placeInfty_or_exists (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place k ↥(modularFunctionFieldC k 1)) :
    letI := Classical.decEq (RatFunc k)
    v = charLGeomPlaceEquiv k (RationalFunctionField.placeInfty k) ∨
      ∃ a : A, v = charLGeomPlaceOfPoint k (red a) := by
  obtain ⟨w, rfl⟩ := P.d4 v
  by_cases h : ∃ a : A, 0 < w.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (a : AlgebraicClosure ℚ))
  · obtain ⟨a, ha⟩ := h
    exact Or.inr ⟨a, P.sp_eq_charLGeomPlaceOfPoint_of_ord_pos w a ha⟩
  · push_neg at h
    exact Or.inl (P.sp_eq_placeInfty_of_forall_ord_le_zero w h)

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"

open Polynomial in

theorem n1N_ord_placeOfPoint_algebraMap_eq_zero (K : Type*) [Field K] (b : K) (p : K[X]) (hp : p.eval b ≠ 0) :
    (AlgebraicCurve.RationalFunctionField.placeOfPoint K b).ord (algebraMap K[X] (RatFunc K) p) = 0 := by
  have hp0 : p ≠ 0 := by rintro rfl; simp at hp
  have key : (AlgebraicCurve.RationalFunctionField.placeOfPoint K b).ord (algebraMap K[X] (RatFunc K) p) ≠ 0 ↔ p.IsRoot b := by
    rw [AlgebraicCurve.RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum,
      AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) _ hp0,
      AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal, Ideal.mem_span_singleton,
      Polynomial.dvd_iff_isRoot]
  by_contra hne
  exact hp (key.mp hne)

theorem n1N_ratFuncEquivCharLOneC_algebraMap (K : Type*) [Field K] (p : Polynomial K) :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) p)
      = Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) p = Polynomial.aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h1]
  change (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) (Polynomial.aeval RatFunc.X p) = _
  rw [← Polynomial.aeval_algHom_apply]
  have h2 : (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) RatFunc.X = ⟨jqModC K, jqModC_mem K 1⟩ :=
    n1N_ratFuncEquivCharLOneC_X K
  rw [h2]

theorem n1N_coe_aeval_jC (K : Type*) [Field K] (p : Polynomial K) :
    ((Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p :
        ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = Polynomial.aeval (jqModC K) p :=
  (Polynomial.aeval_algHom_apply (modularFunctionFieldC K 1).val
    (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p).symm

theorem n1N_ord_charLGeomPlaceOfPoint_aeval_eq_zero (K : Type*) [Field K] (b : K) (p : Polynomial K)
    (hp : p.eval b ≠ 0) :
    (charLGeomPlaceOfPoint K b).ord (Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p) = 0 := by
  rw [← n1N_ratFuncEquivCharLOneC_algebraMap]
  show (charLGeomPlaceEquiv K (AlgebraicCurve.RationalFunctionField.placeOfPoint K b)).ord _ = 0
  rw [pinN_ord_charLGeomPlaceEquiv]
  exact n1N_ord_placeOfPoint_algebraMap_eq_zero K b p hp

theorem n1N_liesOverPrime_of_ringHom {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hq : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hq
  have e : (((q : A) : AlgebraicClosure ℚ)) = (q : AlgebraicClosure ℚ) := by norm_cast
  rw [e] at h
  exact h

namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
p2m_open "ModularCurve.PlaceSpecialization"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  (P : PlaceSpecialization A q 1 data hKr k red hα hβ)

theorem n1N_redFst_frickeInvolutionBar_smul
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redFst (frickeInvolutionBar (1 * q) • W) = P.redSnd W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul q hα hβ]

theorem n1N_redSnd_frickeInvolutionBar_smul
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.redSnd (frickeInvolutionBar (1 * q) • W) = P.redFst W := by
  show P.sp _ = P.sp _
  rw [restrictAlong_heckeBetaBar_frickeInvolutionBar_smul q hα hβ]

private theorem _root_.ModularCurve.PlaceSpecialization.n1N_isStrictTypeOne_frickeInvolutionBar_smul_iff
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    P.IsStrictTypeOne (frickeInvolutionBar (1 * q) • W) ↔ P.IsStrictTypeTwo W := by
  rw [IsStrictTypeOne, IsStrictTypeTwo, n1N_redFst_frickeInvolutionBar_smul, n1N_redSnd_frickeInvolutionBar_smul]
  exact and_congr eq_comm Iff.rfl

p2m_export "ModularCurve.PlaceSpecialization" "n1N_isStrictTypeOne_frickeInvolutionBar_smul_iff"
end PlaceSpecialization

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

open Polynomial

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

omit R in

theorem n1N_ord_pos_of_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {y : F}
    (hy : y ∈ v.toValuationSubring.nonunits) (hy0 : y ≠ 0) : 0 < v.ord y := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hy
  have h0 : 0 ≤ v.ord y := Place.ord_nonneg_of_mem _ hmem
  rcases h0.lt_or_eq with h | h
  · exact h
  · exfalso
    apply (IsLocalRing.mem_maximalIdeal _).mp hmax
    have hinv : y⁻¹ ∈ v.toValuationSubring :=
      Place.mem_of_ord_nonneg _ (inv_ne_zero hy0) (by rw [Place.ord_inv, ← h, neg_zero])
    exact isUnit_iff_exists_inv.mpr ⟨⟨y⁻¹, hinv⟩, Subtype.ext (mul_inv_cancel₀ hy0)⟩

theorem n1N_uInv_mem (hu : (uFun (q := q)) ∈ R.R₁.integers) (hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0) :
    ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := by
  obtain ⟨b, hb⟩ := (R.R₁.isUnit_of_residue_ne_zero hu0).exists_right_inv
  have hb' : (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) * (b : ↥(modularFunctionFieldBar (1 * q))) = 1 := by
    have := congrArg Subtype.val hb
    exact this
  rw [← eq_inv_of_mul_eq_one_right hb']
  exact b.2

theorem n1N_residue₁_uFun_eq_aeval [IsAlgClosed k] [DecidableEq k] (hu : (uFun (q := q)) ∈ R.R₁.integers)
    (Pk : k[X])
    (hPid : ((HahnSeries.ofPowerSeries ℤ k (PowerSeries.map (Int.castRingHom k) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹
        = aeval (jqModC k) Pk) :
    R.residue₁ ⟨uFun, hu⟩ = aeval (⟨jqModC k, jqModC_mem k 1⟩ : ↥(modularFunctionFieldC k 1)) Pk := by
  apply Subtype.ext
  rw [n1N_residue₁_uFun_coe, n1N_coe_aeval_jC, ← hPid]

theorem n1N_ord_redFst_residue₁_uFun_eq_zero [IsAlgClosed k] [DecidableEq k] (hu : (uFun (q := q)) ∈ R.R₁.integers)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW : P.IsStrictTypeOne W) :
    (P.redFst W).ord (R.residue₁ ⟨uFun, hu⟩) = 0 := by
  letI := Classical.decEq (RatFunc k)
  obtain ⟨Pk, -, hroots, hPid⟩ := N1Glue.exists_monic_deltaBar_pow_inv_eq_aeval q k
  obtain ⟨x, y, -, -, hredFst, -, -, hfix⟩ := exists_coords_of_isStrictTypeOne W hW
  rw [n1N_residue₁_uFun_eq_aeval R hu Pk hPid, hredFst]
  apply n1N_ord_charLGeomPlaceOfPoint_aeval_eq_zero
  intro hroot
  exact hfix (ModularCurve.pow_q_sq_eq_self_of_mem_ssJSet q (hroots _ hroot))

theorem n1N_not_uInvFinite_of_isStrictTypeTwo [IsAlgClosed k] [DecidableEq k] (hA : A.LiesOverPrime q)
    (hu : (uFun (q := q)) ∈ R.R₁.integers)
    (hVALa : ∀ W' : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), P.IsStrictTypeOne W' →
      (P.redFst W').ord (R.residue₁ ⟨uFun, hu⟩) = 0 →
      ∃ a : A, red a ≠ 0 ∧ ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))
        - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ W'.toValuationSubring.nonunits)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (hW2 : P.IsStrictTypeTwo W) :
    ¬ UInvFinite (A := A) W := by
  rintro ⟨a₀, ha₀⟩
  set σ := frickeInvolutionBar (1 * q) with hσ
  have h1 : P.IsStrictTypeOne (σ • W) := (P.n1N_isStrictTypeOne_frickeInvolutionBar_smul_iff W).mpr hW2
  obtain ⟨a, ha, hmem⟩ := hVALa (σ • W) h1 (n1N_ord_redFst_residue₁_uFun_eq_zero R hu _ h1)

  haveI : Fact (1 * q).Prime := ⟨by rw [one_mul]; exact Fact.out⟩
  have hσσ : σ * σ = 1 := AlgEquiv.ext fun y => ModularCurve.frickeInvolutionBar_frickeInvolutionBar (1 * q) y

  have hc0 : ((((1 * q : ℕ) : AlgebraicClosure ℚ)) ^ 12) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne (1 * q)))
  set c : AlgebraicClosure ℚ := (((1 * q : ℕ) : AlgebraicClosure ℚ)) ^ 12 with hc
  have hσuinv : σ ((uFun (q := q))⁻¹) = algebraMap (AlgebraicClosure ℚ) _ c⁻¹ * (uFun (q := q)) := by
    have key : (((σ (uFun (q := q)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))
        = c • (((uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))⁻¹ :=
      ModularCurve.frickeInvolutionBar_coeffEmb_modularUnitSeries (1 * q) (modularUnitSeries_mem_modularFunctionFieldFull (1 * q))
    have key' : (((σ (uFun (q := q)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))
        = HahnSeries.C c * ((((uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))⁻¹) := by
      rw [key]
      first
      | exact HahnSeries.C_mul_eq_smul.symm
      | (rw [Algebra.smul_def, algebraMap_laurentSeries_eq_single]; rfl)
      | (rw [Algebra.smul_def]; rfl)
      | (simp only [Algebra.smul_def]; rfl)
    apply Subtype.ext
    show (((σ ((uFun (q := q))⁻¹) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))
      = algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ)) c⁻¹
          * (((uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ)))
    rw [map_inv₀, algebraMap_laurentSeries_eq_single]
    show ((((σ (uFun (q := q)) : ↥(modularFunctionFieldBar (1 * q))) : LaurentSeries (AlgebraicClosure ℚ))))⁻¹ = _
    rw [key', mul_inv, inv_inv, ← map_inv₀]
    rfl

  have h2 : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)) : ↥(modularFunctionFieldBar (1 * q)))
      - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) ∈ W.toValuationSubring.nonunits := by
    have e : σ (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) := by
      rw [map_sub, hσuinv, AlgEquiv.commutes]
    by_cases hy0 : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ) = 0
    · rw [← e, hy0, map_zero]
      exact ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mpr
        ⟨zero_mem _, by rw [show (⟨(0 : ↥(modularFunctionFieldBar (1 * q))), zero_mem _⟩ : W.toValuationSubring) = 0 from rfl]; exact Ideal.zero_mem _⟩
    · have hpos := n1N_ord_pos_of_mem_nonunits (σ • W) hmem hy0
      have hy : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ)
          = σ (σ (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))) := by
        rw [← AlgEquiv.mul_apply, hσσ, AlgEquiv.one_apply]
      rw [hy, Place.ord_smul, e] at hpos
      exact pinN_mem_nonunits_of_ord_pos W hpos

  obtain ⟨hm1, hx1⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp ha₀
  obtain ⟨hm2, hx2⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h2
  have ha₀W : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a₀ : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
    W.algebraMap_mem' _
  have haW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ) ∈ W.toValuationSubring :=
    W.algebraMap_mem' _
  have hVW : (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)) : ↥(modularFunctionFieldBar (1 * q))) ∈ W.toValuationSubring := by
    have := add_mem hm2 haW
    rwa [sub_add_cancel] at this
  have hkey : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)), hVW⟩ * ⟨_, hm1⟩ + ⟨_, ha₀W⟩ * ⟨_, hm2⟩ : W.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal W.toValuationSubring :=
    Ideal.add_mem _ (Ideal.mul_mem_left _ _ hx1) (Ideal.mul_mem_left _ _ hx2)
  have hu1 : (uFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) * (uFun (q := q))⁻¹ = 1 :=
    mul_inv_cancel₀ (n1N_uFun_ne_zero (q := q))
  have hval : ((⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)), hVW⟩ * ⟨_, hm1⟩ + ⟨_, ha₀W⟩ * ⟨_, hm2⟩ : W.toValuationSubring) : ↥(modularFunctionFieldBar (1 * q)))
      = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c⁻¹ - (a : AlgebraicClosure ℚ) * a₀) := by
    show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q))
          * (((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) - algebraMap (AlgebraicClosure ℚ) _ (a₀ : AlgebraicClosure ℚ))
        + algebraMap (AlgebraicClosure ℚ) _ (a₀ : AlgebraicClosure ℚ)
          * (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))
        = algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c⁻¹ - (a : AlgebraicClosure ℚ) * a₀)
    rw [map_sub, map_mul]
    linear_combination (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹) * hu1
  have hm : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c⁻¹ - (a : AlgebraicClosure ℚ) * a₀), W.algebraMap_mem' _⟩ : W.toValuationSubring)
      ∈ IsLocalRing.maximalIdeal W.toValuationSubring := by
    have e2 : (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c⁻¹ - (a : AlgebraicClosure ℚ) * a₀), W.algebraMap_mem' _⟩ : W.toValuationSubring)
        = ⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) c⁻¹ * (uFun (q := q)), hVW⟩ * ⟨_, hm1⟩ + ⟨_, ha₀W⟩ * ⟨_, hm2⟩ := Subtype.ext hval.symm
    rw [e2]; exact hkey
  have hzero := pinN_eq_zero_of_algebraMap_mem_maximalIdeal W _ hm
  have hprod : (a : AlgebraicClosure ℚ) * a₀ * c = 1 := by
    rw [sub_eq_zero] at hzero
    rw [← hzero, inv_mul_cancel₀ hc0]

  have hunit : IsUnit (q : A) := by
    refine isUnit_iff_exists_inv.mpr ⟨(q : A) ^ 11 * (a * a₀), Subtype.ext ?_⟩
    push_cast
    rw [hc] at hprod
    push_cast at hprod
    linear_combination hprod
  have hq : ((q : A) : AlgebraicClosure ℚ) ∈ A.nonunits := by
    have e3 : ((q : A) : AlgebraicClosure ℚ) = (q : AlgebraicClosure ℚ) := by norm_cast
    rw [e3]; exact hA
  exact (IsLocalRing.mem_maximalIdeal _ |>.mp (ValuationSubring.coe_mem_nonunits_iff.mp hq)) hunit

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"

open Polynomial

theorem n1N_mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (f : α → β) (D : α →₀ M) (v : β) :
    Finsupp.mapDomain f D v = ∑ a ∈ D.support.filter (fun a => f a = v), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = v <;> simp [Finsupp.single_apply, h]

theorem n1N_ord_eq_zero_of_sub_const_mem_nonunits {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : AlgebraicCurve.Place K F) {x : F} {c : K}
    (hc : c ≠ 0) (h : x - algebraMap K F c ∈ v.toValuationSubring.nonunits) : v.ord x = 0 := by
  obtain ⟨hmem, hmax⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp h
  have hcmem : algebraMap K F c ∈ v.toValuationSubring := v.algebraMap_mem' c
  have hxmem : x ∈ v.toValuationSubring := by
    have := add_mem hmem hcmem
    rwa [sub_add_cancel] at this
  have hcu : IsUnit (⟨algebraMap K F c, hcmem⟩ : v.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' _⟩, Subtype.ext (by
      show algebraMap K F c * algebraMap K F c⁻¹ = 1
      rw [← map_mul, mul_inv_cancel₀ hc, map_one])⟩
  have hunit : IsUnit (⟨x, hxmem⟩ : v.toValuationSubring) := by
    have e : (⟨x, hxmem⟩ : v.toValuationSubring) = ⟨algebraMap K F c, hcmem⟩ + ⟨_, hmem⟩ :=
      Subtype.ext (by push_cast; ring)
    rw [e]
    by_contra hnu
    have hm : (⟨algebraMap K F c, hcmem⟩ + ⟨_, hmem⟩ : v.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ :=
      (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have h2 := Ideal.sub_mem _ hm hmax
    rw [add_sub_cancel_right] at h2
    exact (IsLocalRing.mem_maximalIdeal _).mp h2 hcu
  have h0 := v.ord_coe_unit hunit.unit
  rw [IsUnit.unit_spec] at h0
  exact h0

theorem n1N_ord_charLGeomPlaceOfPoint_jt_sub_pos (K : Type*) [Field K] (b : K) :
    0 < (charLGeomPlaceOfPoint K b).ord
      ((⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) - algebraMap K ↥(modularFunctionFieldC K 1) b) := by
  have e : ((⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) - algebraMap K ↥(modularFunctionFieldC K 1) b)
      = aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) (X - Polynomial.C b) := by
    rw [map_sub, aeval_X, aeval_C]
  rw [e, ← n1N_ratFuncEquivCharLOneC_algebraMap]
  show 0 < (charLGeomPlaceEquiv K (AlgebraicCurve.RationalFunctionField.placeOfPoint K b)).ord _
  rw [pinN_ord_charLGeomPlaceEquiv, AlgebraicCurve.RationalFunctionField.placeOfPoint_eq_ofHeightOneSpectrum]
  have hne : (AlgebraicCurve.Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
      (AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C b))).ord
        (algebraMap K[X] (RatFunc K) (X - Polynomial.C b)) ≠ 0 := by
    rw [AlgebraicCurve.Place.ord_ofHeightOneSpectrum_ne_zero_iff (K := K) (F := RatFunc K) _ (X_sub_C_ne_zero b),
      AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal]
    exact Ideal.mem_span_singleton_self _
  have hge : 0 ≤ (AlgebraicCurve.Place.ofHeightOneSpectrum (K := K) (F := RatFunc K)
      (AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible K (irreducible_X_sub_C b))).ord
        (algebraMap K[X] (RatFunc K) (X - Polynomial.C b)) :=
    AlgebraicCurve.Place.ord_nonneg_of_mem _ (AlgebraicCurve.RationalFunctionField.algebraMap_mem_ofHeightOneSpectrum K _ _)
  omega

theorem n1N_ord_placeInfty_aeval (K : Type*) [Field K] (p : K[X]) (hp : p ≠ 0) :
    letI := Classical.decEq (RatFunc K)
    (charLGeomPlaceEquiv K (AlgebraicCurve.RationalFunctionField.placeInfty K)).ord
      (aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p) = -(p.natDegree : ℤ) := by
  letI := Classical.decEq (RatFunc K)
  rw [← n1N_ratFuncEquivCharLOneC_algebraMap, pinN_ord_charLGeomPlaceEquiv]
  exact AlgebraicCurve.RationalFunctionField.ord_placeInfty_algebraMap hp

theorem n1N_place_eq_of_ord_jt_sub_pos (K : Type*) [Field K]
    (Q Q' : AlgebraicCurve.Place K ↥(modularFunctionFieldFullC K 1)) (c : K)
    (hQ : 0 < Q.ord ((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c))
    (hQ' : 0 < Q'.ord ((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c)) :
    Q = Q' := by
  set e := (n1N_inclC K).symm with he_def
  have he : ∀ a, e.toRingEquiv (algebraMap K ↥(modularFunctionFieldFullC K 1) a) = algebraMap K ↥(modularFunctionFieldC K 1) a :=
    fun a => e.commutes a
  have hej : e (⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) = ⟨jqModC K, jqModC_mem K 1⟩ := by
    rw [he_def, AlgEquiv.symm_apply_eq]
    exact Subtype.ext (n1N_inclC_coe K ⟨jqModC K, jqModC_mem K 1⟩).symm
  have key : ∀ Q₀ : AlgebraicCurve.Place K ↥(modularFunctionFieldFullC K 1),
      0 < Q₀.ord ((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c) →
      AlgebraicCurve.Place.congrRingEquiv e.toRingEquiv he Q₀ = charLGeomPlaceOfPoint K c := by
    intro Q₀ h0
    apply eq_charLGeomPlaceOfPoint_of_ord_pos
    have e2 : (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) - algebraMap K _ c
        = e.toRingEquiv ((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c) := by
      rw [map_sub]
      show _ = e _ - e _
      rw [hej, e.commutes]
    rw [e2, AlgebraicCurve.Place.ord_congrRingEquiv]
    exact h0
  have h1 := key Q hQ
  have h2 := key Q' hQ'
  exact (AlgebraicCurve.Place.congrEquiv e.toRingEquiv he).injective (h1.trans h2.symm)

end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace N1Glue
p2m_open "ModularCurve~coeffMap_injective"

open Polynomial

theorem natDegree_ne_zero_of_deltaBar_pow_inv_eq_aeval (q : ℕ) [Fact q.Prime] (K : Type*) [Field K] (P : K[X]) (hP : P.Monic)
    (h : ((ofPowerSeries ℤ K (PowerSeries.map (Int.castRingHom K) (PowerSeries.X * dedekindEtaUnit))) ^ (q - 1))⁻¹
        = aeval (jqModC K) P) :
    P.natDegree ≠ 0 := by
  intro h0
  rw [hP.natDegree_eq_zero] at h0
  rw [h0, map_one, inv_eq_one] at h
  have hc := congrArg (fun s : LaurentSeries K => s.coeff 0) h
  beta_reduce at hc
  have h2 := (Fact.out : q.Prime).two_le
  rw [← coeffMap_deltaSeriesZ, ← map_pow, deltaSeriesZ, mul_pow, HahnSeries.single_pow, one_pow, ← map_pow, map_mul,
    coeffMap_single, map_one, coeffMap_ofPowerSeries, HahnSeries.coeff_single_mul, one_mul, ofPowerSeries_coeff_of_neg,
    HahnSeries.coeff_one] at hc
  · simp at hc
  · simp only [nsmul_eq_mul, mul_one]
    omega

end ModularCurve.N1Glue

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"

theorem n1N_jt_sub_ne_zero (K : Type*) [Field K] (c : K) :
    ((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c) ≠ 0 := by
  intro h
  have h1 := congrArg (fun z : ↥(modularFunctionFieldFullC K 1) => (z : LaurentSeries K).coeff (-1)) h
  beta_reduce at h1
  have e : (((⟨jqModC K, jqModC_mem_full K 1⟩ : ↥(modularFunctionFieldFullC K 1)) - algebraMap K _ c :
      ↥(modularFunctionFieldFullC K 1)) : LaurentSeries K) = jqModC K - algebraMap K (LaurentSeries K) c := rfl
  rw [e, HahnSeries.coeff_sub, algebraMap_laurentSeries_eq_single, HahnSeries.coeff_single_of_ne (by norm_num),
    sub_zero, coeff_jqModC_neg_one] at h1
  exact one_ne_zero (h1.trans (by rfl))

end ModularCurve

p2m_open "AlgebraicCurve IsLocalRing ModularCurve~coeffMap_injective P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.ModularCurve"

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"
namespace C4a

theorem ratFuncEquivCharLOneC_X (k : Type*) [Field k] :
    ratFuncEquivCharLOneC k RatFunc.X = ⟨jqModC k, jqModC_mem k 1⟩ := by
  apply Subtype.ext
  simp only [ratFuncEquivCharLOneC, AlgEquiv.trans_apply]
  exact RatFunc.algEquivOfTranscendental_X (f := jqModC k) (h := transcendental_jqModC k)

theorem ord_charLGeomPlaceEquiv (k : Type*) [Field k] (v₀ : Place k (RatFunc k)) (f : RatFunc k) :
    (charLGeomPlaceEquiv k v₀).ord (ratFuncEquivCharLOneC k f) = v₀.ord f :=
  Place.ord_congrRingEquiv (ratFuncEquivCharLOneC k).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC k).commutes a) v₀ f

theorem ratFuncEquivCharLOneC_algebraMap (K : Type*) [Field K] (p : Polynomial K) :
    ratFuncEquivCharLOneC K (algebraMap (Polynomial K) (RatFunc K) p)
      = Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p := by
  have h1 : algebraMap (Polynomial K) (RatFunc K) p = Polynomial.aeval (RatFunc.X : RatFunc K) p := by
    rw [← RatFunc.algebraMap_X, Polynomial.aeval_algebraMap_apply, Polynomial.aeval_X_left_apply]
  rw [h1]
  change (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) (Polynomial.aeval RatFunc.X p) = _
  rw [← Polynomial.aeval_algHom_apply]
  have h2 : (ratFuncEquivCharLOneC K : RatFunc K →ₐ[K] ↥(modularFunctionFieldC K 1)) RatFunc.X = ⟨jqModC K, jqModC_mem K 1⟩ :=
    ratFuncEquivCharLOneC_X K
  rw [h2]

theorem coe_aeval_jC (K : Type*) [Field K] (p : Polynomial K) :
    ((Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p :
        ↥(modularFunctionFieldC K 1)) : LaurentSeries K) = Polynomial.aeval (jqModC K) p :=
  (Polynomial.aeval_algHom_apply (modularFunctionFieldC K 1).val
    (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p).symm

theorem ord_charLGeomPlaceOfPoint_aeval (K : Type*) [Field K] (b : K) (p : Polynomial K) (hp : p ≠ 0) :
    (charLGeomPlaceOfPoint K b).ord (Polynomial.aeval (⟨jqModC K, jqModC_mem K 1⟩ : ↥(modularFunctionFieldC K 1)) p)
      = (Polynomial.rootMultiplicity b p : ℤ) := by
  rw [← ratFuncEquivCharLOneC_algebraMap]
  show (charLGeomPlaceEquiv K (RationalFunctionField.placeOfPoint K b)).ord _ = _
  rw [ord_charLGeomPlaceEquiv]
  exact RationalFunctionField.ord_placeOfPoint_algebraMap b hp

theorem coeffMap_aeval_jqModC {k₀ k : Type*} [Field k₀] [Field k] (θ : k₀ →+* k) (p : Polynomial k₀) :
    coeffMap θ (Polynomial.aeval (jqModC k₀) p) = Polynomial.aeval (jqModC k) (p.map θ) := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.eval₂_map, Polynomial.hom_eval₂, coeffMap_jqModC]
  congr 1
  ext c
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [algebraMap_laurentSeries_eq_single, algebraMap_laurentSeries_eq_single, coeffMap_single]

theorem ord_transport {k₀ k : Type*} [Field k₀] [Field k] (θ : k₀ →+* k)
    (y : ↥(modularFunctionFieldC k₀ 1)) (hy0 : y ≠ 0) (z : ↥(modularFunctionFieldC k 1))
    (hz : (z : LaurentSeries k) = coeffMap θ (y : LaurentSeries k₀)) :
    (∀ a₀ : k₀, (charLGeomPlaceOfPoint k (θ a₀)).ord z = (charLGeomPlaceOfPoint k₀ a₀).ord y) ∧
    (IsAlgClosed k₀ → ∀ a : k, (∀ a₀, θ a₀ ≠ a) → (charLGeomPlaceOfPoint k a).ord z = 0) := by
  classical

  obtain ⟨r, hr⟩ := (ratFuncEquivCharLOneC k₀).surjective y
  set p := r.num with hp
  set d := r.denom with hd
  have hd0 : d ≠ 0 := RatFunc.denom_ne_zero r
  have hr0 : r ≠ 0 := by rintro rfl; exact hy0 (by rw [← hr, map_zero])
  have hp0 : p ≠ 0 := RatFunc.num_ne_zero hr0
  set J₀ : ↥(modularFunctionFieldC k₀ 1) := ⟨jqModC k₀, jqModC_mem k₀ 1⟩ with hJ₀
  set J : ↥(modularFunctionFieldC k 1) := ⟨jqModC k, jqModC_mem k 1⟩ with hJ
  have hyeq : y = Polynomial.aeval J₀ p / Polynomial.aeval J₀ d := by
    rw [← hr, ← RatFunc.num_div_denom r, map_div₀, ratFuncEquivCharLOneC_algebraMap, ratFuncEquivCharLOneC_algebraMap]
  have hed0 : Polynomial.aeval J₀ d ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k₀).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k₀) (RatFunc k₀))).mpr hd0)
  have hep0 : Polynomial.aeval J₀ p ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k₀).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k₀) (RatFunc k₀))).mpr hp0)
  have hpθ0 : p.map θ ≠ 0 := (Polynomial.map_ne_zero_iff θ.injective).mpr hp0
  have hdθ0 : d.map θ ≠ 0 := (Polynomial.map_ne_zero_iff θ.injective).mpr hd0
  have heθd0 : Polynomial.aeval J (d.map θ) ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hdθ0)
  have heθp0 : Polynomial.aeval J (p.map θ) ≠ 0 := by
    rw [← ratFuncEquivCharLOneC_algebraMap]
    exact (map_ne_zero_iff _ (ratFuncEquivCharLOneC k).injective).mpr
      ((map_ne_zero_iff _ (IsFractionRing.injective (Polynomial k) (RatFunc k))).mpr hpθ0)

  have hzeq : z = Polynomial.aeval J (p.map θ) / Polynomial.aeval J (d.map θ) := by
    apply Subtype.ext
    rw [hz, hyeq]
    show coeffMap θ (((Polynomial.aeval J₀ p / Polynomial.aeval J₀ d : ↥(modularFunctionFieldC k₀ 1)) : LaurentSeries k₀))
      = ((Polynomial.aeval J (p.map θ) / Polynomial.aeval J (d.map θ) : ↥(modularFunctionFieldC k 1)) : LaurentSeries k)
    push_cast
    rw [map_div₀, coe_aeval_jC, coe_aeval_jC, coe_aeval_jC, coe_aeval_jC, coeffMap_aeval_jqModC, coeffMap_aeval_jqModC]

  have hordz : ∀ b : k, (charLGeomPlaceOfPoint k b).ord z
      = (Polynomial.rootMultiplicity b (p.map θ) : ℤ) - (Polynomial.rootMultiplicity b (d.map θ) : ℤ) := by
    intro b
    rw [hzeq, div_eq_mul_inv, Place.ord_mul _ heθp0 (inv_ne_zero heθd0), Place.ord_inv,
      ord_charLGeomPlaceOfPoint_aeval k b _ hpθ0, ord_charLGeomPlaceOfPoint_aeval k b _ hdθ0]
    ring
  have hordy : ∀ b : k₀, (charLGeomPlaceOfPoint k₀ b).ord y
      = (Polynomial.rootMultiplicity b p : ℤ) - (Polynomial.rootMultiplicity b d : ℤ) := by
    intro b
    rw [hyeq, div_eq_mul_inv, Place.ord_mul _ hep0 (inv_ne_zero hed0), Place.ord_inv,
      ord_charLGeomPlaceOfPoint_aeval k₀ b _ hp0, ord_charLGeomPlaceOfPoint_aeval k₀ b _ hd0]
    ring
  refine ⟨fun a₀ => ?_, fun hclosed a ha => ?_⟩
  · rw [hordz, hordy, ← Polynomial.eq_rootMultiplicity_map θ.injective, ← Polynomial.eq_rootMultiplicity_map θ.injective]
  · haveI := hclosed
    have hroot : ∀ s : Polynomial k₀, s ≠ 0 → Polynomial.rootMultiplicity a (s.map θ) = 0 := by
      intro s hs
      apply Polynomial.rootMultiplicity_eq_zero
      intro hroot
      have hmem : a ∈ (s.map θ).roots := (Polynomial.mem_roots ((Polynomial.map_ne_zero_iff θ.injective).mpr hs)).mpr hroot
      rw [← Polynomial.roots_map_of_injective_of_card_eq_natDegree θ.injective
        (Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits s))] at hmem
      obtain ⟨a₀, -, rfl⟩ := Multiset.mem_map.mp hmem
      exact ha a₀ rfl
    rw [hordz, hroot p hp0, hroot d hd0]
    simp

section RedNat
variable {L : Type*} [Field L] (B : Subring L) {k₀ k : Type*} [Field k₀] [Field k] (red₀ : B →+* k₀) (θ : k₀ →+* k)
  (N : ℕ) [NeZero N]

theorem coeffRed_comp (x : CharPReduction.integralCoeffs B) :
    CharPReduction.coeffRed B (θ.comp red₀) x = coeffMap θ (CharPReduction.coeffRed B red₀ x) := by
  ext n
  rw [CharPReduction.coeffRed_coeff, coeffMap_coeff, CharPReduction.coeffRed_coeff, RingHom.comp_apply]

theorem redRes_comp (s : ↥(CharPReduction.modularRing N B)) :
    CharPReduction.redRes B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s
      = coeffMap θ (CharPReduction.redRes B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s) := by
  rw [CharPReduction.redRes_apply, CharPReduction.redRes_apply, coeffRed_comp]

theorem coeffMap_injective_field : Function.Injective (coeffMap (R := k₀) (S := k) θ) := by
  intro x y h
  ext n
  have := congrArg (fun s => HahnSeries.coeff s n) h
  simp only [coeffMap_coeff] at this
  exact θ.injective this

theorem redKer_comp_iff (s : ↥(CharPReduction.modularRing N B)) :
    s ∈ CharPReduction.redKer B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B)
      ↔ s ∈ CharPReduction.redKer B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) := by
  rw [CharPReduction.redKer, RingHom.mem_ker, CharPReduction.redKer, RingHom.mem_ker, redRes_comp]
  constructor
  · intro h
    exact coeffMap_injective_field θ (by rw [h, map_zero])
  · intro h; rw [h, map_zero]

theorem mem_modularLocalized_comp_iff (g : LaurentSeries L) :
    g ∈ CharPReduction.modularLocalized N B (θ.comp red₀) ↔ g ∈ CharPReduction.modularLocalized N B red₀ := by
  rw [CharPReduction.modularLocalized, CharPReduction.modularLocalized, CharPReduction.mem_localizedAtKer,
    CharPReduction.mem_localizedAtKer]
  constructor
  · rintro ⟨r, s, hs, e⟩; exact ⟨r, s, fun h => hs ((redKer_comp_iff B red₀ θ N s).mpr h), e⟩
  · rintro ⟨r, s, hs, e⟩; exact ⟨r, s, fun h => hs ((redKer_comp_iff B red₀ θ N s).mp h), e⟩

theorem modularRedLocHom_comp (g : LaurentSeries L) (hg : g ∈ CharPReduction.modularLocalized N B (θ.comp red₀))
    (hg₀ : g ∈ CharPReduction.modularLocalized N B red₀) :
    CharPReduction.modularRedLocHom N B (θ.comp red₀) ⟨g, hg⟩
      = coeffMap θ (CharPReduction.modularRedLocHom N B red₀ ⟨g, hg₀⟩) := by
  obtain ⟨r, s, hs, e⟩ := (CharPReduction.mem_localizedAtKer _ _ _ _).mp hg₀
  have hs' : s ∉ CharPReduction.redKer B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) :=
    fun h => hs ((redKer_comp_iff B red₀ θ N s).mp h)
  have h1 := CharPReduction.redLoc_spec (A := B) (red := θ.comp red₀) (R := CharPReduction.modularRing N B)
    (hR := CharPReduction.modularRing_le_integralCoeffs N B) ⟨g, hg⟩ (r := r) (s := s) e
  have h0 := CharPReduction.redLoc_spec (A := B) (red := red₀) (R := CharPReduction.modularRing N B)
    (hR := CharPReduction.modularRing_le_integralCoeffs N B) ⟨g, hg₀⟩ (r := r) (s := s) e
  have hs0 : CharPReduction.redRes B red₀ (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs
  have hs1 : CharPReduction.redRes B (θ.comp red₀) (CharPReduction.modularRing N B) (CharPReduction.modularRing_le_integralCoeffs N B) s ≠ 0 :=
    (CharPReduction.notMem_redKer_iff _ _ _ _).mp hs'
  show CharPReduction.redLoc ⟨g, hg⟩ = coeffMap θ (CharPReduction.redLoc ⟨g, hg₀⟩)
  rw [redRes_comp, redRes_comp] at h1
  have h0' := (eq_div_iff hs0).mpr h0
  have h1' := (eq_div_iff hs1).mpr h1
  rw [h1', h0', map_div₀]
  rfl

end RedNat

theorem red_eq_zero_of_mem_maximalIdeal {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
  have hq : ((q : ℕ) : AlgebraicClosure ℚ) ∈ A := natCast_mem A q
  have hA : A.LiesOverPrime q := by
    rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff]
    have hnu : ¬ IsUnit (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) := by
      intro hu
      have h1 := hu.map red
      have h0 : red ⟨(q : AlgebraicClosure ℚ), hq⟩ = 0 := by
        have : (⟨(q : AlgebraicClosure ℚ), hq⟩ : A) = (q : A) := Subtype.ext (by push_cast; rfl)
        rw [this, map_natCast, CharP.cast_eq_zero]
      rw [h0] at h1
      exact not_isUnit_zero h1
    exact (ValuationSubring.valuation_lt_one_iff A ⟨(q : AlgebraicClosure ℚ), hq⟩).mp
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu)
  exact ValuationSubring.map_eq_zero_of_valuation_lt_one_of_charP A q hA red τ
    ((ValuationSubring.valuation_lt_one_iff A τ).mp hτ)

theorem liesOverPrime_of_ringHom {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) : A.LiesOverPrime q := by
  have hq : (q : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    have h := hunit.map red
    rw [map_natCast, CharP.cast_eq_zero] at h
    exact not_isUnit_zero h
  have h := (ValuationSubring.coe_mem_nonunits_iff (A := A)).mpr hq
  have e : (((q : A) : AlgebraicClosure ℚ)) = (q : AlgebraicClosure ℚ) := by norm_cast
  rw [e] at h
  exact h

theorem mapDomain_apply_eq_sum {α β M : Type*} [AddCommMonoid M] [DecidableEq β] (f : α → β) (D : α →₀ M) (v : β) :
    Finsupp.mapDomain f D v = ∑ a ∈ D.support.filter (fun a => f a = v), D a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases h : f a = v <;> simp [Finsupp.single_apply, h]

end C4a
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"
namespace C4b

theorem exists_sub_algebraMap_mem_nonunits {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    [IsCurveOver K F] (v : Place K F) {f : F} (hf : f ∈ v.toValuationSubring) :
    ∃ ξ : K, f - algebraMap K F ξ ∈ v.toValuationSubring.nonunits := by
  haveI : Module.Finite K v.ResidueField := IsCurveOver.finiteResidue v
  haveI : Algebra.IsIntegral K v.ResidueField := Algebra.IsIntegral.of_finite K v.ResidueField
  have hbij : Function.Bijective (algebraMap K v.ResidueField) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  obtain ⟨ξ, hξ⟩ := hbij.2 (IsLocalRing.residue v.toValuationSubring ⟨f, hf⟩)
  refine ⟨ξ, ?_⟩
  rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
  have hmem : f - algebraMap K F ξ ∈ v.toValuationSubring := sub_mem hf (v.algebraMap_mem' ξ)
  refine ⟨hmem, ?_⟩
  have e : (⟨f - algebraMap K F ξ, hmem⟩ : v.toValuationSubring) = ⟨f, hf⟩ - algebraMap K v.toValuationSubring ξ :=
    Subtype.ext rfl
  rw [e, ← Ideal.Quotient.eq]
  exact hξ.symm

theorem sub_algebraMap_ne_zero_of_ord_ne_zero {K F : Type*} [Field K] [Field F] [Algebra K F]
    (v : Place K F) {g : F} (hg : v.ord g ≠ 0) (c : K) : g - algebraMap K F c ≠ 0 := by
  intro h
  have hgc : g = algebraMap K F c := sub_eq_zero.mp h
  by_cases hc : c = 0
  · apply hg
    rw [hgc, hc, map_zero, Place.ord_zero]
  · apply hg
    rw [hgc]
    exact AlgebraicCurve.ConstantReduction.ord_algebraMap v hc

end C4b
end ModularCurve

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
namespace PlaceSpecialization
p2m_export "ModularCurve.PlaceSpecialization" "LevelOneProlongationPair jFun jqFun LevelOneProlongationPair.residue₁_apply redFst redSnd IsStrictTypeOne IsStrictTypeTwo sp d0_jN d4 redFst_eq_charLGeomPlaceOfPoint_of_ord_pos redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos redFst_eq_placeInfty_of_forall_ord_le_zero sp_eq_placeInfty_of_forall_ord_le_zero exists_levelOneProlongationPair sp_eq_charLGeomPlaceOfPoint_of_ord_pos red_surjective"
namespace LevelOneProlongationPair
p2m_export "ModularCurve.PlaceSpecialization.LevelOneProlongationPair" "residue₁ residue₁_apply residue₁_eq_modularRedLocHom residue₁_coeffMap redBar ι_coe ι R₁ redBar_residue coeffEmb_modularUnitSeries_mem_integersFst residue_coeffEmb_modularUnitSeries_ne_zero finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv"
p2m_open "ModularCurve.PlaceSpecialization.LevelOneProlongationPair ModularCurve.PlaceSpecialization ModularCurve~coeffMap_injective"

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k] {red : A →+* k}
  {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
  {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
  {P : PlaceSpecialization A q 1 data hKr k red hα hβ} (R : LevelOneProlongationPair P)

set_option maxHeartbeats 16000000 in

theorem c4b_value_mem (hu : (uFun (q := q)) ∈ R.R₁.integers) (hu' : (uFun (q := q))⁻¹ ∈ R.R₁.integers)
    (hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (c : A) (hc : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q)))
      - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring.nonunits)
    (hred : R.ReducesOnUInvChart W Q)
    (hūQ : Q.ord (R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) = 0)
    (g : ↥(modularFunctionFieldBar (1 * q))) (hg : g ∈ R.R₁.integers) (m : ℕ)
    (hint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
      (g * ((uFun (q := q))⁻¹) ^ m))
    (ξ : AlgebraicClosure ℚ) (hξ : g - algebraMap (AlgebraicClosure ℚ) _ ξ ∈ W.toValuationSubring.nonunits) :
    ξ ∈ A := by
  classical
  by_contra hξA

  have hξ0 : ξ ≠ 0 := by rintro rfl; exact hξA A.zero_mem
  have hinvA : ξ⁻¹ ∈ A := (A.mem_or_inv_mem ξ).resolve_left hξA
  have hinvm : (⟨ξ⁻¹, hinvA⟩ : A) ∈ IsLocalRing.maximalIdeal A := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    apply hξA
    obtain ⟨w, hw⟩ := hunit.exists_left_inv
    have h1 : (w : AlgebraicClosure ℚ) * ξ⁻¹ = 1 := by
      have := congrArg (fun z : A => (z : AlgebraicClosure ℚ)) hw
      simpa using this
    have hwξ : (w : AlgebraicClosure ℚ) = ξ := by
      have := congrArg (· * ξ) h1
      simp only [mul_assoc, inv_mul_cancel₀ hξ0, mul_one, one_mul] at this
      exact this
    rw [← hwξ]; exact w.2

  have hint_x : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
      {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))}) (((⟨(uFun (q := q))⁻¹, hu'⟩ : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q)))) :=
    isIntegral_algebraMap (A := ↥(modularFunctionFieldBar (1 * q)))
      (x := (⟨_, Algebra.self_mem_adjoin_singleton (AlgebraicClosure ℚ) _⟩ : Algebra.adjoin (AlgebraicClosure ℚ)
        {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))}))
  have hresinv : R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ = (R.R₁.residue ⟨uFun, hu⟩)⁻¹ := n1N_residue_uInv R hu hu'
  have hc0 : IsLocalRing.residue A c ≠ 0 := by
    intro h0
    have h1 := hred ⟨_, hu'⟩ hint_x c hc
    rw [h0, map_zero, sub_zero] at h1
    have hpos := n1N_ord_pos_of_mem_nonunits Q h1 (by rw [hresinv]; exact inv_ne_zero hu0)
    rw [hresinv, Place.ord_inv, hūQ, neg_zero] at hpos
    exact lt_irrefl _ hpos

  set x : ↥(modularFunctionFieldBar (1 * q)) := (uFun (q := q))⁻¹ with hx_def
  have hcstA : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ ∈ R.R₁.integers := by
    have := (R.n1N_constHom ⟨ξ⁻¹, hinvA⟩).2
    rwa [n1N_constHom_coe] at this
  have hh : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ * (g * x ^ m) ∈ R.R₁.integers :=
    mul_mem hcstA (mul_mem hg (pow_mem hu' m))
  have hhint : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ) {(x : ↥(modularFunctionFieldBar (1 * q)))}) (algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ * (g * x ^ m)) := by
    refine IsIntegral.mul ?_ hint
    exact isIntegral_algebraMap (A := ↥(modularFunctionFieldBar (1 * q)))
      (x := (⟨algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹, Subalgebra.algebraMap_mem _ _⟩ :
        Algebra.adjoin (AlgebraicClosure ℚ) {(x : ↥(modularFunctionFieldBar (1 * q)))}))

  obtain ⟨hgξ_mem, hgξ_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hξ
  obtain ⟨hxc_mem, hxc_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hc
  have hξW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ ∈ W.toValuationSubring := W.algebraMap_mem' _
  have hξiW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ ∈ W.toValuationSubring := W.algebraMap_mem' _
  have hcW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) (c : AlgebraicClosure ℚ) ∈ W.toValuationSubring := W.algebraMap_mem' _
  have hgW : g ∈ W.toValuationSubring := by have := add_mem hgξ_mem hξW; rwa [sub_add_cancel] at this
  have hxW : x ∈ W.toValuationSubring := by have := add_mem hxc_mem hcW; rwa [sub_add_cancel] at this
  have hhW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ * (g * x ^ m) ∈ W.toValuationSubring :=
    mul_mem hξiW (mul_mem hgW (pow_mem hxW m))
  have hcmW : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c ^ m : A) : AlgebraicClosure ℚ) ∈ W.toValuationSubring := W.algebraMap_mem' _
  have hval : algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ * (g * x ^ m)
      - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ((c ^ m : A) : AlgebraicClosure ℚ) ∈ W.toValuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal]
    refine ⟨sub_mem hhW hcmW, ?_⟩
    have ee : (⟨_, sub_mem hhW hcmW⟩ : W.toValuationSubring) = ⟨_, hhW⟩ - ⟨_, hcmW⟩ := Subtype.ext rfl
    rw [ee]

    have e1 : (⟨_, hhW⟩ : W.toValuationSubring) = ⟨_, hξiW⟩ * (⟨g, hgW⟩ * ⟨x, hxW⟩ ^ m) := Subtype.ext rfl
    have e2 : (⟨_, hcmW⟩ : W.toValuationSubring) = ⟨_, hcW⟩ ^ m :=
      Subtype.ext (by simp only [SubmonoidClass.coe_pow, map_pow])
    have e3 : (⟨_, hξiW⟩ : W.toValuationSubring) * ⟨_, hξW⟩ = 1 :=
      Subtype.ext (by
        show algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ⁻¹ * algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) ξ = 1
        rw [← map_mul, inv_mul_cancel₀ hξ0, map_one])
    rw [e1, e2]
    have e4 : (⟨_, hξiW⟩ * (⟨g, hgW⟩ * ⟨x, hxW⟩ ^ m) : W.toValuationSubring) - ⟨_, hcW⟩ ^ m
        = ⟨_, hξiW⟩ * ((⟨g, hgW⟩ - ⟨_, hξW⟩) * ⟨x, hxW⟩ ^ m)
          + (⟨x, hxW⟩ ^ m - ⟨_, hcW⟩ ^ m) := by
      have : (⟨_, hξiW⟩ * ⟨_, hξW⟩ : W.toValuationSubring) = 1 := e3
      linear_combination (⟨x, hxW⟩ ^ m : W.toValuationSubring) * this
    show (⟨_, hξiW⟩ * (⟨g, hgW⟩ * ⟨x, hxW⟩ ^ m) : W.toValuationSubring) - ⟨_, hcW⟩ ^ m ∈ IsLocalRing.maximalIdeal _
    rw [e4]
    refine add_mem (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ ?_)) ?_
    · have ee : (⟨g, hgW⟩ - ⟨_, hξW⟩ : W.toValuationSubring) = ⟨_, hgξ_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hgξ_max
    · have hxc : (⟨x, hxW⟩ - ⟨_, hcW⟩ : W.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
        have ee : (⟨x, hxW⟩ - ⟨_, hcW⟩ : W.toValuationSubring) = ⟨_, hxc_mem⟩ := Subtype.ext rfl
        rw [ee]; exact hxc_max
      obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow (⟨x, hxW⟩ : W.toValuationSubring) ⟨_, hcW⟩ m
      rw [hr]; exact Ideal.mul_mem_right _ _ hxc

  have hchart := hred ⟨_, hh⟩ hhint (c ^ m) hval
  have hres0 : R.R₁.residue ⟨_, hh⟩ = 0 := by
    have e1 : (⟨_, hh⟩ : R.R₁.integers) = R.n1N_constHom ⟨ξ⁻¹, hinvA⟩ * ⟨g * x ^ m, mul_mem hg (pow_mem hu' m)⟩ :=
      Subtype.ext (by rw [MulMemClass.coe_mul, n1N_constHom_coe])
    rw [e1, map_mul, n1N_residue_constHom, (IsLocalRing.residue_eq_zero_iff _).mpr hinvm, map_zero, zero_mul]
  rw [hres0, zero_sub, map_pow] at hchart
  obtain ⟨hm_mem, hm_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp hchart
  have hcQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c)
      ∈ Q.toValuationSubring := Q.algebraMap_mem' _
  have hneg : (-(⟨_, hcQ⟩ ^ m) : Q.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := by
    have ee : (-(⟨_, hcQ⟩ ^ m) : Q.toValuationSubring) = ⟨_, hm_mem⟩ := Subtype.ext (by push_cast; ring)
    rw [ee]; exact hm_max
  rw [neg_mem_iff] at hneg
  have hunit : IsUnit (⟨_, hcQ⟩ : Q.toValuationSubring) :=
    isUnit_iff_exists_inv.mpr ⟨⟨algebraMap (ResidueField A) _ (IsLocalRing.residue A c)⁻¹, Q.algebraMap_mem' _⟩,
      Subtype.ext (by
        show algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c)
            * algebraMap (ResidueField A) _ (IsLocalRing.residue A c)⁻¹ = 1
        rw [← map_mul, mul_inv_cancel₀ hc0, map_one])⟩
  exact (IsLocalRing.mem_maximalIdeal _).mp hneg (hunit.pow m)

set_option maxHeartbeats 16000000 in

theorem c4b_coords (hu : (uFun (q := q)) ∈ R.R₁.integers) (hu' : (uFun (q := q))⁻¹ ∈ R.R₁.integers)
    (hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (Q : Place (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1))
    (hfin : UInvFinite (A := A) W) (hred : R.ReducesOnUInvChart W Q)
    (hūQ : Q.ord (R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) = 0)
    (hj₁ : jFun (q := q) ∈ R.R₁.integers) (hj₂ : jqFun (q := q) ∈ R.R₁.integers)
    (ej : ((R.R₁.residue ⟨_, hj₁⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = jqModC (ResidueField A))
    (ejq : ((R.R₁.residue ⟨_, hj₂⟩ : modularFunctionFieldFullC (ResidueField A) 1) : LaurentSeries (ResidueField A))
      = qExpand (ResidueField A) (1 * q) (jqModC (ResidueField A)))
    (c d : A)
    (hc : 0 < W.ord ((jFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (c : AlgebraicClosure ℚ)))
    (hd : 0 < W.ord ((jqFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (d : AlgebraicClosure ℚ))) :
    R.R₁.residue ⟨jFun, hj₁⟩ - algebraMap (ResidueField A) _ (IsLocalRing.residue A c) ∈ Q.toValuationSubring.nonunits ∧
    IsLocalRing.residue A d = IsLocalRing.residue A c ^ q := by
  classical
  haveI : CharP (ResidueField A) q := (RingHom.charP_iff_charP R.redBar q).mpr inferInstance

  have hpow : R.R₁.residue ⟨jqFun, hj₂⟩ = R.R₁.residue ⟨jFun, hj₁⟩ ^ q := by
    apply Subtype.ext
    rw [ejq, SubmonoidClass.coe_pow, ej, ← qExpand_jqModC_eq_pow (ResidueField A) data hKr]
    simp only [one_mul]

  have Lj := R.residue_sub_mem_nonunits_of_reducesOnUInvChart hu hu' hu0 W Q hfin hred hūQ
    (jFun (q := q)) hj₁ 1 (isIntegral_adjoin_uInv_jFun_mul (q := q)) c (pinN_mem_nonunits_of_ord_pos W hc)
  have Ljq := R.residue_sub_mem_nonunits_of_reducesOnUInvChart hu hu' hu0 W Q hfin hred hūQ
    (jqFun (q := q)) hj₂ 2 (isIntegral_adjoin_uInv_jqFun_mul (q := q)) d (pinN_mem_nonunits_of_ord_pos W hd)
  refine ⟨Lj, ?_⟩

  obtain ⟨hLj_mem, hLj_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp Lj
  obtain ⟨hLjq_mem, hLjq_max⟩ := ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp Ljq
  have hcQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have hdQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have hρjQ : R.R₁.residue ⟨jFun, hj₁⟩ ∈ Q.toValuationSubring := by
    have := add_mem hLj_mem hcQ; simpa using this
  have hρjqQ : R.R₁.residue ⟨jqFun, hj₂⟩ ∈ Q.toValuationSubring := by
    have := add_mem hLjq_mem hdQ; simpa using this
  have f1 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρjQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcQ⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρjQ⟩ - ⟨_, hcQ⟩ : Q.toValuationSubring) = ⟨_, hLj_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hLj_max)
  have f2 : IsLocalRing.residue Q.toValuationSubring ⟨_, hρjqQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩ :=
    Ideal.Quotient.eq.mpr (by
      have ee : (⟨_, hρjqQ⟩ - ⟨_, hdQ⟩ : Q.toValuationSubring) = ⟨_, hLjq_mem⟩ := Subtype.ext rfl
      rw [ee]; exact hLjq_max)
  have hcqQ : algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q) ∈ Q.toValuationSubring :=
    Q.algebraMap_mem' _
  have g1 : (⟨_, hρjqQ⟩ : Q.toValuationSubring) = ⟨_, hρjQ⟩ ^ q := Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hpow)
  have g2 : (⟨_, hcqQ⟩ : Q.toValuationSubring) = ⟨_, hcQ⟩ ^ q := Subtype.ext (by
    show algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q)
      = (algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c)) ^ q
    rw [map_pow])
  have f3 : IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcqQ⟩ :=
    calc IsLocalRing.residue Q.toValuationSubring ⟨_, hdQ⟩
        = IsLocalRing.residue Q.toValuationSubring ⟨_, hρjqQ⟩ := f2.symm
      _ = IsLocalRing.residue Q.toValuationSubring (⟨_, hρjQ⟩ ^ q) := congrArg _ g1
      _ = (IsLocalRing.residue Q.toValuationSubring ⟨_, hρjQ⟩) ^ q := map_pow _ _ _
      _ = (IsLocalRing.residue Q.toValuationSubring ⟨_, hcQ⟩) ^ q := by rw [f1]
      _ = IsLocalRing.residue Q.toValuationSubring (⟨_, hcQ⟩ ^ q) := (map_pow _ _ _).symm
      _ = IsLocalRing.residue Q.toValuationSubring ⟨_, hcqQ⟩ := congrArg _ g2.symm
  have hdiff : (⟨_, hdQ⟩ - ⟨_, hcqQ⟩ : Q.toValuationSubring) ∈ IsLocalRing.maximalIdeal _ := Ideal.Quotient.eq.mp f3
  have ee : (⟨_, hdQ⟩ - ⟨_, hcqQ⟩ : Q.toValuationSubring)
      = ⟨algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d - IsLocalRing.residue A c ^ q),
          Q.algebraMap_mem' _⟩ := by
    apply Subtype.ext
    show algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d)
        - algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A c ^ q)
      = algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A d - IsLocalRing.residue A c ^ q)
    rw [map_sub]
  rw [ee] at hdiff
  exact sub_eq_zero.mp (pinN_eq_zero_of_algebraMap_mem_maximalIdeal Q _ hdiff)

end ModularCurve.PlaceSpecialization.LevelOneProlongationPair

namespace ModularCurve
p2m_export "ModularCurve" "mem_ssJSet_map_of_isAlgClosed ssJSet PlaceSpecialization.LevelOneProlongationPair PlaceSpecialization.LevelOneProlongationPair.residue₁_apply modularFunctionFieldBar qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qExpand_one_apply eisenstein4 dedekindEtaUnit constantCoeff_dedekindEtaUnit dedekindEtaUnitInv dedekindEtaUnit_mul_inv jNum constantCoeff_jNum jq ofPowerSeries_coeff_of_neg ModularPolynomialData jq_mem jqd_mem_full modularFunctionField_le_full coeffMap coeffMap_coeff coeffMap_single coeffMap_coeffMap coeffMap_congr algebraMap_laurentSeries_eq_single coeffEmb coeffEmb_mem_laurentBaseChange jqModC jqNModC jqModC_rat modularFunctionFieldC jqModC_mem PlaceSpecialization heckeAlphaBar coe_heckeAlphaBar heckeBetaBar coe_heckeBetaBar HeckeAlphaBarIntegral HeckeBetaBarIntegral qExpand_jqModC_eq_pow frobeniusGeomLevel frobeniusGeomLevel_jq frobOnPlacesGeomLevel mem_frobOnPlacesGeomLevel_iff frobOnPlacesGeomLevel_injective KroneckerCongruence ratFuncEquivCharLOneC charLGeomPlaceEquiv charLGeomPlaceOfPoint charLGeomPlaceOfPoint_injective transcendental_jqModC CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff CharPReduction.redRes CharPReduction.redRes_apply CharPReduction.redKer CharPReduction.notMem_redKer_iff CharPReduction.mem_localizedAtKer CharPReduction.redLoc CharPReduction.redLoc_spec CharPReduction.modularRing CharPReduction.modularRing_le_integralCoeffs CharPReduction.modularLocalized CharPReduction.modularRedLocHom frickeInvolutionBar cuspZeroBar_def isFrickeAutFull_frickeInvolutionFull cuspInftyBar jq_mem_full IsCusp coeffMap_ofPowerSeries coeffMap_jqModC modularFunctionFieldFullC jqModC_mem_full modularFunctionFieldC_le_full coeffMap_qExpand coeff_jqModC_neg_one deltaSeries deltaSeriesN deltaSeriesN_ne_zero modularUnitSeries modularUnitSeries_mem_modularFunctionFieldFull frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty eq_charLGeomPlaceOfPoint_of_ord_pos finrank_adjoin_coeffEmb_modularUnitSeries_inv hasPrincipalDivisors_modularFunctionFieldBar_unconditional isCusp_iff_ord_neg eq_cuspInftyBar_or_eq_cuspZeroBar isCusp_cuspInftyBar isCusp_cuspZeroBar ord_cuspInftyBar_coeffEmb_modularUnitSeries ord_cuspZeroBar_coeffEmb_modularUnitSeries ord_coeffEmb_modularUnitSeries_of_not_isCusp ord_cuspInftyBar_coeffEmb_jq ord_cuspInftyBar_coeffEmb_qExpand frickeInvolutionBar_frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero jWidth jWidth_eq_one_or map_intCast_pow_char_eq_qExpand delta_pow_mul_prod_jqModC_sub_pow_eq_one zero_mem_ssJSet_of_lt_five ssJSet_finite pow_q_sq_eq_self_of_mem_ssJSet restrictAlong_heckeAlphaBar_frickeInvolutionBar_smul restrictAlong_heckeBetaBar_frickeInvolutionBar_smul frickeInvolutionBar_coeffEmb_modularUnitSeries isCurveOver_modularFunctionFieldBar isCurveOver_modularFunctionFieldFullC placeSpecialization_exists_level_one_residueField exists_kroneckerCongruence_of_prime heckeAlphaBarIntegral_of_prime heckeBetaBarIntegral_of_prime"
p2m_open "ModularCurve~coeffMap_injective"
namespace C4b

p2m_open "ModularCurve.PlaceSpecialization P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.ModularCurve.PlaceSpecialization ModularCurve.PlaceSpecialization.LevelOneProlongationPair P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq.ModularCurve.PlaceSpecialization.LevelOneProlongationPair Polynomial"

set_option maxHeartbeats 16000000 in

theorem core {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (θ : ResidueField A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)))
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1)
    (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩ ≠ 0)
    (a : k) (ha : a ∉ ssJSet q k)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, (θ.comp (IsLocalRing.residue A)) x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, (θ.comp (IsLocalRing.residue A)) y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    (charLGeomPlaceOfPoint k a).ord
        (⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩, h₁F⟩ : modularFunctionFieldC k 1) = 0 := by
  classical
  letI := Classical.decEq (RatFunc (ResidueField A))
  letI := Classical.decEq (ResidueField A)
  haveI : CharP (ResidueField A) q := (RingHom.charP_iff_charP θ q).mpr inferInstance
  haveI : IsAlgClosed (ResidueField A) := ValuationSubring.isAlgClosed_residueField_algebraicClosure_rat A
  haveI : IsCurveOver (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)) := isCurveOver_modularFunctionFieldBar (1 * q)
  haveI : IsCurveOver (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) :=
    isCurveOver_modularFunctionFieldFullC (ResidueField A) 1
  have hA : A.LiesOverPrime q := ModularCurve.C4a.liesOverPrime_of_ringHom (θ.comp (IsLocalRing.residue A))

  have h₁₀ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring (IsLocalRing.residue A) :=
    (ModularCurve.C4a.mem_modularLocalized_comp_iff A.toSubring (IsLocalRing.residue A) θ (1 * q) _).mp h₁
  have hT1 := ModularCurve.C4a.modularRedLocHom_comp A.toSubring (IsLocalRing.residue A) θ (1 * q) _ h₁ h₁₀

  obtain ⟨data, hKr⟩ := ModularCurve.exists_kroneckerCongruence_of_prime q
  have hα := ModularCurve.heckeAlphaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q
  have hβ := ModularCurve.heckeBetaBarIntegral_of_prime (AlgebraicClosure ℚ) 1 q
  obtain ⟨P⟩ := ModularCurve.placeSpecialization_exists_level_one_residueField q data hKr A hA hα hβ
  obtain ⟨R⟩ := P.exists_levelOneProlongationPair hA
  obtain ⟨hf1, hres⟩ := R.residue₁_eq_modularRedLocHom f h₁₀
  set y : ↥(modularFunctionFieldC (ResidueField A) 1) := R.residue₁ ⟨f, hf1⟩ with hy_def
  have hy : ((y : ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A))
      = CharPReduction.modularRedLocHom (1 * q) A.toSubring (IsLocalRing.residue A) ⟨_, h₁₀⟩ := hres
  have hz : ((⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring (θ.comp (IsLocalRing.residue A)) ⟨_, h₁⟩, h₁F⟩ :
      ↥(modularFunctionFieldC k 1)) : LaurentSeries k) = coeffMap θ (y : LaurentSeries (ResidueField A)) := by
    rw [hy]; exact hT1
  have hy0 : y ≠ 0 := by
    intro h0
    apply h₁0
    rw [hT1, ← hy, h0]
    show coeffMap θ ((0 : ↥(modularFunctionFieldC (ResidueField A) 1)) : LaurentSeries (ResidueField A)) = 0
    rw [ZeroMemClass.coe_zero, map_zero]
  have hfres0 : R.R₁.residue ⟨f, hf1⟩ ≠ 0 := by
    intro h0; apply hy0
    rw [hy_def, ModularCurve.PlaceSpecialization.LevelOneProlongationPair.residue₁_apply, h0, map_zero]
  obtain ⟨hTa, hTb⟩ := ModularCurve.C4a.ord_transport θ y hy0 _ hz
  by_cases har : ∃ a₀, θ a₀ = a
  swap
  · push_neg at har
    exact hTb inferInstance a har
  obtain ⟨a₀, rfl⟩ := har
  rw [hTa a₀]

  obtain ⟨hu, -⟩ := coeffEmb_modularUnitSeries_mem_integersFst R
  change (uFun (q := q)) ∈ R.R₁.integers at hu
  have hu0 : R.R₁.residue ⟨uFun, hu⟩ ≠ 0 := residue_coeffEmb_modularUnitSeries_ne_zero R hu
  have hu' : ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) ∈ R.R₁.integers := n1N_uInv_mem R hu hu0
  have hresinv : R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ = (R.R₁.residue ⟨uFun, hu⟩)⁻¹ := n1N_residue_uInv R hu hu'

  obtain ⟨Pk, hPkmonic, hroots, hPkid⟩ := N1Glue.exists_monic_deltaBar_pow_inv_eq_aeval q (ResidueField A)
  have hū_eq : R.residue₁ ⟨uFun, hu⟩ = aeval (⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) 1⟩ :
      ↥(modularFunctionFieldC (ResidueField A) 1)) Pk := n1N_residue₁_uFun_eq_aeval R hu Pk hPkid
  have hPk0 : Pk ≠ 0 := hPkmonic.ne_zero
  have hPkdeg : Pk.natDegree ≠ 0 := N1Glue.natDegree_ne_zero_of_deltaBar_pow_inv_eq_aeval q (ResidueField A) Pk hPkmonic hPkid
  have hPka₀ : Pk.eval a₀ ≠ 0 := fun h0 =>
    ha (ModularCurve.mem_ssJSet_map_of_isAlgClosed θ a₀ (hroots a₀ h0))

  obtain ⟨Q, -, hQord⟩ := asmN_exists_place_comap_iota R (charLGeomPlaceOfPoint (ResidueField A) a₀)
  have hūv : (charLGeomPlaceOfPoint (ResidueField A) a₀).ord (R.residue₁ ⟨uFun, hu⟩) = 0 := by
    rw [hū_eq]
    exact n1N_ord_charLGeomPlaceOfPoint_aeval_eq_zero _ _ _ hPka₀
  have hūQ : Q.ord (R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1)) = 0 := by
    rw [hQord, ← residue₁_apply]; exact hūv
  have hQx : R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩ ∈ Q.toValuationSubring :=
    Place.mem_of_ord_nonneg _ (by rw [hresinv]; exact inv_ne_zero hu0) (by rw [hresinv, Place.ord_inv, hūQ, neg_zero])

  obtain ⟨Qi, -, hQiord⟩ := asmN_exists_place_comap_iota R (charLGeomPlaceEquiv (ResidueField A) (RationalFunctionField.placeInfty (ResidueField A)))
  have hordinf : (charLGeomPlaceEquiv (ResidueField A) (RationalFunctionField.placeInfty (ResidueField A))).ord (R.residue₁ ⟨uFun, hu⟩) = -(Pk.natDegree : ℤ) := by
    rw [hū_eq]
    exact n1N_ord_placeInfty_aeval (ResidueField A) Pk hPk0
  have hQi_inv : Qi.ord (R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩) = (Pk.natDegree : ℤ) := by
    rw [hQiord, hresinv, map_inv₀, Place.ord_inv, ← residue₁_apply, hordinf, neg_neg]
  have hx_tr : Transcendental (ResidueField A) (R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩) :=
    Place.transcendental_of_ord_ne_zero Qi (by rw [hQi_inv]; exact_mod_cast hPkdeg)

  have hq2 := (Fact.out : q.Prime).two_le
  have hdeg_down : Module.finrank (IntermediateField.adjoin (ResidueField A)
      ({(R.R₁.residue ⟨uFun, hu⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1))⁻¹} :
        Set ↥(modularFunctionFieldFullC (ResidueField A) 1))) ↥(modularFunctionFieldFullC (ResidueField A) 1) = q - 1 :=
    finrank_adjoin_residue_coeffEmb_modularUnitSeries_inv R hu
  have hdeg : Module.finrank (IntermediateField.adjoin (AlgebraicClosure ℚ)
        ({(((⟨(uFun (q := q))⁻¹, hu'⟩ : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q))))} : Set ↥(modularFunctionFieldBar (1 * q))))
        ↥(modularFunctionFieldBar (1 * q))
      = Module.finrank (IntermediateField.adjoin (ResidueField A)
          ({R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩} : Set ↥(modularFunctionFieldFullC (ResidueField A) 1)))
          ↥(modularFunctionFieldFullC (ResidueField A) 1) := by
    rw [hresinv, hdeg_down]
    exact ModularCurve.finrank_adjoin_coeffEmb_modularUnitSeries_inv (q := q)
  have hfin : 0 < Module.finrank (IntermediateField.adjoin (ResidueField A)
          ({R.R₁.residue ⟨(uFun (q := q))⁻¹, hu'⟩} : Set ↥(modularFunctionFieldFullC (ResidueField A) 1)))
          ↥(modularFunctionFieldFullC (ResidueField A) 1) := by
    rw [hresinv, hdeg_down]
    omega
  have hchart := exists_isIntegral_and_residue_eq_of_isIntegral_adjoin_residue_modularUnitSeries_inv R hu'

  have hιj : R.ι ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ = ⟨jqModC (ResidueField A), jqModC_mem (ResidueField A) 1⟩ :=
    Subtype.ext (by rw [R.ι_coe]; exact coeffMap_jqModC _)
  have hιc : ∀ c : A, R.ι (algebraMap (ResidueField A) _ (IsLocalRing.residue A c))
      = algebraMap (ResidueField A) _ (IsLocalRing.residue A c) := fun c => by
    rw [asmN_iota_algebraMap, R.redBar_residue]
  obtain ⟨hj₁, ej⟩ := pinN_exists_jFun_mem_integers₁ R
  obtain ⟨hj₂, ejq⟩ := pinN_exists_jqFun_mem_integers₁ R
  have hjres' : R.R₁.residue ⟨jFun, hj₁⟩ = ⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ := Subtype.ext ej

  obtain ⟨D, hD, -⟩ := (ModularCurve.hasPrincipalDivisors_modularFunctionFieldBar_unconditional (1 * q)).exists_divisor f
    (by intro h0; apply hfres0; simp only [h0]; exact map_zero _)

  have hT : ∀ W, W ∈ (∅ : Finset (Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))) ↔
      (D W ≠ 0 ∧ UInvFinite (A := A) W ∧ R.ReducesOnUInvChart W Q) := by
    intro W
    simp only [Finset.notMem_empty, false_iff, not_and]
    intro hDW hfinW hredW
    obtain ⟨c, hc⟩ := id hfinW

    have hint_x : IsIntegral (Algebra.adjoin (AlgebraicClosure ℚ)
        {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))})
        (((⟨(uFun (q := q))⁻¹, hu'⟩ : R.R₁.integers) : ↥(modularFunctionFieldBar (1 * q)))) :=
      isIntegral_algebraMap (A := ↥(modularFunctionFieldBar (1 * q)))
        (x := (⟨_, Algebra.self_mem_adjoin_singleton (AlgebraicClosure ℚ) _⟩ : Algebra.adjoin (AlgebraicClosure ℚ)
          {(((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) : ↥(modularFunctionFieldBar (1 * q)))}))
    have hc0 : IsLocalRing.residue A c ≠ 0 := by
      intro h0
      have h1 := hredW ⟨_, hu'⟩ hint_x c hc
      rw [h0, map_zero, sub_zero] at h1
      have hpos := n1N_ord_pos_of_mem_nonunits Q h1 (by rw [hresinv]; exact inv_ne_zero hu0)
      rw [hresinv, Place.ord_inv, hūQ, neg_zero] at hpos
      exact lt_irrefl _ hpos
    have hc0' : (c : AlgebraicClosure ℚ) ≠ 0 := by
      intro h; apply hc0
      have : c = 0 := Subtype.ext h
      rw [this, map_zero]
    have hordu : W.ord ((uFun (q := q))⁻¹ : ↥(modularFunctionFieldBar (1 * q))) = 0 :=
      n1N_ord_eq_zero_of_sub_const_mem_nonunits W hc0' hc
    have hnc : ¬ IsCusp (⟨coeffEmb (AlgebraicClosure ℚ) jq,
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) W := by
      rcases pinN_uInv_regular_cases (q := q) W (le_of_eq hordu.symm) with ⟨hnc, -⟩ | ⟨-, h1⟩
      · exact hnc
      · exfalso
        rw [hordu] at h1
        have : (2 : ℤ) ≤ ((1 * q : ℕ) : ℤ) := by push_cast; omega
        omega

    have hjW : 0 ≤ W.ord (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) :=
      not_lt.mp fun hlt => hnc ((ModularCurve.isCusp_iff_ord_neg _ _).mpr hlt)
    have hjqW : 0 ≤ W.ord (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) := pinN_ord_jqFun_nonneg_of_not_isCusp (q := q) W hnc
    obtain ⟨ξ, hξ⟩ := C4b.exists_sub_algebraMap_mem_nonunits W
      (Place.mem_of_ord_nonneg _ (pinN_jFun_ne_zero (q := q)) hjW)
    obtain ⟨η, hη⟩ := C4b.exists_sub_algebraMap_mem_nonunits W
      (Place.mem_of_ord_nonneg _ (pinN_jqFun_ne_zero (q := q)) hjqW)

    have hξA : ξ ∈ A := c4b_value_mem R hu hu' hu0 W Q c hc hredW hūQ (jFun (q := q)) hj₁ 1
      (isIntegral_adjoin_uInv_jFun_mul (q := q)) ξ hξ
    have hηA : η ∈ A := c4b_value_mem R hu hu' hu0 W Q c hc hredW hūQ (jqFun (q := q)) hj₂ 2
      (isIntegral_adjoin_uInv_jqFun_mul (q := q)) η hη
    set x : A := ⟨ξ, hξA⟩
    set yy : A := ⟨η, hηA⟩
    have hxpos : 0 < W.ord ((jFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (x : AlgebraicClosure ℚ)) :=
      n1N_ord_pos_of_mem_nonunits W hξ (C4b.sub_algebraMap_ne_zero_of_ord_ne_zero (cuspInftyBar (1 * q))
        (by rw [show (jFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) jq,
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full (1 * q))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
            ModularCurve.ord_cuspInftyBar_coeffEmb_jq (1 * q)]; norm_num) ξ)
    have hypos : 0 < W.ord ((jqFun (q := q)) - algebraMap (AlgebraicClosure ℚ) _ (yy : AlgebraicClosure ℚ)) :=
      n1N_ord_pos_of_mem_nonunits W hη (C4b.sub_algebraMap_ne_zero_of_ord_ne_zero (cuspInftyBar (1 * q))
        (by rw [show (jqFun (q := q) : ↥(modularFunctionFieldBar (1 * q))) = (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
            coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : ↥(modularFunctionFieldBar (1 * q))) from rfl,
            ModularCurve.ord_cuspInftyBar_coeffEmb_qExpand (1 * q) (1 * q) (dvd_refl _)]
            push_cast; omega) η)

    obtain ⟨Lj, hyx⟩ := c4b_coords R hu hu' hu0 W Q hfinW hredW hūQ hj₁ hj₂ ej ejq x yy hxpos hypos

    rw [hjres'] at Lj
    have hposx := n1N_ord_pos_of_mem_nonunits Q Lj (n1N_jt_sub_ne_zero _ _)
    obtain ⟨ã, hã⟩ := IsLocalRing.residue_surjective a₀
    have hposa : 0 < Q.ord ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ :
        ↥(modularFunctionFieldFullC (ResidueField A) 1)) - algebraMap (ResidueField A) _ (IsLocalRing.residue A ã)) := by
      rw [hQord, map_sub, hιj, hιc, hã]
      exact n1N_ord_charLGeomPlaceOfPoint_jt_sub_pos (ResidueField A) a₀
    have hxa : IsLocalRing.residue A x = a₀ := by
      rw [← hã]
      by_contra hne
      have hdiff := Ideal.sub_mem _
        (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (pinN_mem_nonunits_of_ord_pos Q hposx)).2
        (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (pinN_mem_nonunits_of_ord_pos Q hposa)).2
      have ee : ((⟨_, (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (pinN_mem_nonunits_of_ord_pos Q hposx)).1⟩ : Q.toValuationSubring)
          - ⟨_, (ValuationSubring.mem_nonunits_iff_exists_mem_maximalIdeal.mp (pinN_mem_nonunits_of_ord_pos Q hposa)).1⟩)
          = ⟨algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1)
              (IsLocalRing.residue A ã - IsLocalRing.residue A x), Q.algebraMap_mem' _⟩ := by
        apply Subtype.ext
        show ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1))
              - algebraMap (ResidueField A) _ (IsLocalRing.residue A x))
            - ((⟨jqModC (ResidueField A), jqModC_mem_full (ResidueField A) 1⟩ : ↥(modularFunctionFieldFullC (ResidueField A) 1))
              - algebraMap (ResidueField A) _ (IsLocalRing.residue A ã))
          = algebraMap (ResidueField A) ↥(modularFunctionFieldFullC (ResidueField A) 1) (IsLocalRing.residue A ã - IsLocalRing.residue A x)
        rw [map_sub]
        ring
      rw [ee] at hdiff
      exact hne (sub_eq_zero.mp (pinN_eq_zero_of_algebraMap_mem_maximalIdeal Q _ hdiff)).symm

    have hordW : W.ord f ≠ 0 := by rw [← hD]; exact hDW
    refine hsupp W hordW ⟨⟨x, ?_, hxpos⟩, ⟨yy, ?_, hypos⟩⟩
    · rw [RingHom.comp_apply, hxa]
    · rw [RingHom.comp_apply, hyx, map_pow, hxa]
  have h1b := AlgebraicCurve.RegularProlongation.sum_ord_eq_ord_residue_of_residue_integralClosure_surjective A R.R₁
    ⟨(uFun (q := q))⁻¹, hu'⟩ hx_tr hfin hdeg hchart ⟨f, hf1⟩ hfres0 Q hQx D hD ∅ hT
  rw [Finset.sum_empty] at h1b
  rw [hy_def, residue₁_apply, ← hQord]
  exact h1b.symm

end C4b
end ModularCurve

theorem solution
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (f : ↥(modularFunctionFieldBar (1 * q)))
    (h₁ : (f : LaurentSeries (AlgebraicClosure ℚ)) ∈ CharPReduction.modularLocalized (1 * q) A.toSubring red)
    (h₁F : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ∈ modularFunctionFieldC k 1) (h₁0 : CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩ ≠ 0)
    (a : k) (ha : a ∉ ssJSet q k) (ha2 : a ^ (q ^ 2) = a)
    (hsupp : ∀ W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)), W.ord f ≠ 0 →
      ¬ ((∃ x : A, red x = a ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (x : AlgebraicClosure ℚ))) ∧
         (∃ y : A, red y = a ^ q ∧
            0 < W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ (1 * q) jq),
              coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
                (jqd_mem_full (1 * q) (dvd_refl (1 * q)))⟩ : modularFunctionFieldBar (1 * q)) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ))))) :
    (charLGeomPlaceOfPoint k a).ord
        (⟨CharPReduction.modularRedLocHom (1 * q) A.toSubring red ⟨_, h₁⟩, h₁F⟩ : modularFunctionFieldC k 1) = 0 := by
  have hkerm : ∀ τ : ↥A, τ ∈ IsLocalRing.maximalIdeal ↥A → red τ = 0 := fun τ hτ =>
    ModularCurve.C4a.red_eq_zero_of_mem_maximalIdeal red q τ hτ
  obtain ⟨θ, hθ⟩ : ∃ θ : ResidueField A →+* k, θ.comp (IsLocalRing.residue A) = red :=
    ⟨Ideal.Quotient.lift (IsLocalRing.maximalIdeal ↥A) red hkerm,
      RingHom.ext fun τ => Ideal.Quotient.lift_mk (IsLocalRing.maximalIdeal ↥A) red hkerm⟩
  subst hθ
  exact ModularCurve.C4b.core θ f h₁ h₁F h₁0 a ha hsupp

end

end S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq
end P2MW
export P2MW.S_ModularCurve_ord_charLGeomPlaceOfPoint_modularRedLocHom_eq_zero_of_not_mem_ssJSet_of_pow_sq_eq (solution)
