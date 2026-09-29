-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_anharmonic_mulSemiringAction_lambdaFieldOver
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/7d9f726e-9792-5a8f-b543-b9fe4a6ba744

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero"
p2m_attr_erase "simp" "ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option maxHeartbeats 3200000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_injective qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap transcendental_lambdaModC qExpand_two_jq_mul_lambdaModC_sq"
p2m_open "ModularCurve"
namespace Ws30EG

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

scoped instance instCharZeroLQ : CharZero LQ := charZero_of_injective_algebraMap (algebraMap Qb LQ).injective

section Anharmonic
variable {F : Type*} [Field F]

def anh (i : Fin 6) (t : F) : F :=
  match i with
  | 0 => t
  | 1 => 16⁻¹ - t
  | 2 => (256 * t)⁻¹
  | 3 => (16 - 256 * t)⁻¹
  | 4 => t * (16 * t - 1)⁻¹
  | 5 => (16 * t - 1) * (256 * t)⁻¹

def τs : Fin 6 → Fin 6
  | 0 => 1 | 1 => 0 | 2 => 3 | 3 => 2 | 4 => 5 | 5 => 4

def τi : Fin 6 → Fin 6
  | 0 => 2 | 1 => 5 | 2 => 0 | 3 => 4 | 4 => 3 | 5 => 1

def jexpr (t : F) : F := (256 * t ^ 2 - 16 * t + 1) ^ 3 / (t ^ 2 * (16 * t - 1) ^ 2)

theorem map_anh {F' φ : Type*} [Field F'] [FunLike φ F F'] [RingHomClass φ F F']
    (f : φ) (i : Fin 6) (t : F) : f (anh i t) = anh i (f t) := by
  fin_cases i <;> simp [anh, map_sub, map_inv₀, map_mul, map_ofNat, map_one]

theorem map_jexpr {F' φ : Type*} [Field F'] [FunLike φ F F'] [RingHomClass φ F F']
    (f : φ) (t : F) : f (jexpr t) = jexpr (f t) := by
  simp [jexpr, map_sub, map_div₀, map_mul, map_ofNat, map_one, map_pow, map_add]

variable [CharZero F] {t : F}

theorem nv_aux (h0 : t ≠ 0) (h1 : 16 * t - 1 ≠ 0) :
    16 - 256 * t ≠ 0 ∧ 1 - 16 * t ≠ 0 ∧ (16 : F)⁻¹ - t ≠ 0 ∧ 256 * t ≠ 0 := by
  refine ⟨fun h => h1 ?_, fun h => h1 ?_, fun h => h1 ?_, fun h => h0 ?_⟩
  · linear_combination (-1/16 : F) * h
  · linear_combination (-1 : F) * h
  · linear_combination (-16 : F) * h
  · linear_combination (1/256 : F) * h

theorem anh_anh_one (h0 : t ≠ 0) (h1 : 16 * t - 1 ≠ 0) (i : Fin 6) : anh i (anh 1 t) = anh (τs i) t := by
  obtain ⟨h2, h3, h4, h5⟩ := nv_aux h0 h1
  fin_cases i <;>
  · simp only [anh, τs]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring

theorem anh_anh_two (h0 : t ≠ 0) (h1 : 16 * t - 1 ≠ 0) (i : Fin 6) : anh i (anh 2 t) = anh (τi i) t := by
  obtain ⟨h2, h3, h4, h5⟩ := nv_aux h0 h1
  fin_cases i
  · simp only [anh, τi]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring
  · simp only [anh, τi]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring
  · simp only [anh, τi]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring
  · simp only [anh, τi]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring
  · simp only [anh, τi]
    rw [← mul_inv]
    congr 1
    rw [mul_sub, mul_one, ← mul_assoc, mul_comm (256 * t) 16, mul_assoc, mul_inv_cancel₀ h5, mul_one]
  · simp only [anh, τi]
    try ring_nf
    try ring_nf at h0 h1 h2 h3 h4 h5
    try field_simp
    try ring

theorem jexpr_anh_one (h0 : t ≠ 0) (h1 : 16 * t - 1 ≠ 0) : jexpr (anh 1 t) = jexpr t := by
  obtain ⟨h2, h3, h4, h5⟩ := nv_aux h0 h1
  simp only [anh, jexpr]
  rw [div_eq_div_iff (mul_ne_zero (pow_ne_zero _ h4) (pow_ne_zero _ (by
      intro h; apply h0; linear_combination (-1/16 : F) * h))) (mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h1))]
  ring

theorem jexpr_anh_two (h0 : t ≠ 0) (h1 : 16 * t - 1 ≠ 0) : jexpr (anh 2 t) = jexpr t := by
  obtain ⟨h2, h3, h4, h5⟩ := nv_aux h0 h1
  have h1' : t * 16 - 1 ≠ 0 := by rw [mul_comm]; exact h1
  have h2' : 16 - t * 256 ≠ 0 := by rw [mul_comm]; exact h2
  have h3' : 1 - t * 16 ≠ 0 := by rw [mul_comm]; exact h3
  have h5' : t * 256 ≠ 0 := by rw [mul_comm]; exact h5
  simp only [anh, jexpr]
  field_simp
  ring

end Anharmonic

section MuFacts

theorem mu_transcendental : Transcendental Qb (lambdaModC Qb) := ModularCurve.transcendental_lambdaModC Qb

theorem mu_ne_zero : lambdaModC Qb ≠ 0 := fun h => mu_transcendental (h ▸ isAlgebraic_zero)

theorem mu16_ne : 16 * lambdaModC Qb - 1 ≠ 0 := by
  intro h
  have key : lambdaModC Qb = algebraMap Qb LQ 16⁻¹ := by
    rw [map_inv₀, map_ofNat]; linear_combination (1/16 : LQ) * h
  exact mu_transcendental (key ▸ isAlgebraic_algebraMap _)

theorem anh_one_mu_ne : anh 1 (lambdaModC Qb) ≠ lambdaModC Qb := by
  intro h
  have key : lambdaModC Qb = algebraMap Qb LQ 32⁻¹ := by
    rw [map_inv₀, map_ofNat]; simp only [anh] at h; linear_combination (-1/2 : LQ) * h
  exact mu_transcendental (key ▸ isAlgebraic_algebraMap _)

theorem anh_three_mu_ne : anh 3 (lambdaModC Qb) ≠ lambdaModC Qb := by
  intro h
  simp only [anh] at h
  have h16 : 16 - 256 * lambdaModC Qb ≠ 0 := (nv_aux mu_ne_zero mu16_ne).1
  have key : 256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1 = 0 := by
    have := inv_mul_cancel₀ h16
    rw [h] at this
    linear_combination (-1 : LQ) * this
  refine mu_transcendental ⟨Polynomial.C 256 * Polynomial.X ^ 2 - Polynomial.C 16 * Polynomial.X + 1, ?_, ?_⟩
  · intro h0; have := congrArg (Polynomial.coeff · 0) h0; simp at this
  · simp only [map_add, map_sub, map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X, map_one]
    rw [map_ofNat, map_ofNat]
    exact key

variable (q : ℕ) [Fact q.Prime]

theorem muq_ne_zero : lambdaNModC Qb q ≠ 0 := by
  rw [lambdaNModC]; exact (map_ne_zero_iff _ (qExpand_injective q)).mpr mu_ne_zero

theorem muq16_ne : 16 * lambdaNModC Qb q - 1 ≠ 0 := by
  have h := (map_ne_zero_iff _ (qExpand_injective (R := Qb) q)).mpr mu16_ne
  simpa only [map_sub, map_mul, map_ofNat, map_one, lambdaNModC] using h

omit [Fact q.Prime] in
theorem qExpand_algebraMap (N : ℕ) [NeZero N] (c : Qb) :
    qExpand Qb N (algebraMap Qb LQ c) = algebraMap Qb LQ c := by
  rw [ModularCurve.algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero]

theorem jLambda_Qb :
    qExpand Qb 2 (jqModC Qb) * lambdaModC Qb ^ 2 * (16 * lambdaModC Qb - 1) ^ 2
      = (256 * lambdaModC Qb ^ 2 - 16 * lambdaModC Qb + 1) ^ 3 := by
  have h := congrArg (laurentMap (algebraMap ℚ Qb)) ModularCurve.qExpand_two_jq_mul_lambdaModC_sq
  have hj : laurentMap (algebraMap ℚ Qb) jq = jqModC Qb := by
    rw [← jqModC_rat]; exact map_jqModC (algebraMap ℚ Qb)
  have hμ : laurentMap (algebraMap ℚ Qb) (lambdaModC ℚ) = lambdaModC Qb := by
    rw [lambdaModC, lambdaModC, laurentMap_laurentMap]
    exact congrArg (fun g => laurentMap g lambdaInt) (RingHom.ext_int _ _)
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, laurentMap_qExpand, hj, hμ, map_ofNat] using h

theorem jLambda_Qb_q :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) jLambda_Qb
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

theorem jexpr_mu_eq : jexpr (lambdaModC Qb) = qExpand Qb 2 (jqModC Qb) := by
  rw [jexpr, div_eq_iff (mul_ne_zero (pow_ne_zero _ mu_ne_zero) (pow_ne_zero _ mu16_ne)), ← jLambda_Qb]
  ring

theorem jexpr_muq_eq : jexpr (lambdaNModC Qb q) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
  rw [jexpr, div_eq_iff (mul_ne_zero (pow_ne_zero _ (muq_ne_zero q)) (pow_ne_zero _ (muq16_ne q))),
    ← jLambda_Qb_q]
  ring

end MuFacts

section Field

variable (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ Qb)

abbrev μL : ↥(lambdaFieldOver q K) := ⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩

abbrev μqL : ↥(lambdaFieldOver q K) := ⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩

def Val (g : RingAut ↥(lambdaFieldOver q K)) (i : Fin 6) : Prop :=
  ((g (μL q K) : ↥(lambdaFieldOver q K)) : LQ) = anh i (lambdaModC Qb) ∧
    ((g (μqL q K) : ↥(lambdaFieldOver q K)) : LQ) = anh i (lambdaNModC Qb q)

def FixC (g : RingAut ↥(lambdaFieldOver q K)) : Prop :=
  ∀ x : ↥(lambdaFieldOver q K), (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → g x = x

theorem val_one : Val q K 1 0 := ⟨rfl, rfl⟩

theorem fixC_one : FixC q K 1 := fun _ _ => rfl

variable {q K}

theorem fixC_mul {x y : RingAut ↥(lambdaFieldOver q K)} (hx : FixC q K x) (hy : FixC q K y) :
    FixC q K (x * y) := fun z hz => by
  show x (y z) = z
  rw [hy z hz, hx z hz]

theorem coe_apply_anh (x : RingAut ↥(lambdaFieldOver q K)) (b : Fin 6) (z : ↥(lambdaFieldOver q K)) :
    ((x (anh b z) : ↥(lambdaFieldOver q K)) : LQ) = anh b ((x z : ↥(lambdaFieldOver q K)) : LQ) := by
  rw [map_anh x]
  exact map_anh (lambdaFieldOver q K).subtype b _

theorem eq_anh_of_coe {y : ↥(lambdaFieldOver q K)} {b : Fin 6} {z : ↥(lambdaFieldOver q K)}
    (h : (y : LQ) = anh b (z : LQ)) : y = anh b z :=
  Subtype.ext (h.trans (map_anh (lambdaFieldOver q K).subtype b z).symm)

theorem val_mul_one {x y : RingAut ↥(lambdaFieldOver q K)} (hx : Val q K x 1) {b : Fin 6} (hy : Val q K y b) :
    Val q K (x * y) (τs b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · show ((x (y (μL q K)) : ↥(lambdaFieldOver q K)) : LQ) = _
    rw [eq_anh_of_coe (z := μL q K) hy1, coe_apply_anh, hx1]
    exact anh_anh_one mu_ne_zero mu16_ne b
  · show ((x (y (μqL q K)) : ↥(lambdaFieldOver q K)) : LQ) = _
    rw [eq_anh_of_coe (z := μqL q K) hy2, coe_apply_anh, hx2]
    exact anh_anh_one (muq_ne_zero q) (muq16_ne q) b

theorem val_mul_two {x y : RingAut ↥(lambdaFieldOver q K)} (hx : Val q K x 2) {b : Fin 6} (hy : Val q K y b) :
    Val q K (x * y) (τi b) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · show ((x (y (μL q K)) : ↥(lambdaFieldOver q K)) : LQ) = _
    rw [eq_anh_of_coe (z := μL q K) hy1, coe_apply_anh, hx1]
    exact anh_anh_two mu_ne_zero mu16_ne b
  · show ((x (y (μqL q K)) : ↥(lambdaFieldOver q K)) : LQ) = _
    rw [eq_anh_of_coe (z := μqL q K) hy2, coe_apply_anh, hx2]
    exact anh_anh_two (muq_ne_zero q) (muq16_ne q) b

theorem coe_apply_jexpr {x : RingAut ↥(lambdaFieldOver q K)} {a : Fin 6} (hx : Val q K x a) :
    ((x (jexpr (μL q K)) : ↥(lambdaFieldOver q K)) : LQ) = jexpr (anh a (lambdaModC Qb)) ∧
    ((x (jexpr (μqL q K)) : ↥(lambdaFieldOver q K)) : LQ) = jexpr (anh a (lambdaNModC Qb q)) := by
  constructor
  · rw [map_jexpr x, ← hx.1]; exact map_jexpr (lambdaFieldOver q K).subtype _
  · rw [map_jexpr x, ← hx.2]; exact map_jexpr (lambdaFieldOver q K).subtype _

theorem coe_jexpr_μL : ((jexpr (μL q K) : ↥(lambdaFieldOver q K)) : LQ) = qExpand Qb 2 (jqModC Qb) := by
  rw [← jexpr_mu_eq]; exact map_jexpr (lambdaFieldOver q K).subtype _

theorem coe_jexpr_μqL :
    ((jexpr (μqL q K) : ↥(lambdaFieldOver q K)) : LQ) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
  rw [← jexpr_muq_eq]; exact map_jexpr (lambdaFieldOver q K).subtype _

theorem apply_jexpr_of_val {x : RingAut ↥(lambdaFieldOver q K)} {a : Fin 6} (hx : Val q K x a) (ha : a = 1 ∨ a = 2) :
    x (jexpr (μL q K)) = jexpr (μL q K) ∧ x (jexpr (μqL q K)) = jexpr (μqL q K) := by
  obtain ⟨h1, h2⟩ := coe_apply_jexpr hx
  have e1 : ((jexpr (μL q K) : ↥(lambdaFieldOver q K)) : LQ) = jexpr (lambdaModC Qb) :=
    map_jexpr (lambdaFieldOver q K).subtype _
  have e2 : ((jexpr (μqL q K) : ↥(lambdaFieldOver q K)) : LQ) = jexpr (lambdaNModC Qb q) :=
    map_jexpr (lambdaFieldOver q K).subtype _
  rcases ha with rfl | rfl
  · exact ⟨Subtype.ext (by rw [h1, e1, jexpr_anh_one mu_ne_zero mu16_ne]),
      Subtype.ext (by rw [h2, e2, jexpr_anh_one (muq_ne_zero q) (muq16_ne q)])⟩
  · exact ⟨Subtype.ext (by rw [h1, e1, jexpr_anh_two mu_ne_zero mu16_ne]),
      Subtype.ext (by rw [h2, e2, jexpr_anh_two (muq_ne_zero q) (muq16_ne q)])⟩

theorem ringHom_ext_gens {φ ψ : ↥(lambdaFieldOver q K) →+* LQ}
    (hc : ∀ x : ↥(lambdaFieldOver q K),
      (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → φ x = ψ x)
    (h1 : φ (μL q K) = ψ (μL q K)) (h2 : φ (μqL q K) = ψ (μqL q K)) : φ = ψ := by
  have key : lambdaFieldOver q K ≤ (RingHom.eqLocusField φ ψ).map (lambdaFieldOver q K).subtype := by
    show Subfield.closure _ ≤ _
    refine Subfield.closure_le.mpr ?_
    rintro x (⟨c, rfl⟩ | hx)
    · exact Subfield.mem_map.mpr ⟨⟨_, Subfield.subset_closure (Or.inl ⟨c, rfl⟩)⟩,
        RingHom.mem_eqLocusField.mpr (hc _ ⟨c, rfl⟩), rfl⟩
    · rcases hx with rfl | rfl
      · exact Subfield.mem_map.mpr ⟨μL q K, RingHom.mem_eqLocusField.mpr h1, rfl⟩
      · exact Subfield.mem_map.mpr ⟨μqL q K, RingHom.mem_eqLocusField.mpr h2, rfl⟩
  refine RingHom.ext fun x => ?_
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (key x.2)
  have : y = x := Subtype.ext hyx
  subst this
  exact RingHom.mem_eqLocusField.mp hy

theorem aut_ext {g h : RingAut ↥(lambdaFieldOver q K)} (hg : FixC q K g) (hh : FixC q K h) {i : Fin 6}
    (hgv : Val q K g i) (hhv : Val q K h i) : g = h := by
  have key := ringHom_ext_gens (q := q) (K := K)
    (φ := (lambdaFieldOver q K).subtype.comp g.toRingHom) (ψ := (lambdaFieldOver q K).subtype.comp h.toRingHom)
    (fun x hx => by
      show ((g x : ↥(lambdaFieldOver q K)) : LQ) = ((h x : ↥(lambdaFieldOver q K)) : LQ)
      rw [hg x hx, hh x hx])
    (by show ((g (μL q K) : ↥(lambdaFieldOver q K)) : LQ) = ((h (μL q K) : ↥(lambdaFieldOver q K)) : LQ)
        rw [hgv.1, hhv.1])
    (by show ((g (μqL q K) : ↥(lambdaFieldOver q K)) : LQ) = ((h (μqL q K) : ↥(lambdaFieldOver q K)) : LQ)
        rw [hgv.2, hhv.2])
  exact RingEquiv.ext fun x => Subtype.ext (RingHom.congr_fun key x)

theorem apply_eq_of_mem_map_fieldOver {g : RingAut ↥(lambdaFieldOver q K)} (hgc : FixC q K g)
    (hgJ : g (jexpr (μL q K)) = jexpr (μL q K)) (hgJq : g (jexpr (μqL q K)) = jexpr (μqL q K))
    (x : ↥(lambdaFieldOver q K)) (hx : (x : LQ) ∈ (fieldOver (1 * q) K).map (qExpand Qb 2)) : g x = x := by
  have hle : (fieldOver (1 * q) K).map (qExpand Qb 2) ≤
      (RingHom.eqLocusField g.toRingHom (RingHom.id _)).map (lambdaFieldOver q K).subtype := by
    rw [fieldOver, RingHom.map_field_closure]
    refine Subfield.closure_le.mpr ?_
    rintro _ ⟨y, hy, rfl⟩
    rcases hy with ⟨c, rfl⟩ | hy
    · have hc : qExpand Qb 2 (CharPReduction.constSeries K.toSubalgebra.toSubring c) =
          CharPReduction.constSeries K.toSubalgebra.toSubring c := qExpand_algebraMap 2 _
      rw [hc]
      exact Subfield.mem_map.mpr ⟨⟨_, Subfield.subset_closure (Or.inl ⟨c, rfl⟩)⟩,
        RingHom.mem_eqLocusField.mpr (hgc _ ⟨c, rfl⟩), rfl⟩
    · rcases hy with rfl | rfl
      · exact Subfield.mem_map.mpr ⟨jexpr (μL q K), RingHom.mem_eqLocusField.mpr hgJ, coe_jexpr_μL⟩
      · exact Subfield.mem_map.mpr ⟨jexpr (μqL q K), RingHom.mem_eqLocusField.mpr hgJq, coe_jexpr_μqL⟩
  obtain ⟨y, hy, hyx⟩ := Subfield.mem_map.mp (hle hx)
  have : y = x := Subtype.ext hyx
  subst this
  exact RingHom.mem_eqLocusField.mp hy

end Field

section Main

theorem mainEG (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (K : IntermediateField ℚ Qb) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥(lambdaFieldOver q K)),
      Fintype.card G = 6 ∧
      (∀ g : G, (∀ x : ↥(lambdaFieldOver q K), g • x = x) → g = 1) ∧
      (∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → g • x = x) ∧
      (∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) → g • x = x) ∧
      (∀ g : G,
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) ∧
      (∀ T Tq : LaurentSeries (AlgebraicClosure ℚ),
        ((T = lambdaModC (AlgebraicClosure ℚ) ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (T = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ Tq = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (T = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (T = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (T = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (T = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) →
        ∃ g : G, ((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = T ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = Tq) := by
  classical
  obtain ⟨σi, hσic, hσiμ, hσiμq⟩ := exists_ringEquiv_lambdaFieldOver_map_eq_inv q hq2 K
  obtain ⟨σs, hσsc, hσsμ, hσsμq⟩ := exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub q hq2 K

  have vs : Val q K σs 1 := ⟨hσsμ, hσsμq⟩
  have vi : Val q K σi 2 := ⟨hσiμ, hσiμq⟩
  have v1 : Val q K 1 0 := val_one q K
  have cs : FixC q K σs := hσsc
  have ci : FixC q K σi := hσic
  have c1 : FixC q K 1 := fixC_one q K

  have hss : σs * σs = 1 := aut_ext (fixC_mul cs cs) c1 (val_mul_one vs vs) v1
  have hii : σi * σi = 1 := aut_ext (fixC_mul ci ci) c1 (val_mul_two vi vi) v1
  have hsinv : σs⁻¹ = σs := inv_eq_of_mul_eq_one_right hss
  have hiinv : σi⁻¹ = σi := inv_eq_of_mul_eq_one_right hii

  have hJs := apply_jexpr_of_val vs (Or.inl rfl)
  have hJi := apply_jexpr_of_val vi (Or.inr rfl)

  let P : RingAut ↥(lambdaFieldOver q K) → Prop := fun g =>
    FixC q K g ∧ g (jexpr (μL q K)) = jexpr (μL q K) ∧ g (jexpr (μqL q K)) = jexpr (μqL q K) ∧ ∃ i, Val q K g i
  have hPs : ∀ y, P y → P (σs * y) := fun y ⟨hyc, hyJ, hyJq, b, hyv⟩ =>
    ⟨fixC_mul cs hyc, by show σs (y _) = _; rw [hyJ, hJs.1], by show σs (y _) = _; rw [hyJq, hJs.2],
      τs b, val_mul_one vs hyv⟩
  have hPi : ∀ y, P y → P (σi * y) := fun y ⟨hyc, hyJ, hyJq, b, hyv⟩ =>
    ⟨fixC_mul ci hyc, by show σi (y _) = _; rw [hyJ, hJi.1], by show σi (y _) = _; rw [hyJq, hJi.2],
      τi b, val_mul_two vi hyv⟩

  let S : Set (RingAut ↥(lambdaFieldOver q K)) := {σs, σi}
  let H : Subgroup (RingAut ↥(lambdaFieldOver q K)) := Subgroup.closure S
  have hP : ∀ g ∈ H, P g := by
    intro g hg
    refine Subgroup.closure_induction_left (p := fun g _ => P g) ?_ ?_ ?_ hg
    · exact ⟨c1, rfl, rfl, 0, v1⟩
    · rintro x hx y - hy
      rcases hx with hx | hx
      · rw [hx]; exact hPs y hy
      · rw [Set.mem_singleton_iff.mp hx]; exact hPi y hy
    · rintro x hx y - hy
      rcases hx with hx | hx
      · rw [hx, hsinv]; exact hPs y hy
      · rw [Set.mem_singleton_iff.mp hx, hiinv]; exact hPi y hy
  have ms : σs ∈ H := Subgroup.subset_closure (Set.mem_insert _ _)
  have mi : σi ∈ H := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  let gs : ↥H := ⟨σs, ms⟩
  let gi : ↥H := ⟨σi, mi⟩

  have vw3 : Val q K (σs * σi) 3 := val_mul_one vs vi
  have vw5 : Val q K (σi * σs) 5 := val_mul_two vi vs
  have vw4 : Val q K (σi * (σs * σi)) 4 := val_mul_two vi vw3
  let w : Fin 6 → ↥H := ![1, gs, gi, gs * gi, gi * (gs * gi), gi * gs]
  have hsurj : Function.Surjective w := by
    intro g
    obtain ⟨hgc, -, -, i, hgv⟩ := hP g.1 g.2
    fin_cases i
    · exact ⟨0, Subtype.ext (aut_ext c1 hgc v1 hgv)⟩
    · exact ⟨1, Subtype.ext (aut_ext cs hgc vs hgv)⟩
    · exact ⟨2, Subtype.ext (aut_ext ci hgc vi hgv)⟩
    · exact ⟨3, Subtype.ext (aut_ext (fixC_mul cs ci) hgc vw3 hgv)⟩
    · exact ⟨4, Subtype.ext (aut_ext (fixC_mul ci (fixC_mul cs ci)) hgc vw4 hgv)⟩
    · exact ⟨5, Subtype.ext (aut_ext (fixC_mul ci cs) hgc vw5 hgv)⟩
  letI : Fintype ↥H := Fintype.ofSurjective w hsurj

  have hle : Fintype.card ↥H ≤ 6 :=
    (Fintype.card_le_of_surjective w hsurj).trans_eq (Fintype.card_fin 6)
  have hord2 : orderOf gs = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one, pow_two]; exact hss)
    · intro h
      have h' : σs = 1 := congrArg Subtype.val h
      apply anh_one_mu_ne
      rw [← vs.1, h']
      rfl
  have vr2 : Val q K (σs * (σi * (σs * σi))) 5 := val_mul_one vs vw4
  have vr3 : Val q K (σs * (σi * (σs * (σi * (σs * σi))))) 0 := val_mul_one vs (val_mul_two vi vr2)
  have hord3 : orderOf (gs * gi) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · refine Subtype.ext ?_
      rw [Subgroup.coe_pow, Subgroup.coe_one, Subgroup.coe_mul, pow_three]
      simp only [mul_assoc]
      exact aut_ext (fixC_mul cs (fixC_mul ci (fixC_mul cs (fixC_mul ci (fixC_mul cs ci))))) c1 vr3 v1
    · intro h
      have h' : σs * σi = 1 := congrArg Subtype.val h
      apply anh_three_mu_ne
      rw [← vw3.1, h']
      rfl
  have hcard : Fintype.card ↥H = 6 := by
    have h2 : 2 ∣ Fintype.card ↥H := hord2 ▸ orderOf_dvd_card
    have h3 : 3 ∣ Fintype.card ↥H := hord3 ▸ orderOf_dvd_card
    have h6 : 6 ∣ Fintype.card ↥H := Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num) h2 h3
    have := Nat.le_of_dvd Fintype.card_pos h6
    omega
  refine ⟨↥H, inferInstance, inferInstance, inferInstance, hcard, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro g hg
    exact Subtype.ext (RingEquiv.ext fun x => hg x)
  ·
    intro g x hx
    exact (hP g.1 g.2).1 x hx
  ·
    intro g x hx
    obtain ⟨hgc, hgJ, hgJq, -⟩ := hP g.1 g.2
    exact apply_eq_of_mem_map_fieldOver hgc hgJ hgJq x hx
  ·
    intro g
    obtain ⟨-, -, -, i, hv⟩ := hP g.1 g.2
    fin_cases i
    · exact Or.inl hv
    · exact Or.inr (Or.inl hv)
    · exact Or.inr (Or.inr (Or.inl hv))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hv)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hv))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hv))))
  ·
    rintro T Tq (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨1, v1⟩
    · exact ⟨gs, vs⟩
    · exact ⟨gi, vi⟩
    · exact ⟨gs * gi, vw3⟩
    · exact ⟨gi * (gs * gi), vw4⟩
    · exact ⟨gi * gs, vw5⟩

end Main

end Ws30EG
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve.Ws30EG"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve.Ws30EG P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve"

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve ModularCurve.Ws30EG in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G) (_ : MulSemiringAction G ↥(lambdaFieldOver q K)),
      Fintype.card G = 6 ∧
      (∀ g : G, (∀ x : ↥(lambdaFieldOver q K), g • x = x) → g = 1) ∧
      (∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → g • x = x) ∧
      (∀ (g : G) (x : ↥(lambdaFieldOver q K)), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) → g • x = x) ∧
      (∀ g : G,
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨
        (((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) ∧
      (∀ T Tq : LaurentSeries (AlgebraicClosure ℚ),
        ((T = lambdaModC (AlgebraicClosure ℚ) ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q) ∨ (T = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧ Tq = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (T = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨ (T = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (T = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧ Tq = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹) ∨ (T = (16 * lambdaModC (AlgebraicClosure ℚ) - 1) * (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧ Tq = (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1) * (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹)) →
        ∃ g : G, ((g • (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = T ∧
          ((g • (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = Tq) :=
  mainEG q hq2 K

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve.Ws30EG P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver.ModularCurve"

end S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_anharmonic_mulSemiringAction_lambdaFieldOver (solution)
