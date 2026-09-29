-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/bc19a473-ef62-53a4-81bb-30f5de2fb6bc

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Theorems.Thm_ModularCurve_qExpand_two_jq_mul_lambdaModC_sq
import Theorems.Thm_ValuationSubring_map_eq_zero_of_valuation_lt_one_of_charP
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem
p2m_attr_erase "instance" "ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation"
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy"
p2m_attr_erase "simp" "ModularCurve.ProjectiveLine.map_mk ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring"
p2m_attr_erase "simp" "AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen"
p2m_attr_erase "simp" "ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ"
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized"

namespace ModularCurve p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap qExpand_two_jq_mul_lambdaModC_sq LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv" namespace D3Proof end ModularCurve.D3Proof
p2m_open_scoped "ModularCurve" in

theorem ModularCurve.D3Proof.level_two_values_cases
    {k : Type*} [Field k] {q : ℕ} [Fact q.Prime] [CharP k q] (hq : 5 ≤ q)
    (a : k) (h01728 : a = 0 ∨ a = 1728) (l₁ l₂ : k)
    (h₁ : a * ((16 * l₁) ^ 2 * (16 * l₁ - 1) ^ 2) = 256 * ((16 * l₁) ^ 2 - 16 * l₁ + 1) ^ 3)
    (h₂ : a * ((16 * l₂) ^ 2 * (16 * l₂ - 1) ^ 2) = 256 * ((16 * l₂) ^ 2 - 16 * l₂ + 1) ^ 3) :
    l₁ = l₂ ∨ 16 * (l₁ + l₂) = 1 ∨ 256 * l₁ * l₂ = 1 ∨ l₂ * (16 * l₁ - 1) = l₁ := by
  have hp : q.Prime := Fact.out
  have h2 : (2 : k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hpow2 : ∀ n : ℕ, ((2 : k) ^ n) ≠ 0 := fun n => pow_ne_zero _ h2
  have h16 : (16 : k) ≠ 0 := by have := hpow2 4; norm_num at this; exact this
  have h32 : (32 : k) ≠ 0 := by have := hpow2 5; norm_num at this; exact this
  have h64 : (64 : k) ≠ 0 := by have := hpow2 6; norm_num at this; exact this
  have h256 : (256 : k) ≠ 0 := by have := hpow2 8; norm_num at this; exact this
  rcases h01728 with rfl | rfl
  ·
    have e₁ : 256 * l₁ ^ 2 - 16 * l₁ + 1 = 0 := by
      rw [zero_mul] at h₁
      have := (mul_eq_zero.mp h₁.symm).resolve_left h256
      have := pow_eq_zero_iff (by norm_num) |>.mp this
      linear_combination this
    have e₂ : 256 * l₂ ^ 2 - 16 * l₂ + 1 = 0 := by
      rw [zero_mul] at h₂
      have := (mul_eq_zero.mp h₂.symm).resolve_left h256
      have := pow_eq_zero_iff (by norm_num) |>.mp this
      linear_combination this
    have : (l₁ - l₂) * (16 * (16 * (l₁ + l₂) - 1)) = 0 := by linear_combination e₁ - e₂
    rcases mul_eq_zero.mp this with h | h
    · left; linear_combination h
    · right; left
      have := (mul_eq_zero.mp h).resolve_left h16
      linear_combination this
  ·
    have fac : ∀ l : k, 1728 * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3 →
        16 * l + 1 = 0 ∨ 16 * l - 2 = 0 ∨ 32 * l - 1 = 0 := by
      intro l hl
      have hfac : (64 : k) * ((16 * l + 1) ^ 2 * (16 * l - 2) ^ 2 * (32 * l - 1) ^ 2) = 0 := by
        linear_combination (-1 : k) * hl
      have hprod := (mul_eq_zero.mp hfac).resolve_left h64
      rcases mul_eq_zero.mp hprod with h | h
      · rcases mul_eq_zero.mp h with h | h
        · left; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
        · right; left; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
      · right; right; exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h
    have i16 : (16 : k)⁻¹ * 16 = 1 := inv_mul_cancel₀ h16
    have i32 : (32 : k)⁻¹ * 32 = 1 := inv_mul_cancel₀ h32
    rcases fac l₁ h₁ with a₁ | a₁ | a₁ <;> rcases fac l₂ h₂ with a₂ | a₂ | a₂
    · left; linear_combination (16 : k)⁻¹ * a₁ - (16 : k)⁻¹ * a₂ - (l₁ - l₂) * i16
    · right; left; linear_combination a₁ + a₂
    · right; right; right
      linear_combination (l₂ - (16 : k)⁻¹) * a₁ - (16 : k)⁻¹ * a₂ + (2 * l₂ + l₁) * i16
    · right; left; linear_combination a₁ + a₂
    · left; linear_combination (16 : k)⁻¹ * a₁ - (16 : k)⁻¹ * a₂ - (l₁ - l₂) * i16
    · right; right; left; linear_combination (16 * l₂) * a₁ + a₂
    · right; right; right
      linear_combination (l₁ - (16 : k)⁻¹) * a₂ - (16 : k)⁻¹ * a₁ + (2 * l₁ + l₂) * i16
    · right; right; left; linear_combination (16 * l₁) * a₂ + a₁
    · left; linear_combination (32 : k)⁻¹ * a₁ - (32 : k)⁻¹ * a₂ - (l₁ - l₂) * i32

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap qExpand_two_jq_mul_lambdaModC_sq LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv"
p2m_open "ModularCurve"
namespace D3Proof

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

scoped instance instCharZeroLQ : CharZero (LaurentSeries (AlgebraicClosure ℚ)) :=
  charZero_of_injective_algebraMap (algebraMap (AlgebraicClosure ℚ) (LaurentSeries (AlgebraicClosure ℚ))).injective

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

theorem jLambda_Qb_q (q : ℕ) [NeZero q] :
    qExpand Qb 2 (jqNModC Qb (1 * q)) * lambdaNModC Qb q ^ 2 * (16 * lambdaNModC Qb q - 1) ^ 2
      = (256 * lambdaNModC Qb q ^ 2 - 16 * lambdaNModC Qb q + 1) ^ 3 := by
  have h := congrArg (qExpand Qb q) (jLambda_Qb)
  have hj : qExpand Qb q (qExpand Qb 2 (jqModC Qb)) = qExpand Qb 2 (jqNModC Qb (1 * q)) := by
    rw [jqNModC, qExpand_qExpand, qExpand_qExpand]
    exact qExpand_congr (by ring) _
  simpa only [map_mul, map_pow, map_sub, map_add, map_one, map_ofNat, hj, lambdaNModC] using h

def Rj {F : Type*} [Field F] (m : F) : F := (256 * m ^ 2 - 16 * m + 1) ^ 3 / (m ^ 2 * (16 * m - 1) ^ 2)

theorem map_Rj {F F' : Type*} [Field F] [Field F'] {G : Type*} [FunLike G F F'] [RingHomClass G F F']
    (f : G) (m : F) : f (Rj m) = Rj (f m) := by
  simp only [Rj, map_div₀, map_pow, map_sub, map_add, map_mul, map_one, map_ofNat]

theorem ne_zero_of_jRel {F : Type*} [Field F] [CharZero F] (J m : F)
    (hJ : J * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) : m ≠ 0 ∧ 16 * m - 1 ≠ 0 := by
  constructor
  · intro h0; rw [h0] at hJ; norm_num at hJ
  · intro h0
    have h1 : (256 * m ^ 2 - 16 * m + 1) = 1 := by linear_combination (16 * m) * h0
    rw [h0, h1] at hJ; norm_num at hJ

theorem eq_Rj_of_jRel {F : Type*} [Field F] [CharZero F] (J m : F)
    (hJ : J * m ^ 2 * (16 * m - 1) ^ 2 = (256 * m ^ 2 - 16 * m + 1) ^ 3) : J = Rj m := by
  obtain ⟨h0, h16⟩ := ne_zero_of_jRel J m hJ
  have hD : m ^ 2 * (16 * m - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h16)
  rw [Rj, eq_div_iff hD, ← hJ]; ring

theorem Rj_sixteenth_sub {F : Type*} [Field F] (m : F) (h0 : m ≠ 0) (h16 : 16 * m - 1 ≠ 0) (h16' : (16 : F) ≠ 0) :
    Rj (16⁻¹ - m) = Rj m := by
  have h1 : (16⁻¹ - m) ^ 2 * (16 * (16⁻¹ - m) - 1) ^ 2 = m ^ 2 * (16 * m - 1) ^ 2 := by
    field_simp; ring
  have h2 : (256 * (16⁻¹ - m) ^ 2 - 16 * (16⁻¹ - m) + 1) = 256 * m ^ 2 - 16 * m + 1 := by
    field_simp; ring
  rw [Rj, Rj, h1, h2]

theorem Rj_inv {F : Type*} [Field F] (m : F) (h0 : m ≠ 0) (h16 : 16 * m - 1 ≠ 0) (h16' : (16 : F) ≠ 0)
    (h256 : (256 : F) ≠ 0) : Rj ((256 * m)⁻¹) = Rj m := by
  have hD : m ^ 2 * (16 * m - 1) ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ h0) (pow_ne_zero _ h16)
  have h256m : 256 * m ≠ 0 := mul_ne_zero h256 h0
  have hnum : 16 * (256 * m)⁻¹ - 1 ≠ 0 := by
    have : 16 * (256 * m)⁻¹ - 1 = -(16 * (16 * m - 1)) * (256 * m)⁻¹ := by field_simp; ring
    rw [this]
    exact mul_ne_zero (neg_ne_zero.mpr (mul_ne_zero h16' h16)) (inv_ne_zero h256m)
  have hD' : ((256 * m)⁻¹) ^ 2 * (16 * (256 * m)⁻¹ - 1) ^ 2 ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (inv_ne_zero h256m)) (pow_ne_zero _ hnum)
  rw [Rj, Rj, div_eq_div_iff hD' hD]
  field_simp
  ring

section Ctx
variable (q : ℕ) [Fact q.Prime] (K : IntermediateField ℚ Qb)

abbrev Λ : Subfield LQ := lambdaFieldOver q K

def fixedSubfield (σ : ↥(Λ q K) ≃+* ↥(Λ q K)) : Subfield ↥(Λ q K) where
  carrier := {x | σ x = x}
  zero_mem' := by show σ 0 = 0; exact map_zero σ
  one_mem' := by show σ 1 = 1; exact map_one σ
  add_mem' := by
    intro a b ha hb
    show σ (a + b) = a + b
    rw [map_add, show σ a = a from ha, show σ b = b from hb]
  neg_mem' := by
    intro a ha
    show σ (-a) = -a
    rw [map_neg, show σ a = a from ha]
  mul_mem' := by
    intro a b ha hb
    show σ (a * b) = a * b
    rw [map_mul, show σ a = a from ha, show σ b = b from hb]
  inv_mem' := by
    intro a ha
    show σ a⁻¹ = a⁻¹
    rw [map_inv₀, show σ a = a from ha]

theorem mem_fixedSubfield (σ : ↥(Λ q K) ≃+* ↥(Λ q K)) (x : ↥(Λ q K)) : x ∈ fixedSubfield q K σ ↔ σ x = x :=
  Iff.rfl

theorem jq2_mem : qExpand Qb 2 (jqModC Qb) ∈ Λ q K := by
  rw [eq_Rj_of_jRel _ _ jLambda_Qb]
  have h := map_Rj (Λ q K).subtype (⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K))
  exact h ▸ SetLike.coe_mem _

theorem jqN2_mem : qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ Λ q K := by
  rw [eq_Rj_of_jRel _ _ (jLambda_Qb_q q)]
  have h := map_Rj (Λ q K).subtype (⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K))
  exact h ▸ SetLike.coe_mem _

theorem fixes_map_fieldOver (σ : ↥(Λ q K) ≃+* ↥(Λ q K))
    (hc : ∀ x : ↥(Λ q K), (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hμ : Rj (σ ⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩) =
      Rj (⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K)))
    (hμq : Rj (σ ⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩) =
      Rj (⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K))) :
    ∀ x : ↥(Λ q K), (x : LQ) ∈ (fieldOver (1 * q) K).map (qExpand Qb 2) → σ x = x := by
  intro x hx
  obtain ⟨z, hz, hzx⟩ := Subfield.mem_map.mp hx
  have hT : fieldOver (1 * q) K ≤ ((fixedSubfield q K σ).map (Λ q K).subtype).comap (qExpand Qb 2) := by
    unfold fieldOver
    rw [Subfield.closure_le]
    rintro w (⟨c, rfl⟩ | rfl | rfl)
    · show qExpand Qb 2 (CharPReduction.constSeries _ c) ∈ (fixedSubfield q K σ).map (Λ q K).subtype
      have hmem : CharPReduction.constSeries K.toSubalgebra.toSubring c ∈ Λ q K :=
        Subfield.subset_closure (Or.inl ⟨c, rfl⟩)
      have hfix := hc ⟨_, hmem⟩ ⟨c, rfl⟩
      rw [CharPReduction.constSeries, RingHom.comp_apply, qExpand_algebraMap]
      exact ⟨⟨_, hmem⟩, hfix, rfl⟩
    · show qExpand Qb 2 (jqModC Qb) ∈ (fixedSubfield q K σ).map (Λ q K).subtype
      refine ⟨⟨_, jq2_mem q K⟩, ?_, rfl⟩
      show σ _ = _
      have hj : (⟨qExpand Qb 2 (jqModC Qb), jq2_mem q K⟩ : ↥(Λ q K))
          = Rj ⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ := by
        apply Subtype.ext
        show qExpand Qb 2 (jqModC Qb) = _
        rw [eq_Rj_of_jRel _ _ jLambda_Qb]
        exact (map_Rj (Λ q K).subtype (⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K))).symm
      rw [hj, map_Rj σ, hμ]
    · show qExpand Qb 2 (jqNModC Qb (1 * q)) ∈ (fixedSubfield q K σ).map (Λ q K).subtype
      refine ⟨⟨_, jqN2_mem q K⟩, ?_, rfl⟩
      show σ _ = _
      have hj : (⟨qExpand Qb 2 (jqNModC Qb (1 * q)), jqN2_mem q K⟩ : ↥(Λ q K))
          = Rj ⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ := by
        apply Subtype.ext
        show qExpand Qb 2 (jqNModC Qb (1 * q)) = _
        rw [eq_Rj_of_jRel _ _ (jLambda_Qb_q q)]
        exact (map_Rj (Λ q K).subtype (⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(Λ q K))).symm
      rw [hj, map_Rj σ, hμq]
  obtain ⟨w, hw, hwz⟩ := Subfield.mem_map.mp (Subfield.mem_comap.mp (hT hz))
  have : w = x := Subtype.ext (hwz.trans hzx)
  rw [← this]; exact hw

end Ctx

section Core
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]
  (red : A →+* k) (K : IntermediateField ℚ Qb)

theorem transport_core (σ : ↥(Λ q K) ≃+* ↥(Λ q K))
    (hc : ∀ x : ↥(Λ q K), (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (y₂ : ↥(coeffSubring A K))
    (B : Subring LQ) (hBL : B ≤ (Λ q K).toSubring)
    (hTB : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B)
    (hσB : ∀ (b : LQ) (hb : b ∈ B), ((σ ⟨b, hBL hb⟩ : ↥(Λ q K)) : LQ) ∈ B)
    (I : Ideal ↥B)
    (hIc : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 →
      (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C c), hTB _⟩ : ↥B) ∈ I)
    (hμ : (⟨((σ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), hBL (hTB _)⟩ : ↥(Λ q K)) : LQ), hσB _ (hTB _)⟩
        - ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C y₂), hTB _⟩ : ↥B) ∈ I)
    (hμq : (⟨((σ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), hBL (hTB _)⟩ : ↥(Λ q K)) : LQ), hσB _ (hTB _)⟩
        - ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C (y₂ ^ q)), hTB _⟩ : ↥B) ∈ I) :
    ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
      pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y₂) (redRestrict red K y₂ ^ q) p = 0 →
        (⟨((σ ⟨lambdaEval q (coeffSubring A K) p, hBL (hTB p)⟩ : ↥(Λ q K)) : LQ), hσB _ (hTB p)⟩ : ↥B) ∈ I := by
  classical
  intro p hp
  let evB : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥B := (lambdaEval q (coeffSubring A K)).codRestrict B hTB
  let σB : ↥B →+* ↥B :=
    { toFun := fun b => ⟨((σ ⟨b, hBL b.2⟩ : ↥(Λ q K)) : LQ), hσB b b.2⟩
      map_one' := by
        apply Subtype.ext
        show ((σ ⟨((1 : ↥B) : LQ), _⟩ : ↥(Λ q K)) : LQ) = 1
        rw [show (⟨((1 : ↥B) : LQ), hBL (1 : ↥B).2⟩ : ↥(Λ q K)) = 1 from rfl, map_one]; rfl
      map_mul' := fun b b' => by
        apply Subtype.ext
        show ((σ ⟨((b * b' : ↥B) : LQ), _⟩ : ↥(Λ q K)) : LQ) = ((σ ⟨(b : LQ), _⟩ : ↥(Λ q K)) : LQ) * ((σ ⟨(b' : LQ), _⟩ : ↥(Λ q K)) : LQ)
        rw [show (⟨((b * b' : ↥B) : LQ), hBL (b * b').2⟩ : ↥(Λ q K)) = ⟨(b : LQ), hBL b.2⟩ * ⟨(b' : LQ), hBL b'.2⟩ from rfl,
          map_mul]; rfl
      map_zero' := by
        apply Subtype.ext
        show ((σ ⟨((0 : ↥B) : LQ), _⟩ : ↥(Λ q K)) : LQ) = 0
        rw [show (⟨((0 : ↥B) : LQ), hBL (0 : ↥B).2⟩ : ↥(Λ q K)) = 0 from rfl, map_zero]; rfl
      map_add' := fun b b' => by
        apply Subtype.ext
        show ((σ ⟨((b + b' : ↥B) : LQ), _⟩ : ↥(Λ q K)) : LQ) = ((σ ⟨(b : LQ), _⟩ : ↥(Λ q K)) : LQ) + ((σ ⟨(b' : LQ), _⟩ : ↥(Λ q K)) : LQ)
        rw [show (⟨((b + b' : ↥B) : LQ), hBL (b + b').2⟩ : ↥(Λ q K)) = ⟨(b : LQ), hBL b.2⟩ + ⟨(b' : LQ), hBL b'.2⟩ from rfl,
          map_add]; rfl }
  let Θ : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥B ⧸ I := (Ideal.Quotient.mk I).comp (σB.comp evB)
  let g : ↥(coeffSubring A K) →+* ↥B ⧸ I := (Ideal.Quotient.mk I).comp (evB.comp MvPolynomial.C)
  let w : Fin 2 → ↥(coeffSubring A K) := ![y₂, y₂ ^ q]

  have hσconst : ∀ c : ↥(coeffSubring A K), σB (evB (MvPolynomial.C c)) = evB (MvPolynomial.C c) := by
    intro c
    apply Subtype.ext
    show ((σ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C c), _⟩ : ↥(Λ q K)) : LQ) = lambdaEval q (coeffSubring A K) (MvPolynomial.C c)
    have hval : lambdaEval q (coeffSubring A K) (MvPolynomial.C c) = CharPReduction.constSeries K.toSubalgebra.toSubring ⟨c, c.2.2⟩ := by
      rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl
    have := hc ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C c), hBL (hTB _)⟩ ⟨⟨c, c.2.2⟩, hval.symm⟩
    exact congrArg Subtype.val this
  have hΘ : Θ = MvPolynomial.eval₂Hom g (g ∘ w) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      show Ideal.Quotient.mk I (σB (evB (MvPolynomial.C c))) = _
      rw [MvPolynomial.eval₂Hom_C, hσconst]; rfl
    · intro i
      rw [MvPolynomial.eval₂Hom_X']
      show Ideal.Quotient.mk I (σB (evB (MvPolynomial.X i))) = Ideal.Quotient.mk I (evB (MvPolynomial.C (w i)))
      rw [Ideal.Quotient.eq]
      fin_cases i
      · exact hμ
      · exact hμq
  have hΘp : Θ p = g (MvPolynomial.eval w p) := by
    have h := MvPolynomial.eval₂_comp_left g (RingHom.id _) w p
    rw [RingHom.comp_id] at h
    rw [hΘ, MvPolynomial.coe_eval₂Hom, ← h]
    rfl

  have hc0 : redRestrict red K (MvPolynomial.eval w p) = 0 := by
    have h := MvPolynomial.eval₂_comp_left (redRestrict red K) (RingHom.id _) w p
    rw [RingHom.comp_id] at h
    have hw : (redRestrict red K) ∘ w = ![redRestrict red K y₂, redRestrict red K y₂ ^ q] := by
      ext i; fin_cases i
      · rfl
      · show redRestrict red K (y₂ ^ q) = redRestrict red K y₂ ^ q; rw [map_pow]
    rw [hw] at h
    show redRestrict red K (MvPolynomial.eval₂ (RingHom.id _) w p) = 0
    rw [h]
    exact hp
  have hzero : Θ p = 0 := by
    rw [hΘp]
    show Ideal.Quotient.mk I (evB (MvPolynomial.C (MvPolynomial.eval w p))) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hIc _ hc0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp hzero

end Core

end D3Proof
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

noncomputable section

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries algebraMap_laurentSeries_eq_single jqModC jqNModC jqModC_rat map_jqModC qExpand qExpand_single qExpand_congr qExpand_qExpand jq lambdaInt lambdaModC lambdaNModC laurentMap laurentMap_qExpand laurentMap_laurentMap qExpand_two_jq_mul_lambdaModC_sq LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv"
p2m_open "ModularCurve"
namespace D3Proof

local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)
local notation "Qb" => AlgebraicClosure ℚ

section Red
variable {A : ValuationSubring Qb} {k : Type*} [Field k]

theorem mem_coeffSubring_iff' (K : IntermediateField ℚ Qb) {x : Qb} : x ∈ coeffSubring A K ↔ x ∈ A ∧ x ∈ K := Iff.rfl

theorem red_eq_zero_of_mem_maximalIdeal (red : A →+* k) (q : ℕ) [Fact q.Prime] [CharP k q] (τ : A) (hτ : τ ∈ IsLocalRing.maximalIdeal A) : red τ = 0 := by
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

theorem isUnit_coeffSubring_iff (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (c : ↥(coeffSubring A K)) : IsUnit c ↔ redRestrict red K c ≠ 0 := by
  constructor
  · rintro ⟨u, rfl⟩ hc
    have h1 : redRestrict red K ((u * u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) = 1 := by
      rw [mul_inv_cancel, Units.val_one, map_one]
    rw [Units.val_mul, map_mul, hc, zero_mul] at h1
    exact zero_ne_one h1
  · intro hc
    have hcA : (c : Qb) ∈ A := ((mem_coeffSubring_iff' (A := A) K).mp c.2).1
    have hcK : (c : Qb) ∈ K := ((mem_coeffSubring_iff' (A := A) K).mp c.2).2
    have hcm : (⟨(c : Qb), hcA⟩ : A) ∉ IsLocalRing.maximalIdeal A := fun hm =>
      hc (red_eq_zero_of_mem_maximalIdeal red q _ hm)
    have hu : IsUnit (⟨(c : Qb), hcA⟩ : A) := by
      by_contra h; exact hcm ((IsLocalRing.mem_maximalIdeal _).mpr h)
    obtain ⟨u, hu⟩ := hu
    have hmul : (((u⁻¹ : Aˣ) : A) : Qb) * (c : Qb) = 1 := by
      have h := congrArg (fun z : A => (z : Qb)) u.inv_mul
      rw [hu] at h
      simpa using h
    have hinv : (c : Qb)⁻¹ = (((u⁻¹ : Aˣ) : A) : Qb) := inv_eq_of_mul_eq_one_left hmul
    have hinvmem : (c : Qb)⁻¹ ∈ coeffSubring A K :=
      (mem_coeffSubring_iff' (A := A) K).mpr ⟨hinv ▸ ((u⁻¹ : Aˣ) : A).2, K.inv_mem hcK⟩
    have hc0 : (c : Qb) ≠ 0 := by
      rintro h0
      apply hc
      have : c = 0 := Subtype.ext h0
      rw [this, map_zero]
    exact isUnit_iff_exists_inv.mpr ⟨⟨_, hinvmem⟩, Subtype.ext (mul_inv_cancel₀ hc0)⟩

theorem inv_two_pow_mem (red : A →+* k) (K : IntermediateField ℚ Qb) (q : ℕ) [Fact q.Prime] [CharP k q]
    (hq : 5 ≤ q) (n : ℕ) : ((2 : Qb) ^ n)⁻¹ ∈ coeffSubring A K := by
  have h : IsUnit (((2 ^ n : ℕ) : ↥(coeffSubring A K))) := by
    rw [isUnit_coeffSubring_iff red K q, map_natCast, Ne, CharP.cast_eq_zero_iff k q]
    intro hdvd
    have h2 : q ∣ 2 := (Fact.out : q.Prime).dvd_of_dvd_pow hdvd
    have := Nat.le_of_dvd (by norm_num) h2
    omega
  obtain ⟨u, hu⟩ := h
  have hmul : (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) * (2 : Qb) ^ n = 1 := by
    have h1 := congrArg (fun z : ↥(coeffSubring A K) => (z : Qb)) u.inv_mul
    rw [hu] at h1
    first | simpa using h1 | (push_cast at h1 ⊢; exact h1) | exact_mod_cast h1
  have : ((2 : Qb) ^ n)⁻¹ = (((u⁻¹ : (↥(coeffSubring A K))ˣ) : ↥(coeffSubring A K)) : Qb) :=
    (eq_inv_of_mul_eq_one_left hmul).symm
  rw [this]; exact SetLike.coe_mem _

end Red
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

section Main
variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring Qb} {k : Type*} [Field k] [CharP k q]

theorem lambdaEval_X0 (K : IntermediateField ℚ Qb) :
    lambdaEval q (coeffSubring A K) (MvPolynomial.X 0) = lambdaModC Qb := by
  rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl

theorem lambdaEval_X1 (K : IntermediateField ℚ Qb) :
    lambdaEval q (coeffSubring A K) (MvPolynomial.X 1) = lambdaNModC Qb q := by
  rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]; rfl

theorem lambdaEval_C (K : IntermediateField ℚ Qb) (c : ↥(coeffSubring A K)) :
    lambdaEval q (coeffSubring A K) (MvPolynomial.C c) = algebraMap Qb LQ (c : Qb) := by
  rw [lambdaEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; rfl

theorem key_identity (m Y : LQ) (h : 16 * m - 1 ≠ 0) :
    m / (16 * m - 1) - Y = (16 * (m / (16 * m - 1)) - 1) * (Y + (1 - 16 * Y) * m) := by
  rw [div_eq_mul_inv]
  have hD : (16 * m - 1) * (16 * m - 1)⁻¹ = 1 := mul_inv_cancel₀ h
  linear_combination (-m * (1 - 16 * Y)) * hD

theorem frob_rel (l₁ l₂ : k) :
    (l₁ = l₂ → l₁ ^ q = l₂ ^ q) ∧
    (16 * (l₁ + l₂) = 1 → 16 * (l₁ ^ q + l₂ ^ q) = 1) ∧
    (256 * l₁ * l₂ = 1 → 256 * l₁ ^ q * l₂ ^ q = 1) ∧
    (l₂ * (16 * l₁ - 1) = l₁ → l₂ ^ q * (16 * l₁ ^ q - 1) = l₁ ^ q) := by
  refine ⟨fun h => by rw [h], fun h => ?_, fun h => ?_, fun h => ?_⟩
  · have := congrArg (frobenius k q) h
    simpa only [map_mul, map_add, map_ofNat, map_one, frobenius_def] using this
  · have := congrArg (frobenius k q) h
    simpa only [map_mul, map_ofNat, map_one, frobenius_def] using this
  · have := congrArg (frobenius k q) h
    simpa only [map_mul, map_sub, map_ofNat, map_one, frobenius_def] using this

theorem _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (y₁ y₂ : ↥(coeffSubring A K))
    (hy₁ : a * ((16 * redRestrict red K y₁) ^ 2 * (16 * redRestrict red K y₁ - 1) ^ 2)
      = 256 * ((16 * redRestrict red K y₁) ^ 2 - 16 * redRestrict red K y₁ + 1) ^ 3)
    (hy₂ : a * ((16 * redRestrict red K y₂) ^ 2 * (16 * redRestrict red K y₂ - 1) ^ 2)
      = 256 * ((16 * redRestrict red K y₂) ^ 2 - 16 * redRestrict red K y₂ + 1) ^ 3) :
    ∃ σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K),
      (∀ x : ↥(lambdaFieldOver q K),
        (x : LaurentSeries (AlgebraicClosure ℚ)) ∈ (fieldOver (1 * q) K).map (qExpand (AlgebraicClosure ℚ) 2) →
          σ x = x) ∧
      ∀ (B : Subring (LaurentSeries (AlgebraicClosure ℚ))) (hBL : B ≤ (lambdaFieldOver q K).toSubring)
        (hTB : ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K), lambdaEval q (coeffSubring A K) p ∈ B)
        (hσB : ∀ (b : LaurentSeries (AlgebraicClosure ℚ)) (hb : b ∈ B),
          ((σ ⟨b, hBL hb⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ B)
        (I : Ideal ↥B),
        (∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y₁) (redRestrict red K y₁ ^ q) p = 0 →
            (⟨lambdaEval q (coeffSubring A K) p, hTB p⟩ : ↥B) ∈ I) →
        ∀ p : MvPolynomial (Fin 2) ↥(coeffSubring A K),
          pointEval (coeffSubring A K) (redRestrict red K) (redRestrict red K y₂) (redRestrict red K y₂ ^ q) p = 0 →
            (⟨((σ ⟨lambdaEval q (coeffSubring A K) p, hBL (hTB p)⟩ : ↥(lambdaFieldOver q K)) :
                LaurentSeries (AlgebraicClosure ℚ)), hσB _ (hTB p)⟩ : ↥B) ∈ I := by
  classical
  have hp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega

  have hk2 : (2 : k) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : k) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff k q] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hk16 : (16 : k) ≠ 0 := by
    have : (16 : k) = 2 ^ 4 := by norm_num
    rw [this]; exact pow_ne_zero _ hk2
  have h16mem : (16 : Qb)⁻¹ ∈ coeffSubring A K := by
    have := inv_two_pow_mem red K q hq 4; norm_num at this; rwa [one_div] at this
  let c16 : ↥(coeffSubring A K) := ⟨(16 : Qb)⁻¹, h16mem⟩
  have hc16 : redRestrict red K c16 = 16⁻¹ := by
    have h1 : c16 * 16 = 1 := Subtype.ext (by push_cast; exact inv_mul_cancel₀ (by norm_num))
    have h2 := congrArg (redRestrict red K) h1
    rw [map_mul, map_ofNat, map_one] at h2
    exact (eq_inv_of_mul_eq_one_left h2)
  have hn256 : ((256 : ↥(coeffSubring A K)) : Qb) = 256 := by norm_cast
  have hn16 : ((16 : ↥(coeffSubring A K)) : Qb) = 16 := by norm_cast
  have hn1 : ((1 : ↥(coeffSubring A K)) : Qb) = 1 := by norm_cast
  have hc16Q : algebraMap Qb LQ (c16 : Qb) = 16⁻¹ := by
    show algebraMap Qb LQ (16 : Qb)⁻¹ = 16⁻¹
    rw [map_inv₀, map_ofNat]

  obtain ⟨σ₁, hcσ₁, hμ₁, hμq₁⟩ :=
    ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_sixteenth_sub q hq2 K
  obtain ⟨σ₂, hcσ₂, hμ₂, hμq₂⟩ :=
    ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv q hq2 K

  let m : ↥(Λ q K) := ⟨lambdaModC Qb, lambdaModC_mem_lambdaFieldOver q K⟩
  let mq : ↥(Λ q K) := ⟨lambdaNModC Qb q, lambdaNModC_mem_lambdaFieldOver q K⟩
  have hm0' := ne_zero_of_jRel _ _ jLambda_Qb
  have hmq0' := ne_zero_of_jRel _ _ (jLambda_Qb_q q)
  haveI : CharZero ↥(Λ q K) := (Λ q K).subtype.charZero
  have hμ0 : lambdaModC Qb ≠ 0 := hm0'.1
  have hμ16 : 16 * lambdaModC Qb - 1 ≠ 0 := hm0'.2
  have hμq0 : lambdaNModC Qb q ≠ 0 := hmq0'.1
  have hμq16 : 16 * lambdaNModC Qb q - 1 ≠ 0 := hmq0'.2
  have hm0 : m ≠ 0 := fun h => hm0'.1 (congrArg Subtype.val h)
  have hmq0 : mq ≠ 0 := fun h => hmq0'.1 (congrArg Subtype.val h)
  have hm16 : 16 * m - 1 ≠ 0 := fun h => hm0'.2 (by
    have := congrArg Subtype.val h; push_cast at this; exact this)
  have hmq16 : 16 * mq - 1 ≠ 0 := fun h => hmq0'.2 (by
    have := congrArg Subtype.val h; push_cast at this; exact this)
  have hΛ16 : (16 : ↥(Λ q K)) ≠ 0 := by
    intro h; have := congrArg Subtype.val h; push_cast at this; norm_num at this
  have hΛ256 : (256 : ↥(Λ q K)) ≠ 0 := by
    intro h; have := congrArg Subtype.val h; push_cast at this; norm_num at this
  have hμ₁' : ((σ₁ m : ↥(Λ q K)) : LQ) = 16⁻¹ - lambdaModC Qb := hμ₁
  have hμq₁' : ((σ₁ mq : ↥(Λ q K)) : LQ) = 16⁻¹ - lambdaNModC Qb q := hμq₁
  have hμ₂' : ((σ₂ m : ↥(Λ q K)) : LQ) = (256 * lambdaModC Qb)⁻¹ := hμ₂
  have hμq₂' : ((σ₂ mq : ↥(Λ q K)) : LQ) = (256 * lambdaNModC Qb q)⁻¹ := hμq₂
  have e₁ : σ₁ m = 16⁻¹ - m := Subtype.ext (by rw [hμ₁']; push_cast; rfl)
  have eq₁ : σ₁ mq = 16⁻¹ - mq := Subtype.ext (by rw [hμq₁']; push_cast; rfl)
  have e₂ : σ₂ m = (256 * m)⁻¹ := Subtype.ext (by rw [hμ₂']; push_cast; rfl)
  have eq₂ : σ₂ mq = (256 * mq)⁻¹ := Subtype.ext (by rw [hμq₂']; push_cast; rfl)
  have hfix₁ := fixes_map_fieldOver q K σ₁ hcσ₁
    (by show Rj (σ₁ m) = Rj m; rw [e₁]; exact Rj_sixteenth_sub m hm0 hm16 hΛ16)
    (by show Rj (σ₁ mq) = Rj mq; rw [eq₁]; exact Rj_sixteenth_sub mq hmq0 hmq16 hΛ16)
  have hfix₂ := fixes_map_fieldOver q K σ₂ hcσ₂
    (by show Rj (σ₂ m) = Rj m; rw [e₂]; exact Rj_inv m hm0 hm16 hΛ16 hΛ256)
    (by show Rj (σ₂ mq) = Rj mq; rw [eq₂]; exact Rj_inv mq hmq0 hmq16 hΛ16 hΛ256)

  have hX0 : ∀ h, (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), h⟩ : ↥(Λ q K)) = m :=
    fun h => Subtype.ext (lambdaEval_X0 K)
  have hX1 : ∀ h, (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), h⟩ : ↥(Λ q K)) = mq :=
    fun h => Subtype.ext (lambdaEval_X1 K)

  obtain ⟨-, hF2, hF3, hF4⟩ := frob_rel (q := q) (redRestrict red K y₁) (redRestrict red K y₂)
  rcases level_two_values_cases hq a h01728 _ _ hy₁ hy₂ with h | h | h | h
  ·
    refine ⟨RingEquiv.refl _, fun x _ => rfl, ?_⟩
    intro B hBL hTB hσB I hI p hp
    rw [← h] at hp
    exact hI p hp
  ·
    refine ⟨σ₁, hfix₁, ?_⟩
    intro B hBL hTB hσB I hI
    apply transport_core red K σ₁ hcσ₁ y₂ B hBL hTB hσB I
    · intro c hc
      exact hI (MvPolynomial.C c) (by rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; exact hc)
    · have key := hI (MvPolynomial.C (c16 - y₂) - MvPolynomial.X 0) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-(16 : k)⁻¹) * h + (redRestrict red K y₁ + redRestrict red K y₂) * inv_mul_cancel₀ hk16)
      convert key using 1
      apply Subtype.ext
      show ((σ₁ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C y₂)
        = lambdaEval q (coeffSubring A K) (MvPolynomial.C (c16 - y₂) - MvPolynomial.X 0)
      rw [hX0, hμ₁']
      simp only [map_sub, lambdaEval_C, lambdaEval_X0]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat, hc16Q]
      ring
    · have key := hI (MvPolynomial.C (c16 - y₂ ^ q) - MvPolynomial.X 1) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-(16 : k)⁻¹) * (hF2 h) + (redRestrict red K y₁ ^ q + redRestrict red K y₂ ^ q) * inv_mul_cancel₀ hk16)
      convert key using 1
      apply Subtype.ext
      show ((σ₁ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C (y₂ ^ q))
        = lambdaEval q (coeffSubring A K) (MvPolynomial.C (c16 - y₂ ^ q) - MvPolynomial.X 1)
      rw [hX1, hμq₁']
      simp only [map_sub, lambdaEval_C, lambdaEval_X1]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat, hc16Q]
      ring
  ·
    refine ⟨σ₂, hfix₂, ?_⟩
    intro B hBL hTB hσB I hI
    apply transport_core red K σ₂ hcσ₂ y₂ B hBL hTB hσB I
    · intro c hc
      exact hI (MvPolynomial.C c) (by rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; exact hc)
    · have key := hI (MvPolynomial.C 1 - MvPolynomial.C (256 * y₂) * MvPolynomial.X 0) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-1 : k) * h)
      have key2 := I.mul_mem_left ⟨_, hσB _ (hTB (MvPolynomial.X 0))⟩ key
      convert key2 using 1
      apply Subtype.ext
      show ((σ₂ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C y₂)
        = ((σ₂ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), _⟩ : ↥(Λ q K)) : LQ)
          * lambdaEval q (coeffSubring A K) (MvPolynomial.C 1 - MvPolynomial.C (256 * y₂) * MvPolynomial.X 0)
      rw [hX0, hμ₂']
      simp only [map_sub, map_mul, lambdaEval_C, lambdaEval_X0]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat]
      have hden : -1 + lambdaModC Qb * 16 ≠ 0 := fun h0 => hμ16 (by linear_combination h0)
      have hdenq : -1 + lambdaNModC Qb q * 16 ≠ 0 := fun h0 => hμq16 (by linear_combination h0)
      field_simp
      try ring
    · have key := hI (MvPolynomial.C 1 - MvPolynomial.C (256 * y₂ ^ q) * MvPolynomial.X 1) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-1 : k) * (hF3 h))
      have key2 := I.mul_mem_left ⟨_, hσB _ (hTB (MvPolynomial.X 1))⟩ key
      convert key2 using 1
      apply Subtype.ext
      show ((σ₂ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C (y₂ ^ q))
        = ((σ₂ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), _⟩ : ↥(Λ q K)) : LQ)
          * lambdaEval q (coeffSubring A K) (MvPolynomial.C 1 - MvPolynomial.C (256 * y₂ ^ q) * MvPolynomial.X 1)
      rw [hX1, hμq₂']
      simp only [map_sub, map_mul, lambdaEval_C, lambdaEval_X1]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat]
      have hden : -1 + lambdaModC Qb * 16 ≠ 0 := fun h0 => hμ16 (by linear_combination h0)
      have hdenq : -1 + lambdaNModC Qb q * 16 ≠ 0 := fun h0 => hμq16 (by linear_combination h0)
      field_simp
      try ring
  ·
    let σ₃ : ↥(Λ q K) ≃+* ↥(Λ q K) := σ₂.trans (σ₁.trans σ₂)
    have hσ₃ : ∀ x, σ₃ x = σ₂ (σ₁ (σ₂ x)) := fun _ => rfl
    have hcσ₃ : ∀ x : ↥(Λ q K), (x : LQ) ∈ Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) →
        σ₃ x = x := by
      intro x hx; rw [hσ₃, hcσ₂ x hx, hcσ₁ x hx, hcσ₂ x hx]
    have hfix₃ : ∀ x : ↥(Λ q K), (x : LQ) ∈ (fieldOver (1 * q) K).map (qExpand Qb 2) → σ₃ x = x := by
      intro x hx; rw [hσ₃, hfix₂ x hx, hfix₁ x hx, hfix₂ x hx]
    have e₃ : σ₃ m = m / (16 * m - 1) := by
      have step : σ₃ m = (256 * (16⁻¹ - (256 * m)⁻¹))⁻¹ := by
        simp only [hσ₃, e₂, e₁, map_inv₀, map_mul, map_sub, map_ofNat]
      have h2 : (256 : ↥(Λ q K)) * (16⁻¹ - (256 * m)⁻¹) = (16 * m - 1) / m := by
        field_simp
        ring
      rw [step, h2, inv_div]
    have eq₃ : σ₃ mq = mq / (16 * mq - 1) := by
      have step : σ₃ mq = (256 * (16⁻¹ - (256 * mq)⁻¹))⁻¹ := by
        simp only [hσ₃, eq₂, eq₁, map_inv₀, map_mul, map_sub, map_ofNat]
      have h2 : (256 : ↥(Λ q K)) * (16⁻¹ - (256 * mq)⁻¹) = (16 * mq - 1) / mq := by
        field_simp
        ring
      rw [step, h2, inv_div]
    have e₃' : ((σ₃ m : ↥(Λ q K)) : LQ) = lambdaModC Qb / (16 * lambdaModC Qb - 1) := by
      rw [e₃]; push_cast; rfl
    have eq₃' : ((σ₃ mq : ↥(Λ q K)) : LQ) = lambdaNModC Qb q / (16 * lambdaNModC Qb q - 1) := by
      rw [eq₃]; push_cast; rfl
    refine ⟨σ₃, hfix₃, ?_⟩
    intro B hBL hTB hσB I hI
    have h16B : (16 : LQ) ∈ B := by exact_mod_cast natCast_mem B 16
    apply transport_core red K σ₃ hcσ₃ y₂ B hBL hTB hσB I
    · intro c hc
      exact hI (MvPolynomial.C c) (by rw [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_C]; exact hc)
    · have key := hI (MvPolynomial.C (1 - 16 * y₂) * MvPolynomial.X 0 + MvPolynomial.C y₂) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-1 : k) * h)
      have key2 := I.mul_mem_left
        (⟨16 * _ - 1, sub_mem (mul_mem h16B (hσB _ (hTB (MvPolynomial.X 0)))) (one_mem B)⟩ : ↥B) key
      convert key2 using 1
      apply Subtype.ext
      show ((σ₃ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C y₂)
        = (16 * ((σ₃ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0), _⟩ : ↥(Λ q K)) : LQ) - 1)
          * lambdaEval q (coeffSubring A K) (MvPolynomial.C (1 - 16 * y₂) * MvPolynomial.X 0 + MvPolynomial.C y₂)
      rw [hX0, e₃']
      simp only [map_add, map_mul, lambdaEval_C, lambdaEval_X0]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat]
      linear_combination key_identity (lambdaModC Qb) (algebraMap Qb LQ (y₂ : Qb)) hμ16
    · have key := hI (MvPolynomial.C (1 - 16 * y₂ ^ q) * MvPolynomial.X 1 + MvPolynomial.C (y₂ ^ q)) (by
        simp only [pointEval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_add,
          MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons]
        simp only [map_sub, map_add, map_mul, map_one, map_pow, map_ofNat, hc16]
        linear_combination (-1 : k) * (hF4 h))
      have key2 := I.mul_mem_left
        (⟨16 * _ - 1, sub_mem (mul_mem h16B (hσB _ (hTB (MvPolynomial.X 1)))) (one_mem B)⟩ : ↥B) key
      convert key2 using 1
      apply Subtype.ext
      show ((σ₃ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), _⟩ : ↥(Λ q K)) : LQ)
          - lambdaEval q (coeffSubring A K) (MvPolynomial.C (y₂ ^ q))
        = (16 * ((σ₃ ⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1), _⟩ : ↥(Λ q K)) : LQ) - 1)
          * lambdaEval q (coeffSubring A K) (MvPolynomial.C (1 - 16 * y₂ ^ q) * MvPolynomial.X 1 + MvPolynomial.C (y₂ ^ q))
      rw [hX1, eq₃']
      simp only [map_add, map_mul, lambdaEval_C, lambdaEval_X1]
      push_cast
      simp only [hn256, hn16, hn1, map_mul, map_sub, map_add, map_one, map_ofNat, map_pow]
      linear_combination key_identity (lambdaNModC Qb q) (algebraMap Qb LQ (y₂ : Qb) ^ q) hμq16

end Main
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

end D3Proof
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"
end ModularCurve
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

end
p2m_reactivate "P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve.D3Proof P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem.ModularCurve"

end S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_forall_map_lambdaEval_mem (solution)
