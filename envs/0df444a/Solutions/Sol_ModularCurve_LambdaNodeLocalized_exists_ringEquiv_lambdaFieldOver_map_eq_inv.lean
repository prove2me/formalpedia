-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_map_eq_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0b8fc735-793c-5640-b4f4-4c191c323c5c

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_LambdaModularPolynomialData
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_of_involutive_subst
import Theorems.Thm_ModularCurve_LambdaModularPolynomialData_psi_reciprocal
import Theorems.Thm_ModularCurve_LambdaModularPolynomialData_natDegree_coeff_le
import Theorems.Thm_ModularCurve_transcendental_lambdaModC
import Theorems.Thm_ModularCurve_exists_lambdaKroneckerCongruence
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def"
p2m_attr_erase "simp" "AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk"
p2m_attr_erase "simp" "ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero"
p2m_attr_erase "simp" "ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv.ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv.ModularCurve.LambdaNodeLocalized"
open Finset

namespace ModularCurve
p2m_export "ModularCurve" "CharPReduction.constSeries qExpand_injective lambdaModC lambdaNModC evalAtLambdaInt evalAtLambdaInt_X laurentMap laurentMap_qExpand laurentMap_laurentMap LambdaModularPolynomialData LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_of_involutive_subst LambdaModularPolynomialData.psi_reciprocal LambdaModularPolynomialData.natDegree_coeff_le transcendental_lambdaModC exists_lambdaKroneckerCongruence"
p2m_open "ModularCurve"
namespace LambdaNodeLocalized
p2m_export "ModularCurve.LambdaNodeLocalized" "lambdaFieldOver lambdaModC_mem_lambdaFieldOver lambdaNModC_mem_lambdaFieldOver exists_ringEquiv_lambdaFieldOver_of_involutive_subst"
p2m_open "ModularCurve.LambdaNodeLocalized"
namespace Anh2

local notation "Qb" => AlgebraicClosure ℚ
local notation "LQ" => LaurentSeries (AlgebraicClosure ℚ)

theorem eval₂_Ψ_eq_zero {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q)
    {L : Type*} [Field L] [Algebra ℚ L] :
    data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L)) (lambdaNModC L q) = 0 := by
  set θ : Polynomial ℤ →+* LaurentSeries L := Polynomial.eval₂RingHom (Int.castRingHom _) (lambdaModC L) with hθ
  set E : LaurentSeries ℚ →+* LaurentSeries L := laurentMap (algebraMap ℚ L) with hE
  have hZ : (algebraMap ℚ L).comp (Int.castRingHom ℚ) = Int.castRingHom L := RingHom.ext_int _ _
  have hE1 : E (lambdaNModC ℚ q) = lambdaNModC L q := by
    rw [hE, lambdaNModC, laurentMap_qExpand, lambdaNModC, lambdaModC, lambdaModC, laurentMap_laurentMap, hZ]
  have hEθ : E.comp ((laurentMap (Int.castRingHom ℚ)).comp evalAtLambdaInt) = θ := by
    apply Polynomial.ringHom_ext
    · intro n
      simp only [RingHom.coe_comp, Function.comp_apply, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C,
        map_intCast, eq_intCast, evalAtLambdaInt]
    · rw [RingHom.coe_comp, Function.comp_apply, RingHom.coe_comp, Function.comp_apply, evalAtLambdaInt_X, hE,
        laurentMap_laurentMap, hZ, hθ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, lambdaModC]
  have h := congrArg E data.eval_eq_zero
  rw [map_zero, Polynomial.hom_eval₂, hEθ, hE1] at h
  exact h

section Generic
variable {M : Type*} [Field M]

def ev (P : Polynomial (Polynomial ℤ)) (a b : M) : M :=
  P.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom M) a) b

theorem ev_eq_sum (P : Polynomial (Polynomial ℤ)) (N : ℕ) (hY : P.natDegree ≤ N) (hX : ∀ k, (P.coeff k).natDegree ≤ N)
    (a b : M) :
    ev P a b = ∑ k ∈ range (N + 1), ∑ i ∈ range (N + 1), (((P.coeff k).coeff i : ℤ) : M) * a ^ i * b ^ k := by
  unfold ev
  rw [Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le hY)]
  refine sum_congr rfl fun k _ => ?_
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range' _ (Nat.lt_succ_of_le (hX k)), sum_mul]
  refine sum_congr rfl fun i _ => ?_
  rw [eq_intCast]

theorem recip_identity (P : Polynomial (Polynomial ℤ)) (N : ℕ) (hY : P.natDegree ≤ N) (hX : ∀ k, (P.coeff k).natDegree ≤ N)
    (hrec : ∀ i k : ℕ, i + k ≤ N → (P.coeff (N - k)).coeff (N - i) = 256 ^ (N - i - k) * (P.coeff k).coeff i)
    (a b : M) (ha : a ≠ 0) (hb : b ≠ 0) (h256 : (256 : M) ≠ 0) :
    (256 * a) ^ N * (256 * b) ^ N * ev P (256 * a)⁻¹ (256 * b)⁻¹ = (256 : M) ^ N * ev P a b := by

  have key : ∀ i k : ℕ, i ≤ N → k ≤ N →
      ((P.coeff (N - k)).coeff (N - i) : ℤ) * 256 ^ (i + k) = 256 ^ N * (P.coeff k).coeff i := by
    intro i k hi hk
    by_cases hik : i + k ≤ N
    · rw [hrec i k hik, mul_comm, ← mul_assoc, ← pow_add]
      congr 2; omega
    · push_neg at hik
      have h' := hrec (N - i) (N - k) (by omega)
      rw [Nat.sub_sub_self hi, Nat.sub_sub_self hk] at h'
      have e : i - (N - k) = i + k - N := by omega
      rw [e] at h'
      rw [h', ← mul_assoc, mul_comm ((256 : ℤ) ^ N), mul_assoc, mul_comm ((P.coeff (N - k)).coeff (N - i))]
      rw [← mul_assoc, ← pow_add]
      congr 2; omega
  have hA : (256 * a) ≠ 0 := mul_ne_zero h256 ha
  have hB : (256 * b) ≠ 0 := mul_ne_zero h256 hb
  rw [ev_eq_sum P N hY hX, ev_eq_sum P N hY hX, mul_sum, mul_sum]

  have hL : ∀ k ∈ range (N + 1), (256 * a) ^ N * (256 * b) ^ N *
      ∑ i ∈ range (N + 1), (((P.coeff k).coeff i : ℤ) : M) * (256 * a)⁻¹ ^ i * (256 * b)⁻¹ ^ k
      = ∑ i ∈ range (N + 1), (((P.coeff k).coeff i : ℤ) : M) * (256 * a) ^ (N - i) * (256 * b) ^ (N - k) := by
    intro k hk
    rw [mul_sum]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    have e1 : (256 * a) ^ N * (256 * a)⁻¹ ^ i = (256 * a) ^ (N - i) := by
      rw [inv_pow, ← div_eq_mul_inv, pow_sub₀ _ hA hi', div_eq_mul_inv]
    have e2 : (256 * b) ^ N * (256 * b)⁻¹ ^ k = (256 * b) ^ (N - k) := by
      rw [inv_pow, ← div_eq_mul_inv, pow_sub₀ _ hB hk', div_eq_mul_inv]
    calc (256 * a) ^ N * (256 * b) ^ N * ((((P.coeff k).coeff i : ℤ) : M) * (256 * a)⁻¹ ^ i * (256 * b)⁻¹ ^ k)
        = (((P.coeff k).coeff i : ℤ) : M) * ((256 * a) ^ N * (256 * a)⁻¹ ^ i) * ((256 * b) ^ N * (256 * b)⁻¹ ^ k) := by ring
      _ = _ := by rw [e1, e2]
  rw [sum_congr rfl hL]

  have hrefl : ∑ k ∈ range (N + 1), ∑ i ∈ range (N + 1), (((P.coeff k).coeff i : ℤ) : M) * (256 * a) ^ (N - i) * (256 * b) ^ (N - k)
      = ∑ k ∈ range (N + 1), ∑ i ∈ range (N + 1),
          (((P.coeff (N - k)).coeff (N - i) : ℤ) : M) * (256 * a) ^ i * (256 * b) ^ k := by
    rw [← sum_range_reflect (fun k => ∑ i ∈ range (N + 1),
      (((P.coeff (N - k)).coeff (N - i) : ℤ) : M) * (256 * a) ^ i * (256 * b) ^ k) (N + 1)]
    refine sum_congr rfl fun k hk => ?_
    have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
    simp only [Nat.add_sub_cancel]
    rw [← sum_range_reflect (fun i => (((P.coeff (N - (N - k))).coeff (N - i) : ℤ) : M) * (256 * a) ^ i *
      (256 * b) ^ (N - k)) (N + 1)]
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self hk', Nat.sub_sub_self hi']
  rw [hrefl]
  refine sum_congr rfl fun k hk => ?_
  rw [mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hkey := key i k hi' hk'
  have hkeyM : (((P.coeff (N - k)).coeff (N - i) : ℤ) : M) * (256 : M) ^ (i + k) = (256 : M) ^ N * (((P.coeff k).coeff i : ℤ) : M) := by
    exact_mod_cast congrArg (Int.cast : ℤ → M) hkey
  calc (((P.coeff (N - k)).coeff (N - i) : ℤ) : M) * (256 * a) ^ i * (256 * b) ^ k
      = ((((P.coeff (N - k)).coeff (N - i) : ℤ) : M) * (256 : M) ^ (i + k)) * a ^ i * b ^ k := by rw [pow_add]; ring
    _ = (256 : M) ^ N * (((P.coeff k).coeff i : ℤ) : M) * a ^ i * b ^ k := by rw [hkeyM]
    _ = (256 : M) ^ N * ((((P.coeff k).coeff i : ℤ) : M) * a ^ i * b ^ k) := by ring

end Generic

theorem hroot {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    data.Ψ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom LQ) (256 * lambdaModC Qb)⁻¹)
      (256 * lambdaNModC Qb q)⁻¹ = 0 := by
  have hμ0 : lambdaModC Qb ≠ 0 := by
    intro h0
    exact ModularCurve.transcendental_lambdaModC Qb (h0 ▸ isAlgebraic_zero)
  have hμq0 : lambdaNModC Qb q ≠ 0 := by
    intro h0
    apply hμ0
    apply qExpand_injective (R := Qb) (N := q)
    rw [← lambdaNModC, h0, map_zero]
  haveI : CharZero LQ := charZero_of_injective_algebraMap (algebraMap ℚ LQ).injective
  have h256 : (256 : LQ) ≠ 0 := by norm_num
  have hid := recip_identity (M := LQ) data.Ψ (q + 1) data.natDegree_eq.le
    (ModularCurve.LambdaModularPolynomialData.natDegree_coeff_le q hq2 data)
    (fun i k hik => ModularCurve.LambdaModularPolynomialData.psi_reciprocal q hq2 data i k hik)
    (lambdaModC Qb) (lambdaNModC Qb q) hμ0 hμq0 h256
  have hzero : ev data.Ψ (lambdaModC Qb) (lambdaNModC Qb q) = 0 := eval₂_Ψ_eq_zero data
  rw [hzero, mul_zero] at hid
  have hne : (256 * lambdaModC Qb) ^ (q + 1) * (256 * lambdaNModC Qb q) ^ (q + 1) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (mul_ne_zero h256 hμ0)) (pow_ne_zero _ (mul_ne_zero h256 hμq0))
  exact (mul_eq_zero.mp hid).resolve_left hne

end Anh2
end LambdaNodeLocalized
end ModularCurve

end

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv.ModularCurve ModularCurve.NodeLocalized _root_.ModularCurve.LambdaNodeLocalized _root_.P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv.ModularCurve.LambdaNodeLocalized in
theorem solution
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) :
    ∃ σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K),
      (∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
          Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x) ∧
      ((σ ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) :
          LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
      ((σ ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) :
          LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ := by
  classical
  obtain ⟨data, -⟩ := ModularCurve.exists_lambdaKroneckerCongruence q hq2
  set L := LaurentSeries (AlgebraicClosure ℚ)
  set F := lambdaFieldOver q K with hF
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ L).injective
  have h256L : (256 : L) ≠ 0 := by norm_num
  have h256F : (256 : L) ∈ F := natCast_mem F 256
  have hμ'F : (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∈ F :=
    inv_mem (mul_mem h256F (lambdaModC_mem_lambdaFieldOver q K))
  have hμq'F : (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ ∈ F :=
    inv_mem (mul_mem h256F (lambdaNModC_mem_lambdaFieldOver q K))

  have hμ' : Transcendental (AlgebraicClosure ℚ) (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ := by
    intro halg
    apply ModularCurve.transcendental_lambdaModC (AlgebraicClosure ℚ)
    have h1 : IsAlgebraic (AlgebraicClosure ℚ) (256 * lambdaModC (AlgebraicClosure ℚ)) := by
      simpa using halg.inv
    have h2 : IsAlgebraic (AlgebraicClosure ℚ) ((algebraMap (AlgebraicClosure ℚ) L 256⁻¹) * (256 * lambdaModC (AlgebraicClosure ℚ))) :=
      (isAlgebraic_algebraMap _).mul h1
    have e : (algebraMap (AlgebraicClosure ℚ) L 256⁻¹) * (256 * lambdaModC (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) := by
      rw [map_inv₀, map_ofNat, ← mul_assoc, inv_mul_cancel₀ h256L, one_mul]
    rwa [e] at h2
  refine ModularCurve.LambdaNodeLocalized.exists_ringEquiv_lambdaFieldOver_of_involutive_subst q hq2 data K
    _ _ hμ' (ModularCurve.LambdaNodeLocalized.Anh2.hroot hq2 data) hμ'F hμq'F ?_
  intro φ hφc hφμ hφμq
  have h256φ : φ ⟨(256 : L), h256F⟩ = 256 := by
    have : (⟨(256 : L), h256F⟩ : ↥F) = (256 : ↥F) := Subtype.ext rfl
    rw [this, map_ofNat]
  constructor
  · have e : (⟨(256 * lambdaModC (AlgebraicClosure ℚ))⁻¹, hμ'F⟩ : ↥F)
        = (⟨(256 : L), h256F⟩ * ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_inv₀, map_mul, h256φ, hφμ, mul_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ h256L, one_mul]
  · have e : (⟨(256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹, hμq'F⟩ : ↥F)
        = (⟨(256 : L), h256F⟩ * ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩)⁻¹ := Subtype.ext rfl
    rw [e, map_inv₀, map_mul, h256φ, hφμq, mul_inv, inv_inv, ← mul_assoc, inv_mul_cancel₀ h256L, one_mul]

end S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_lambdaFieldOver_map_eq_inv (solution)
