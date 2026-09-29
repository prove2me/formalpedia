-- Prove2me | solution 1 for ModularCurve.LambdaNodeLocalized.exists_ringEquiv_sub_smul_mem_sq_sup_of_stabilizer_of_eq_zero_or_eq_1728
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/92aa7b1f-d4d4-5222-85f1-5e0fcf38c6fa

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeDescent
import Definitions.Def_ModularCurve_JWidth
import Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
import Theorems.Thm_ModularCurve_NodeLocalized_coeffSubring_eq_or_isDiscreteValuationRing
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_sub_smul_mem_sq_sup_of_stabilizer_of_eq_zero_or_eq_1728
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA AlgebraicCurve.Place.instIsScalarTowerSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Divisor.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instSMulAlgEquiv AlgebraicCurve.Place.instIsPrincipalIdealRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instIsDiscreteValuationRingSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Pic0.instDistribMulActionAlgEquiv AlgebraicCurve.Place.instAlgebraSubtypeMemValuationSubringToValuationSubring AlgebraicCurve.Place.instMulActionAlgEquiv AlgebraicCurve.Pic0.instSMulAlgEquiv ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois ModularCurve.instSMulAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange ModularCurve.instDistribMulActionAlgEquivRatPic0SubtypeLaurentSeriesMemIntermediateFieldLaurentBaseChange AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instDistribMulActionSubtypeProdRingAutMemSubgroupDivisor AlgebraicCurve.Pic0.instModuleZModTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instDistribMulActionTorsion AlgebraicCurve.SemilinearAut.instSMulSubtypeProdRingAutMemSubgroupPic0 AlgebraicCurve.SemilinearAut.instSMulTorsion AlgebraicCurve.SemilinearAut.instMulActionSubtypeProdRingAutMemSubgroupPlace AlgebraicCurve.SemilinearAut.instSMulCommClassZModTorsion AlgebraicCurve.SemilinearAut.instMulSemiringActionSubtypeProdRingAutMemSubgroup AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.instFundamentalIdentityOfSumRamificationInertia AlgebraicCurve.Place.instIsScalarTowerResidueFieldRestrictPushforward AlgebraicCurve.Place.instAlgebraResidueFieldRestrictPushforward AlgebraicCurve.Place.instIsLocalHomRestrictInclusion AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation instDecEqAlgebraicClosureRat"
p2m_attr_erase "instance" "WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv WeierstrassCurve.Affine.Point.instSMulCommClassAlgEquivZModTorsionBy ModularCurve.instFiniteProjectiveLine ModularCurve.unimodularRowSetoid"
p2m_attr_erase "simp" "ModularCurve.LambdaModularPolynomialData.mk.sizeOf_spec ModularCurve.LambdaModularPolynomialData.mk.injEq ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg AlgebraicCurve.Place.mk.injEq AlgebraicCurve.Divisor.degree_single AlgebraicCurve.Divisor.smul_single AlgebraicCurve.Place.smul_toValuationSubring AlgebraicCurve.Place.heightOneSpectrum_asIdeal AlgebraicCurve.Place.coe_algebraMap AlgebraicCurve.Place.ord_one AlgebraicCurve.Place.coe_smulRingEquiv_apply AlgebraicCurve.Pic0.coe_degZeroSMulHom AlgebraicCurve.Place.deg_smul AlgebraicCurve.Pic0.mk_zero AlgebraicCurve.Place.mk.sizeOf_spec"
p2m_attr_erase "simp" "AlgebraicCurve.Divisor.degree_smul AlgebraicCurve.Pic0.mk_add AlgebraicCurve.Place.ord_zero AlgebraicCurve.Place.ofHeightOneSpectrum_toValuationSubring ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.coe_cuspidalDivisor₀ ModularCurve.baseAut_arithmeticGalois ModularCurve.JZero.torsionGaloisRep_apply ModularCurve.coe_arithmeticRingAut_apply ModularCurve.toRingAut_arithmeticGalois AlgebraicCurve.SemilinearAut.toRingAut_inv AlgebraicCurve.SemilinearAut.smul_def AlgebraicCurve.SemilinearAut.smul_single AlgebraicCurve.SemilinearAut.smul_toValuationSubring AlgebraicCurve.SemilinearAut.baseAut_inv AlgebraicCurve.SemilinearAut.baseAut_ofAlgAut AlgebraicCurve.SemilinearAut.toRingAut_ofAlgAut AlgebraicCurve.SemilinearAut.torsionRep_apply AlgebraicCurve.SemilinearAut.toRingAut_one AlgebraicCurve.SemilinearAut.deg_smul AlgebraicCurve.SemilinearAut.degree_smul AlgebraicCurve.SemilinearAut.coe_degZeroSMulHom AlgebraicCurve.SemilinearAut.baseAut_mul AlgebraicCurve.SemilinearAut.coe_smulValuationSubringEquiv_apply AlgebraicCurve.SemilinearAut.baseAut_one AlgebraicCurve.SemilinearAut.ofAlgAut_smul AlgebraicCurve.SemilinearAut.coe_torsion_smul AlgebraicCurve.SemilinearAut.toRingAut_mul AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.Divisor.mapRestrict_single AlgebraicCurve.Divisor.pushforward_single AlgebraicCurve.Place.coe_restrictInclusion AlgebraicCurve.Place.mem_fiber AlgebraicCurve.Place.restrict_toValuationSubring AlgebraicCurve.Divisor.degree_pushforward"
p2m_attr_erase "simp" "AlgebraicCurve.Place.restrictResidueMap_residue AlgebraicCurve.Pic0.coe_pushforwardDegZeroHom AlgebraicCurve.Pic0.coe_pullbackDegZeroHom AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.Divisor.degree_pushforwardAlong AlgebraicCurve.Pic0.coe_degZeroCorrespondence AlgebraicCurve.Place.mem_fiberAlong AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.aeval_heckeGen ModularCurve.coe_mTorsionGaloisRep_apply ModularCurve.eisensteinSystem_of_dvd ModularCurve.eisensteinSystem_of_not_dvd FreyPackage.mk.sizeOf_spec FreyPackage.mk.injEq WeierstrassCurve.Affine.Point.galoisRepModuleEnd_apply ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero"
p2m_attr_erase "simp" "ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.ProjectiveLine.map_mk"

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option synthInstance.maxHeartbeats 1600000

namespace S14STAB

open Ideal

section Binomial
variable {S : Type*} [CommRing S]

theorem add_pow_sub_pow_mem (p : ℕ) (hp : p.Prime) (a d : S) (J : Ideal S)
    (hq : ∀ s : S, (p : S) * s ∈ J) (hd : d ^ 2 ∈ J) : (a + d) ^ p - a ^ p ∈ J := by
  obtain ⟨r, hr⟩ := (Commute.all a d).exists_add_pow_prime_eq hp
  rw [hr]
  have h2 : d ^ p ∈ J := by
    have : d ^ p = d ^ 2 * d ^ (p - 2) := by
      rw [← pow_add]; congr 1; have := hp.two_le; omega
    rw [this]; exact J.mul_mem_right _ hd
  have : a ^ p + d ^ p + (p : S) * a * d * r - a ^ p = d ^ p + (p : S) * (a * d * r) := by ring
  rw [this]
  exact J.add_mem h2 (hq _)
end Binomial

section Taylor
variable {S : Type*} [CommRing S]

theorem moebius_taylor (α β γ δ y m u v : S) (hu : (γ * y + δ) * u = 1) (hv : (γ * (y + m) + δ) * v = 1) :
    (α * (y + m) + β) * v
      = (α * y + β) * u + (α * δ - β * γ) * u ^ 2 * m + m ^ 2 * (-(γ * (α * δ - β * γ) * u ^ 2 * v)) := by
  linear_combination (-(α * (y + m) + β) * v - (α * δ - β * γ) * m * u * v) * hu
    + ((α * y + β) * u + (α * δ - β * γ) * m * u ^ 2) * hv

end Taylor

section Consts
variable {R : Type*} [CommRing R]

theorem natCast_pow_prime_sub_mem (p : ℕ) (hp : p.Prime) (n : ℕ) :
    ((n : R)) ^ p - (n : R) ∈ Ideal.span {((p : ℕ) : R)} := by
  have h : ((p : ℕ) : ℤ) ∣ (n : ℤ) ^ p - n := by
    haveI := Fact.mk hp
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.pow_card, sub_self]
  obtain ⟨c, hc⟩ := h
  rw [Ideal.mem_span_singleton]
  refine ⟨(c : R), ?_⟩
  have := congrArg (Int.cast : ℤ → R) hc
  push_cast at this
  exact this

theorem P_pow_sub_mem (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (z : R) :
    (256 * (z ^ p) ^ 2 - 16 * z ^ p + 1) - (256 * z ^ 2 - 16 * z + 1) ^ p ∈ Ideal.span {((p : ℕ) : R)} := by
  set I : Ideal R := Ideal.span {((p : ℕ) : R)}
  have hI : ∀ s : R, (p : R) * s ∈ I := fun s => Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨r₁, h₁⟩ := (Commute.all (256 * z ^ 2 + -(16 * z)) (1 : R)).exists_add_pow_prime_eq hp
  obtain ⟨r₂, h₂⟩ := (Commute.all (256 * z ^ 2) (-(16 * z) : R)).exists_add_pow_prime_eq hp
  have h256 := natCast_pow_prime_sub_mem (R := R) p hp 256
  have h16 := natCast_pow_prime_sub_mem (R := R) p hp 16

  have e0 : (256 * z ^ 2 - 16 * z + 1 : R) = 256 * z ^ 2 + -(16 * z) + 1 := by ring
  rw [e0, h₁, h₂]
  have key : (256 * (z ^ p) ^ 2 - 16 * z ^ p + 1 : R)
      - ((256 * z ^ 2) ^ p + (-(16 * z)) ^ p + (p : R) * (256 * z ^ 2) * -(16 * z) * r₂ + 1 ^ p
          + (p : R) * (256 * z ^ 2 + -(16 * z)) * 1 * r₁)
      = -(((256 : R) ^ p - 256) * (z ^ p) ^ 2) + ((16 : R) ^ p - 16) * z ^ p
        + (p : R) * (256 * z ^ 2 * (16 * z) * r₂ - (256 * z ^ 2 + -(16 * z)) * r₁) := by
    rw [neg_pow, Odd.neg_one_pow hodd, one_pow]
    ring
  rw [key]
  refine I.add_mem (I.add_mem (I.neg_mem (I.mul_mem_right _ ?_)) (I.mul_mem_right _ ?_)) (hI _)
  · exact_mod_cast h256
  · exact_mod_cast h16

theorem approx_root_unique (J I₁ : Ideal R) (hJ : J ≤ I₁) (z₁ z₂ w : R)
    (hz : z₂ - z₁ ∈ I₁) (hP₁ : 256 * z₁ ^ 2 - 16 * z₁ + 1 ∈ J) (hP₂ : 256 * z₂ ^ 2 - 16 * z₂ + 1 ∈ J)
    (hw : w * (512 * z₁ - 16 + 256 * (z₂ - z₁)) = 1) : z₂ - z₁ ∈ J := by
  have : z₂ - z₁ = ((256 * z₂ ^ 2 - 16 * z₂ + 1) - (256 * z₁ ^ 2 - 16 * z₁ + 1)) * w := by
    have h : (256 * z₂ ^ 2 - 16 * z₂ + 1) - (256 * z₁ ^ 2 - 16 * z₁ + 1)
        = (z₂ - z₁) * (512 * z₁ - 16 + 256 * (z₂ - z₁)) := by ring
    rw [h, mul_assoc, mul_comm _ w, hw, mul_one]
  rw [this]
  exact J.mul_mem_right _ (J.sub_mem hP₂ hP₁)

theorem newton_step (y u : R) (hu : u * (512 * y - 16) = 1) :
    256 * (y - (256 * y ^ 2 - 16 * y + 1) * u) ^ 2 - 16 * (y - (256 * y ^ 2 - 16 * y + 1) * u) + 1
      = 256 * ((256 * y ^ 2 - 16 * y + 1) * u) ^ 2 := by
  linear_combination (-(256 * y ^ 2 - 16 * y + 1)) * hu

theorem phi_sub_self (t v : R) (hv : (16 - 256 * t) * v = 1) :
    v - t = (256 * t ^ 2 - 16 * t + 1) * v := by
  linear_combination t * hv

end Consts

section Case0
variable {κ : Type*} [Field κ]

theorem root_facts (p : ℕ) [Fact p.Prime] [CharP κ p] (hp5 : 5 ≤ p) (l : κ)
    (hl : 256 * l ^ 2 - 16 * l + 1 = 0) :
    l ^ (p ^ 2) = l ∧ (256 * l ^ 2) ^ 3 = 1 ∧ 256 * l ^ 2 ≠ 1 ∧ (256 * l ^ 2) ^ 2 ≠ 1 ∧
      1 - 16 * l ≠ 0 ∧ 16 * l * (1 - 16 * l) = 1 ∧ (512 * l - 16) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have h3 : (3 : κ) ≠ 0 := by
    rw [show (3 : κ) = ((3 : ℕ) : κ) by norm_num, Ne, CharP.cast_eq_zero_iff κ p]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have h16' : (16 : κ) ≠ 0 := by
    rw [show (16 : κ) = ((16 : ℕ) : κ) by norm_num, Ne, CharP.cast_eq_zero_iff κ p]
    intro h
    have h2 : p ∣ 2 := hp.dvd_of_dvd_pow (show p ∣ 2 ^ 4 by simpa using h)
    have := Nat.le_of_dvd two_pos h2; omega
  have hL2 : (16 * l) ^ 2 = 16 * l - 1 := by linear_combination hl
  have hL3 : (16 * l) ^ 3 = -1 := by linear_combination (16 * l + 1) * hL2
  have hL6 : (16 * l) ^ 6 = 1 := by
    have : (16 * l) ^ 6 = ((16 * l) ^ 3) ^ 2 := by ring
    rw [this, hL3]; norm_num

  have hp3 : p % 3 ≠ 0 := by
    intro h
    have : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).1 this with h' | h' <;> omega
  have hp2 : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · exact h
  have hsq : p ^ 2 % 6 = 1 := by
    have h6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
    rw [Nat.pow_mod]
    rcases h6 with h | h <;> rw [h]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have hLp : (16 * l) ^ (p ^ 2) = 16 * l := by
      rw [← Nat.div_add_mod (p ^ 2) 6, pow_add, pow_mul, hL6, one_pow, one_mul, hsq, pow_one]
    have h1 : ((16 : ℕ) : κ) ^ p = ((16 : ℕ) : κ) := by rw [← frobenius_def, map_natCast]
    have h16 : (16 : κ) ^ (p ^ 2) = 16 := by
      have : ((16 : ℕ) : κ) ^ (p ^ 2) = ((16 : ℕ) : κ) := by rw [pow_two, pow_mul, h1, h1]
      exact_mod_cast this
    rw [mul_pow, h16] at hLp
    exact mul_left_cancel₀ h16' hLp
  · have : (256 : κ) * l ^ 2 = (16 * l) ^ 2 := by ring
    rw [this, ← pow_mul]; exact hL6
  · intro h
    have hsq1 : (16 * l) ^ 2 = 1 := by linear_combination h
    have hL1 : 16 * l = 2 := by linear_combination hsq1 - hL2
    exact h3 (by linear_combination hL2 - (16 * l + 1) * hL1)
  · intro h
    have h4 : (16 * l) ^ 4 = 1 := by linear_combination h
    have hm1 : 16 * l = -1 := by linear_combination -h4 + (16 * l) * hL3
    exact h3 (by linear_combination hL2 - (16 * l - 2) * hm1)
  · intro h
    have hone : 16 * l = 1 := by linear_combination -h
    exact one_ne_zero (by linear_combination hL2 - (16 * l) * hone : (1 : κ) = 0)
  · linear_combination -hL2
  · intro h
    have hhalf : 2 * (16 * l) = 1 := mul_left_cancel₀ h16' (by linear_combination h)
    have hL' : 4 * (16 * l) ^ 2 = 4 * (16 * l) - 4 := by linear_combination 4 * hL2
    exact h3 (by linear_combination hL' - (2 * (16 * l) - 1) * hhalf : (3 : κ) = 0)

end Case0

section Case0R
variable {R κ : Type*} [CommRing R] [Field κ]

theorem constants_case0 (p : ℕ) [Fact p.Prime] [CharP κ p] (hp5 : 5 ≤ p) (red : R →+* κ)
    (ϖ : R) (hker : ∀ c, red c = 0 ↔ ∃ d, c = ϖ * d) (hunit : ∀ c, red c ≠ 0 → IsUnit c)
    (hpϖ : red (p : R) = 0) (y : R) (hPy : red (256 * y ^ 2 - 16 * y + 1) = 0) :
    ∃ (y' v vq : R),
      y' - y ∈ Ideal.span {ϖ} ∧ (16 - 256 * y') * v = 1 ∧ (16 - 256 * y' ^ p) * vq = 1 ∧
      red (256 * y' ^ 2) ^ 3 = 1 ∧ red (256 * y' ^ 2) ≠ 1 ∧ red (256 * y' ^ 2) ^ 2 ≠ 1 ∧
      256 * v ^ 2 - 256 * y' ^ 2 ∈ Ideal.span {ϖ} ∧ 256 * vq ^ 2 - (256 * y' ^ 2) ^ p ∈ Ideal.span {ϖ} ∧
      v - vq ^ p - 256 * y' ^ 2 * (y' - (y' ^ p) ^ p) ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} ∧
      vq - v ^ p ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  set l := red y with hl
  have hl0 : 256 * l ^ 2 - 16 * l + 1 = 0 := by
    have := hPy; simpa [map_ofNat] using this
  obtain ⟨hlp2, hζ3, hζ1, hζ2, h1l, hprod, hP'⟩ := root_facts p hp5 l hl0
  set I₁ : Ideal R := Ideal.span {ϖ} with hI₁
  set J : Ideal R := Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} with hJ
  have memI₁ : ∀ c : R, c ∈ I₁ ↔ red c = 0 := fun c => by
    rw [hker, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
  have hredϖ : red ϖ = 0 := (memI₁ ϖ).1 (Ideal.mem_span_singleton_self ϖ)
  have hJI : J ≤ I₁ := by
    refine sup_le ?_ ?_
    · rw [Ideal.span_singleton_le_iff_mem, memI₁, map_pow, hredϖ]; simp
    · rw [Ideal.span_singleton_le_iff_mem, memI₁]; exact hpϖ
  have hpJ : ∀ s : R, (p : R) * s ∈ J := fun s =>
    Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hspJ : Ideal.span {(p : R)} ≤ J := le_sup_right
  have hI₁sqJ : ∀ c : R, c ∈ I₁ → c ^ 2 ∈ J := fun c hc => by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    refine Ideal.mem_sup_left ?_
    rw [mul_pow]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have h16κ : ((16 : ℕ) : κ) ^ p = (16 : ℕ) := by rw [← frobenius_def, map_natCast]
  have h256κ : ((256 : ℕ) : κ) ^ p = (256 : ℕ) := by rw [← frobenius_def, map_natCast]
  push_cast at h16κ h256κ
  have hfrobD : ((16 : κ) - 256 * l) ^ p = 16 - 256 * l ^ p := by
    rw [sub_pow_char, mul_pow, h16κ, h256κ]

  have hlinv : (16 - 256 * l) * l = 1 := by linear_combination hprod
  have hlpinv : (16 - 256 * l ^ p) * l ^ p = 1 := by
    rw [← hfrobD, ← mul_pow, hlinv, one_pow]

  obtain ⟨u, hu⟩ := (hunit (512 * y - 16) (by simpa [← hl, map_ofNat] using hP')).exists_left_inv
  set h := (256 * y ^ 2 - 16 * y + 1) * u with hh
  set y' := y - h with hy'
  have hPy' : 256 * y' ^ 2 - 16 * y' + 1 = 256 * h ^ 2 := by
    rw [hy', hh]; exact newton_step y u hu
  have hhI : h ∈ I₁ := by rw [memI₁, hh, map_mul, hPy, zero_mul]
  have hy'y : y' - y ∈ I₁ := by
    have : y' - y = -h := by rw [hy']; ring
    rw [this]; exact I₁.neg_mem hhI
  have hredy' : red y' = l := by
    have : red (y' - y) = 0 := (memI₁ _).1 hy'y
    rw [map_sub, sub_eq_zero] at this; rw [this]
  have hPy'J : 256 * y' ^ 2 - 16 * y' + 1 ∈ J := by
    rw [hPy']; exact Ideal.mul_mem_left _ _ (hI₁sqJ h hhI)

  have hred16 : red (16 - 256 * y') = 16 - 256 * l := by simp [hredy', map_ofNat]
  have hne16 : (16 : κ) - 256 * l ≠ 0 := fun h0 => by
    have := hlinv; rw [h0, zero_mul] at this; exact zero_ne_one this
  obtain ⟨v, hv⟩ := (hunit _ (by rw [hred16]; exact hne16)).exists_right_inv
  have hred16q : red (16 - 256 * y' ^ p) = 16 - 256 * l ^ p := by simp [hredy', map_ofNat]
  have hne16q : (16 : κ) - 256 * l ^ p ≠ 0 := fun h0 => by
    have := hlpinv; rw [h0, zero_mul] at this; exact zero_ne_one this
  obtain ⟨vq, hvq⟩ := (hunit _ (by rw [hred16q]; exact hne16q)).exists_right_inv

  have hrv : red v = l := by
    have e : (16 - 256 * l) * red v = 1 := by
      have := congrArg red hv; simpa [hredy', map_ofNat] using this
    calc red v = ((16 - 256 * l) * l) * red v := by rw [hlinv, one_mul]
      _ = l * ((16 - 256 * l) * red v) := by ring
      _ = l := by rw [e, mul_one]
  have hrvq : red vq = l ^ p := by
    have e : (16 - 256 * l ^ p) * red vq = 1 := by
      have := congrArg red hvq; simpa [hredy', map_ofNat] using this
    calc red vq = ((16 - 256 * l ^ p) * l ^ p) * red vq := by rw [hlpinv, one_mul]
      _ = l ^ p * ((16 - 256 * l ^ p) * red vq) := by ring
      _ = l ^ p := by rw [e, mul_one]

  have hv1 : v - y' ∈ J := by
    rw [phi_sub_self y' v hv]; exact Ideal.mul_mem_right _ _ hPy'J
  have hPyp : 256 * (y' ^ p) ^ 2 - 16 * y' ^ p + 1 ∈ J := by
    have h1 := P_pow_sub_mem (R := R) p hp hp2 y'
    have h2 : (256 * y' ^ 2 - 16 * y' + 1) ^ p ∈ J := Ideal.pow_mem_of_mem J hPy'J p hp.one_lt.le
    have := J.add_mem (hspJ h1) h2
    simpa using this
  have hvq1 : vq - y' ^ p ∈ J := by
    rw [phi_sub_self (y' ^ p) vq hvq]; exact Ideal.mul_mem_right _ _ hPyp

  have hPypp : 256 * ((y' ^ p) ^ p) ^ 2 - 16 * (y' ^ p) ^ p + 1 ∈ J := by
    have h1 := P_pow_sub_mem (R := R) p hp hp2 (y' ^ p)
    have h2 : (256 * (y' ^ p) ^ 2 - 16 * y' ^ p + 1) ^ p ∈ J := Ideal.pow_mem_of_mem J hPyp p hp.one_lt.le
    have := J.add_mem (hspJ h1) h2
    simpa using this
  have hdiffI : (y' ^ p) ^ p - y' ∈ I₁ := by
    rw [memI₁, map_sub, map_pow, map_pow, hredy', ← pow_mul, ← pow_two, hlp2, sub_self]
  obtain ⟨w, hw⟩ := (hunit (512 * y' - 16 + 256 * ((y' ^ p) ^ p - y')) (by
    have h0 : red ((y' ^ p) ^ p - y') = 0 := (memI₁ _).1 hdiffI
    simp only [map_add, map_sub, map_mul, map_ofNat, hredy', h0, mul_zero, add_zero]
    exact hP')).exists_left_inv
  have hfix : (y' ^ p) ^ p - y' ∈ J :=
    approx_root_unique J I₁ hJI y' ((y' ^ p) ^ p) w hdiffI hPy'J hPypp hw
  refine ⟨y', v, vq, hy'y, hv, hvq, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : red (256 * y' ^ 2) = 256 * l ^ 2 := by simp [hredy', map_ofNat]
    rw [this]; exact hζ3
  · have : red (256 * y' ^ 2) = 256 * l ^ 2 := by simp [hredy', map_ofNat]
    rw [this]; exact hζ1
  · have : red (256 * y' ^ 2) = 256 * l ^ 2 := by simp [hredy', map_ofNat]
    rw [this]; exact hζ2
  · rw [memI₁]; simp [hrv, hredy', map_ofNat]
  · rw [memI₁]; simp only [map_sub, map_mul, map_pow, map_ofNat, hrvq, hredy']
    have : ((256 : κ) * l ^ 2) ^ p = 256 * (l ^ p) ^ 2 := by
      rw [mul_pow, h256κ, ← pow_mul, ← pow_mul, mul_comm 2 p]
    rw [this, sub_self]
  ·
    have e : v - vq ^ p - 256 * y' ^ 2 * (y' - (y' ^ p) ^ p)
        = (v - y') - (vq ^ p - (y' ^ p) ^ p) - (1 - 256 * y' ^ 2) * ((y' ^ p) ^ p - y') := by ring
    rw [e]
    refine J.sub_mem (J.sub_mem hv1 ?_) (J.mul_mem_left _ hfix)
    have : vq = y' ^ p + (vq - y' ^ p) := by ring
    rw [this]
    exact add_pow_sub_pow_mem p hp _ _ J hpJ (by rw [pow_two]; exact J.mul_mem_left _ hvq1)
  ·
    have e : vq - v ^ p = (vq - y' ^ p) - (v ^ p - y' ^ p) := by ring
    rw [e]
    refine J.sub_mem hvq1 ?_
    have : v = y' + (v - y') := by ring
    rw [this]
    exact add_pow_sub_pow_mem p hp _ _ J hpJ (by rw [pow_two]; exact J.mul_mem_left _ hv1)

end Case0R

section Case1728
variable {R κ : Type*} [CommRing R] [Field κ]

theorem frac_pow_prime_sub_mem (p : ℕ) (hp : p.Prime) (n d : ℕ) (w : R) (hw : w * (d : R) = 1) :
    ((n : R) * w) ^ p - (n : R) * w ∈ Ideal.span {((p : ℕ) : R)} := by
  set I : Ideal R := Ideal.span {((p : ℕ) : R)}
  have hn := natCast_pow_prime_sub_mem (R := R) p hp n
  have hd := natCast_pow_prime_sub_mem (R := R) p hp d
  have hwp : w ^ p - w = -(w ^ (p + 1) * ((d : R) ^ p - d)) := by
    have h1 : w ^ p * (d : R) ^ p = 1 := by rw [← mul_pow, hw, one_pow]
    have : w ^ (p + 1) * ((d : R) ^ p - d) = w * (w ^ p * (d : R) ^ p) - w ^ p * (w * d) := by ring
    rw [this, h1, hw]; ring
  have : ((n : R) * w) ^ p - (n : R) * w = ((n : R) ^ p - n) * w ^ p + (n : R) * (w ^ p - w) := by ring
  rw [this, hwp]
  exact I.add_mem (I.mul_mem_right _ hn) (I.mul_mem_left _ (I.neg_mem (I.mul_mem_left _ hd)))

theorem constants_fixed (p : ℕ) (hp : p.Prime) (red : R →+* κ)
    (ϖ : R) (hker : ∀ c, red c = 0 ↔ ∃ d, c = ϖ * d) (hunit : ∀ c, red c ≠ 0 → IsUnit c)
    (hpϖ : red (p : R) = 0)
    (α β γ δ r₀ : R) (hfix : α * r₀ + β = r₀ * (γ * r₀ + δ)) (hdet : α * δ - β * γ = -(γ * r₀ + δ) ^ 2)
    (hD : red (γ * r₀ + δ) ≠ 0) (hr₀p : r₀ ^ p - r₀ ∈ Ideal.span {(p : R)}) :
    ∃ v vq : R, (γ * r₀ + δ) * v = 1 ∧ (γ * r₀ ^ p + δ) * vq = 1 ∧
      (α * r₀ + β) * v = r₀ ∧ (α * δ - β * γ) * v ^ 2 = -1 ∧
      (α * δ - β * γ) * vq ^ 2 - (-1) ∈ Ideal.span {ϖ} ∧
      (α * r₀ + β) * v - ((α * r₀ ^ p + β) * vq) ^ p - (-1) * (r₀ - (r₀ ^ p) ^ p)
        ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} ∧
      (α * r₀ ^ p + β) * vq - ((α * r₀ + β) * v) ^ p - (-1) * (r₀ ^ p - r₀ ^ p)
        ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} := by
  set I₁ : Ideal R := Ideal.span {ϖ} with hI₁
  set Ip : Ideal R := Ideal.span {(p : R)} with hIp
  set J : Ideal R := Ideal.span {ϖ ^ 2} ⊔ Ideal.span {(p : R)} with hJ
  have memI₁ : ∀ c : R, c ∈ I₁ ↔ red c = 0 := fun c => by
    rw [hker, Ideal.mem_span_singleton]
    constructor
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
    · rintro ⟨d, rfl⟩; exact ⟨d, rfl⟩
  have hIpI : Ip ≤ I₁ := by rw [Ideal.span_singleton_le_iff_mem, memI₁]; exact hpϖ
  have hpJ : ∀ s : R, (p : R) * s ∈ J := fun s =>
    Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hpIp : ∀ s : R, (p : R) * s ∈ Ip := fun s => Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  have hIpJ : Ip ≤ J := le_sup_right

  have hredp : red (r₀ ^ p) = red r₀ := by
    have : red (r₀ ^ p - r₀) = 0 := (memI₁ _).1 (hIpI hr₀p)
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨v, hv⟩ := (hunit _ hD).exists_right_inv
  have hDq : red (γ * r₀ ^ p + δ) ≠ 0 := by
    have : red (γ * r₀ ^ p + δ) = red (γ * r₀ + δ) := by simp [hredp]
    rw [this]; exact hD
  obtain ⟨vq, hvq⟩ := (hunit _ hDq).exists_right_inv
  have hφ : (α * r₀ + β) * v = r₀ := by
    rw [hfix, mul_assoc, hv, mul_one]
  have hc₁ : (α * δ - β * γ) * v ^ 2 = -1 := by
    rw [hdet]; have : -(γ * r₀ + δ) ^ 2 * v ^ 2 = -(((γ * r₀ + δ) * v) ^ 2) := by ring
    rw [this, hv, one_pow]

  have hQ : α * r₀ ^ p + β - r₀ ^ p * (γ * r₀ ^ p + δ) ∈ Ip := by
    have : α * r₀ ^ p + β - r₀ ^ p * (γ * r₀ ^ p + δ)
        = (α * r₀ + β - r₀ * (γ * r₀ + δ)) + (r₀ ^ p - r₀) * (α - δ - γ * (r₀ ^ p + r₀)) := by ring
    rw [this, hfix, sub_self, zero_add]
    exact Ip.mul_mem_right _ hr₀p
  have hCG : (α * r₀ ^ p + β) * vq - r₀ ^ p ∈ Ip := by
    have : (α * r₀ ^ p + β) * vq - r₀ ^ p = (α * r₀ ^ p + β - r₀ ^ p * (γ * r₀ ^ p + δ)) * vq := by
      have h := hvq
      linear_combination r₀ ^ p * h
    rw [this]; exact Ip.mul_mem_right _ hQ

  have hpp : (r₀ ^ p) ^ p - r₀ ∈ Ip := by
    have h1 : (r₀ + (r₀ ^ p - r₀)) ^ p - r₀ ^ p ∈ Ip :=
      add_pow_sub_pow_mem p hp r₀ _ Ip hpIp (by rw [pow_two]; exact Ip.mul_mem_left _ hr₀p)
    have : (r₀ ^ p) ^ p - r₀ = ((r₀ + (r₀ ^ p - r₀)) ^ p - r₀ ^ p) + (r₀ ^ p - r₀) := by ring
    rw [this]; exact Ip.add_mem h1 hr₀p
  refine ⟨v, vq, hv, hvq, hφ, hc₁, ?_, ?_, ?_⟩
  · rw [memI₁]
    have hrv : red v * red (γ * r₀ + δ) = 1 := by
      have := congrArg red hv; rw [map_mul, map_one] at this; rw [mul_comm]; exact this
    have hrvq : red vq * red (γ * r₀ + δ) = 1 := by
      have := congrArg red hvq; rw [map_mul, map_one] at this
      have e : red (γ * r₀ ^ p + δ) = red (γ * r₀ + δ) := by simp [hredp]
      rw [e] at this; rw [mul_comm]; exact this
    have hvv : red vq = red v := by
      calc red vq = red vq * (red (γ * r₀ + δ) * red v) := by rw [mul_comm (red _) (red v), hrv, mul_one]
        _ = (red vq * red (γ * r₀ + δ)) * red v := by ring
        _ = red v := by rw [hrvq, one_mul]
    have := congrArg red hc₁
    simp only [map_sub, map_mul, map_pow, map_neg, map_one] at this ⊢
    rw [hvv, this]; ring
  ·
    have e : (α * r₀ + β) * v - ((α * r₀ ^ p + β) * vq) ^ p - (-1) * (r₀ - (r₀ ^ p) ^ p)
        = -(((α * r₀ ^ p + β) * vq) ^ p - (r₀ ^ p) ^ p) - 2 * ((r₀ ^ p) ^ p - r₀) := by rw [hφ]; ring
    rw [e]
    refine J.sub_mem (J.neg_mem ?_) (J.mul_mem_left _ (hIpJ hpp))
    have : (α * r₀ ^ p + β) * vq = r₀ ^ p + ((α * r₀ ^ p + β) * vq - r₀ ^ p) := by ring
    rw [this]
    exact add_pow_sub_pow_mem p hp _ _ J hpJ (by rw [pow_two]; exact J.mul_mem_left _ (hIpJ hCG))
  ·
    have e : (α * r₀ ^ p + β) * vq - ((α * r₀ + β) * v) ^ p - (-1) * (r₀ ^ p - r₀ ^ p)
        = (α * r₀ ^ p + β) * vq - r₀ ^ p := by rw [hφ]; ring
    rw [e]; exact hIpJ hCG

end Case1728

end S14STAB

namespace S14STAB

open Ideal

variable {S : Type*} [CommRing S]

theorem tangency_core (p : ℕ) (hp : p.Prime) (g : S →+* S) (J n : Ideal S)
    (hn2 : n ^ 2 ≤ J) (hq : ∀ s : S, (p : S) * s ∈ J)
    (μ μq y yq m₁ m₂ φy φyq c₁ c₂ ζ₀ ζ₀' r₁ r₂ : S)
    (hμ : μ = y + m₁) (hμq : μq = yq + m₂) (hm₁ : m₁ ∈ n) (hm₂ : m₂ ∈ n)
    (hgμ : g μ = φy + c₁ * m₁ + m₁ ^ 2 * r₁) (hgμq : g μq = φyq + c₂ * m₂ + m₂ ^ 2 * r₂)
    (hc₁ : c₁ - ζ₀ ∈ n) (hc₂ : c₂ - ζ₀' ∈ n)
    (hCH : φy - φyq ^ p - ζ₀ * (y - yq ^ p) ∈ J)
    (hCG : φyq - φy ^ p - ζ₀' * (yq - y ^ p) ∈ J) :
    g (μ - μq ^ p) - ζ₀ * (μ - μq ^ p) ∈ J ∧ g (μq - μ ^ p) - ζ₀' * (μq - μ ^ p) ∈ J := by
  have hn2' : ∀ a b : S, a ∈ n → b ∈ n → a * b ∈ J := fun a b ha hb =>
    hn2 (by rw [pow_two]; exact Ideal.mul_mem_mul ha hb)

  have e1 : g μ - ζ₀ * μ - (φy - ζ₀ * y) ∈ J := by
    have : g μ - ζ₀ * μ - (φy - ζ₀ * y) = (c₁ - ζ₀) * m₁ + m₁ * m₁ * r₁ := by
      rw [hgμ, hμ]; ring
    rw [this]
    exact J.add_mem (hn2' _ _ hc₁ hm₁) (J.mul_mem_right _ (hn2' _ _ hm₁ hm₁))
  have e2 : g μq - ζ₀' * μq - (φyq - ζ₀' * yq) ∈ J := by
    have : g μq - ζ₀' * μq - (φyq - ζ₀' * yq) = (c₂ - ζ₀') * m₂ + m₂ * m₂ * r₂ := by
      rw [hgμq, hμq]; ring
    rw [this]
    exact J.add_mem (hn2' _ _ hc₂ hm₂) (J.mul_mem_right _ (hn2' _ _ hm₂ hm₂))

  have hsq : ∀ d : S, d ∈ n → d ^ 2 ∈ J := fun d hd => hn2 (Ideal.pow_mem_pow hd 2)
  have p1 : (g μq) ^ p - φyq ^ p ∈ J := by
    have : g μq = φyq + (c₂ * m₂ + m₂ ^ 2 * r₂) := by rw [hgμq]; ring
    rw [this]
    refine add_pow_sub_pow_mem p hp _ _ J hq (hsq _ ?_)
    exact n.add_mem (n.mul_mem_left _ hm₂) (by rw [pow_two, mul_assoc]; exact n.mul_mem_right _ hm₂)
  have p2 : μq ^ p - yq ^ p ∈ J := by rw [hμq]; exact add_pow_sub_pow_mem p hp _ _ J hq (hsq _ hm₂)
  have p3 : (g μ) ^ p - φy ^ p ∈ J := by
    have : g μ = φy + (c₁ * m₁ + m₁ ^ 2 * r₁) := by rw [hgμ]; ring
    rw [this]
    refine add_pow_sub_pow_mem p hp _ _ J hq (hsq _ ?_)
    exact n.add_mem (n.mul_mem_left _ hm₁) (by rw [pow_two, mul_assoc]; exact n.mul_mem_right _ hm₁)
  have p4 : μ ^ p - y ^ p ∈ J := by rw [hμ]; exact add_pow_sub_pow_mem p hp _ _ J hq (hsq _ hm₁)
  constructor
  ·
    have : g (μ - μq ^ p) - ζ₀ * (μ - μq ^ p)
        = (g μ - ζ₀ * μ - (φy - ζ₀ * y)) - ((g μq) ^ p - φyq ^ p) + ζ₀ * (μq ^ p - yq ^ p)
          + (φy - φyq ^ p - ζ₀ * (y - yq ^ p)) := by
      rw [map_sub, map_pow]; ring
    rw [this]
    exact J.add_mem (J.add_mem (J.sub_mem e1 p1) (J.mul_mem_left _ p2)) hCH
  ·
    have : g (μq - μ ^ p) - ζ₀' * (μq - μ ^ p)
        = (g μq - ζ₀' * μq - (φyq - ζ₀' * yq)) - ((g μ) ^ p - φy ^ p) + ζ₀' * (μ ^ p - y ^ p)
          + (φyq - φy ^ p - ζ₀' * (yq - y ^ p)) := by
      rw [map_sub, map_pow]; ring
    rw [this]
    exact J.add_mem (J.add_mem (J.sub_mem e2 p3) (J.mul_mem_left _ p4)) hCG

end S14STAB

namespace S14STAB

open MvPolynomial

section Twist
variable {A₀ L₀ κ : Type*} [CommRing A₀] [CommRing L₀] [Field κ]
variable (cst : A₀ →+* L₀) (red : A₀ →+* κ) (μ μq Tμ Tμq : L₀) (l lq : κ) (α β γ δ : A₀)

noncomputable def ev : MvPolynomial (Fin 2) A₀ →+* L₀ := eval₂Hom cst ![μ, μq]
noncomputable def tw : MvPolynomial (Fin 2) A₀ →+* L₀ := eval₂Hom cst ![Tμ, Tμq]
noncomputable def pev : MvPolynomial (Fin 2) A₀ →+* κ := eval₂Hom red ![l, lq]

noncomputable def DD (g d : A₀) : MvPolynomial (Fin 2) A₀ := (C g * X 0 + C d) * (C g * X 1 + C d)

variable {cst red μ μq Tμ Tμq l lq α β γ δ}

theorem exists_twist (hT : Tμ * (cst γ * μ + cst δ) = cst α * μ + cst β)
    (hTq : Tμq * (cst γ * μq + cst δ) = cst α * μq + cst β)
    (hl : red α * l + red β = l * (red γ * l + red δ))
    (hlq : red α * lq + red β = lq * (red γ * lq + red δ))
    (r : MvPolynomial (Fin 2) A₀) :
    ∃ (N : ℕ) (r' : MvPolynomial (Fin 2) A₀),
      tw cst Tμ Tμq r * (ev cst μ μq (DD γ δ)) ^ N = ev cst μ μq r' ∧
      pev red l lq r' = pev red l lq r * (pev red l lq (DD γ δ)) ^ N := by
  classical

  have evC : ∀ c, ev cst μ μq (C c) = cst c := fun c => eval₂Hom_C _ _ _
  have twC : ∀ c, tw cst Tμ Tμq (C c) = cst c := fun c => eval₂Hom_C _ _ _
  have peC : ∀ c, pev red l lq (C c) = red c := fun c => eval₂Hom_C _ _ _
  have evX0 : ev cst μ μq (X 0) = μ := by simp [ev]
  have evX1 : ev cst μ μq (X 1) = μq := by simp [ev]
  have twX0 : tw cst Tμ Tμq (X 0) = Tμ := by simp [tw]
  have twX1 : tw cst Tμ Tμq (X 1) = Tμq := by simp [tw]
  have peX0 : pev red l lq (X 0) = l := by simp [pev]
  have peX1 : pev red l lq (X 1) = lq := by simp [pev]
  have evDD : ev cst μ μq (DD γ δ) = (cst γ * μ + cst δ) * (cst γ * μq + cst δ) := by
    simp [DD, map_mul, map_add, evC, evX0, evX1]
  have peDD : pev red l lq (DD γ δ) = (red γ * l + red δ) * (red γ * lq + red δ) := by
    simp [DD, map_mul, map_add, peC, peX0, peX1]
  induction r using MvPolynomial.induction_on with
  | C c =>
    exact ⟨0, C c, by simp [twC, evC], by simp⟩
  | add r₁ r₂ h₁ h₂ =>
    obtain ⟨N₁, s₁, hs₁, hp₁⟩ := h₁
    obtain ⟨N₂, s₂, hs₂, hp₂⟩ := h₂
    refine ⟨N₁ + N₂, s₁ * DD γ δ ^ N₂ + s₂ * DD γ δ ^ N₁, ?_, ?_⟩
    · rw [map_add, map_add, map_mul, map_mul, map_pow, map_pow, ← hs₁, ← hs₂]; ring
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hp₁, hp₂, map_add]; ring
  | mul_X r i h =>
    obtain ⟨N, s, hs, hps⟩ := h
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · refine ⟨N + 1, s * (C α * X 0 + C β) * (C γ * X 1 + C δ), ?_, ?_⟩
      · rw [map_mul, twX0, pow_succ, map_mul, map_mul, ← hs, evDD]
        simp only [map_add, map_mul, evC, evX0, evX1]
        linear_combination (tw cst Tμ Tμq r * ((cst γ * μ + cst δ) * (cst γ * μq + cst δ)) ^ N
          * (cst γ * μq + cst δ)) * hT
      · rw [map_mul, map_mul, hps, map_mul, peX0, pow_succ, peDD]
        simp only [map_add, map_mul, peC, peX0, peX1]
        linear_combination (pev red l lq r * ((red γ * l + red δ) * (red γ * lq + red δ)) ^ N
          * (red γ * lq + red δ)) * hl
    · refine ⟨N + 1, s * (C α * X 1 + C β) * (C γ * X 0 + C δ), ?_, ?_⟩
      · rw [map_mul, twX1, pow_succ, map_mul, map_mul, ← hs, evDD]
        simp only [map_add, map_mul, evC, evX0, evX1]
        linear_combination (tw cst Tμ Tμq r * ((cst γ * μ + cst δ) * (cst γ * μq + cst δ)) ^ N
          * (cst γ * μ + cst δ)) * hTq
      · rw [map_mul, map_mul, hps, map_mul, peX1, pow_succ, peDD]
        simp only [map_add, map_mul, peC, peX0, peX1]
        linear_combination (pev red l lq r * ((red γ * l + red δ) * (red γ * lq + red δ)) ^ N
          * (red γ * l + red δ)) * hlq

theorem mem_of_mul_tw_eq (S : Subring L₀)
    (hS : ∀ f : L₀, f ∈ S ↔ ∃ r s : MvPolynomial (Fin 2) A₀,
      pev red l lq s ≠ 0 ∧ f * ev cst μ μq s = ev cst μ μq r)
    (hT : Tμ * (cst γ * μ + cst δ) = cst α * μ + cst β)
    (hTq : Tμq * (cst γ * μq + cst δ) = cst α * μq + cst β)
    (hl : red α * l + red β = l * (red γ * l + red δ))
    (hlq : red α * lq + red β = lq * (red γ * lq + red δ))
    (hD : red γ * l + red δ ≠ 0) (hDq : red γ * lq + red δ ≠ 0)
    (f' : L₀) (r s : MvPolynomial (Fin 2) A₀) (hs : pev red l lq s ≠ 0)
    (h : f' * tw cst Tμ Tμq s = tw cst Tμ Tμq r) : f' ∈ S := by
  obtain ⟨N₁, r', hr', hpr'⟩ := exists_twist (cst := cst) (red := red) (μ := μ) (μq := μq) hT hTq hl hlq r
  obtain ⟨N₂, s', hs', hps'⟩ := exists_twist (cst := cst) (red := red) (μ := μ) (μq := μq) hT hTq hl hlq s
  rw [hS]
  refine ⟨r' * DD γ δ ^ N₂, s' * DD γ δ ^ N₁, ?_, ?_⟩
  · rw [map_mul, map_pow, hps']
    have peDD : pev red l lq (DD γ δ) = (red γ * l + red δ) * (red γ * lq + red δ) := by
      simp [DD, pev]
    rw [peDD]
    exact mul_ne_zero (mul_ne_zero hs (pow_ne_zero _ (mul_ne_zero hD hDq)))
      (pow_ne_zero _ (mul_ne_zero hD hDq))
  · rw [map_mul, map_pow, ← hs', map_mul, map_pow, ← hr']
    calc f' * (tw cst Tμ Tμq s * ev cst μ μq (DD γ δ) ^ N₂ * ev cst μ μq (DD γ δ) ^ N₁)
        = (f' * tw cst Tμ Tμq s) * ev cst μ μq (DD γ δ) ^ N₁ * ev cst μ μq (DD γ δ) ^ N₂ := by ring
      _ = tw cst Tμ Tμq r * ev cst μ μq (DD γ δ) ^ N₁ * ev cst μ μq (DD γ δ) ^ N₂ := by rw [h]

end Twist

end S14STAB

namespace S14STAB

section Restrict
variable {L₀ : Type*} [Field L₀] (S : Subring L₀) (F : Subfield L₀) (hSF : S ≤ F.toSubring)
  (σ : ↥F ≃+* ↥F) (hσS : ∀ (b : L₀) (hb : b ∈ S), ((σ ⟨b, hSF hb⟩ : ↥F) : L₀) ∈ S)

noncomputable def restrictHom : ↥S →+* ↥S where
  toFun f := ⟨((σ ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀), hσS _ f.2⟩
  map_one' := Subtype.ext (by
    change ((σ ⟨((1 : ↥S) : L₀), hSF (1 : ↥S).2⟩ : ↥F) : L₀) = 1
    rw [show (⟨((1 : ↥S) : L₀), hSF (1 : ↥S).2⟩ : ↥F) = 1 from Subtype.ext rfl, map_one]; rfl)
  map_mul' f g := Subtype.ext (by
    change ((σ ⟨((f * g : ↥S) : L₀), hSF (f * g).2⟩ : ↥F) : L₀)
      = ((σ ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀) * ((σ ⟨(g : L₀), hSF g.2⟩ : ↥F) : L₀)
    rw [show (⟨((f * g : ↥S) : L₀), hSF (f * g).2⟩ : ↥F) = ⟨f, hSF f.2⟩ * ⟨g, hSF g.2⟩ from Subtype.ext rfl,
      map_mul]; rfl)
  map_zero' := Subtype.ext (by
    change ((σ ⟨((0 : ↥S) : L₀), hSF (0 : ↥S).2⟩ : ↥F) : L₀) = 0
    rw [show (⟨((0 : ↥S) : L₀), hSF (0 : ↥S).2⟩ : ↥F) = 0 from Subtype.ext rfl, map_zero]; rfl)
  map_add' f g := Subtype.ext (by
    change ((σ ⟨((f + g : ↥S) : L₀), hSF (f + g).2⟩ : ↥F) : L₀)
      = ((σ ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀) + ((σ ⟨(g : L₀), hSF g.2⟩ : ↥F) : L₀)
    rw [show (⟨((f + g : ↥S) : L₀), hSF (f + g).2⟩ : ↥F) = ⟨f, hSF f.2⟩ + ⟨g, hSF g.2⟩ from Subtype.ext rfl,
      map_add]; rfl)

theorem coe_restrictHom (f : ↥S) :
    ((restrictHom S F hSF σ hσS f : ↥S) : L₀) = ((σ ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀) := rfl

theorem coe_restrictHom_iterate (n : ℕ) (f : ↥S) :
    (((restrictHom S F hSF σ hσS)^[n] f : ↥S) : L₀) = ((σ^[n] ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    congr 2

variable (hσ6 : ∀ x : ↥F, σ^[6] x = x)

noncomputable def restrictEquiv : ↥S ≃+* ↥S :=
  RingEquiv.ofRingHom (restrictHom S F hSF σ hσS)
    ((restrictHom S F hSF σ hσS).comp ((restrictHom S F hSF σ hσS).comp ((restrictHom S F hSF σ hσS).comp
      ((restrictHom S F hSF σ hσS).comp (restrictHom S F hSF σ hσS)))))
    (by
      ext f
      change ((((restrictHom S F hSF σ hσS)^[6]) f : ↥S) : L₀) = f
      rw [coe_restrictHom_iterate, hσ6])
    (by
      ext f
      change ((((restrictHom S F hSF σ hσS)^[6]) f : ↥S) : L₀) = f
      rw [coe_restrictHom_iterate, hσ6])

theorem coe_restrictEquiv (f : ↥S) :
    ((restrictEquiv S F hSF σ hσS hσ6 f : ↥S) : L₀) = ((σ ⟨(f : L₀), hSF f.2⟩ : ↥F) : L₀) := rfl

end Restrict

end S14STAB

namespace S14STAB

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized MvPolynomial

section Assembly

variable {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
  {k : Type*} [Field k] [CharP k q] [DecidableEq k]

local notation "L₀" => LaurentSeries (AlgebraicClosure ℚ)

theorem lambdaEval_eq_ev (A₀ : Subring (AlgebraicClosure ℚ)) :
    lambdaEval q A₀ = ev (CharPReduction.constSeries A₀) (lambdaModC (AlgebraicClosure ℚ)) (lambdaNModC (AlgebraicClosure ℚ) q) := rfl

theorem pointEval_eq_pev (A₀ : Subring (AlgebraicClosure ℚ)) (red₀ : A₀ →+* k) (l lq : k) :
    NodeLocalized.pointEval A₀ red₀ l lq = pev red₀ l lq := rfl

variable (red : A →+* k) (K : IntermediateField ℚ (AlgebraicClosure ℚ)) (l : k)

theorem constSeries_mem_lambdaFieldOver (c : ↥(coeffSubring A K)) :
    CharPReduction.constSeries (coeffSubring A K) c ∈ lambdaFieldOver q K := by
  refine Subfield.subset_closure (Or.inl ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩)

theorem lambdaEval_mem_lambdaFieldOver (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    lambdaEval q (coeffSubring A K) r ∈ lambdaFieldOver q K := by
  induction r using MvPolynomial.induction_on with
  | C c => rw [lambdaEval_eq_ev, ev, eval₂Hom_C]; exact constSeries_mem_lambdaFieldOver K c
  | add r₁ r₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
  | mul_X r i h =>
    rw [map_mul]
    refine mul_mem h ?_
    fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue]
    · rw [lambdaEval_eq_ev, ev]; simp [lambdaModC_mem_lambdaFieldOver]
    · rw [lambdaEval_eq_ev, ev]; simp [lambdaNModC_mem_lambdaFieldOver]

theorem lambdaLocalizedAtPoint_le_lambdaFieldOver (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l) :
    lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) ≤ (lambdaFieldOver q K).toSubring := by
  intro f hf
  obtain ⟨r, s, hs, hfs⟩ := hf
  have hs0 : lambdaEval q (coeffSubring A K) s ≠ 0 := fun h0 =>
    hs (pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K s h0)
  have : f = lambdaEval q (coeffSubring A K) r * (lambdaEval q (coeffSubring A K) s)⁻¹ := by
    rw [← hfs, mul_assoc, mul_inv_cancel₀ hs0, mul_one]
  rw [this]
  exact (lambdaFieldOver q K).mul_mem (lambdaEval_mem_lambdaFieldOver K r)
    ((lambdaFieldOver q K).inv_mem (lambdaEval_mem_lambdaFieldOver K s))

noncomputable def evF : MvPolynomial (Fin 2) ↥(coeffSubring A K) →+* ↥(lambdaFieldOver q K) :=
  (lambdaEval q (coeffSubring A K)).codRestrict (lambdaFieldOver q K).toSubring
    (fun r => lambdaEval_mem_lambdaFieldOver (q := q) K r)

theorem coe_evF (r : MvPolynomial (Fin 2) ↥(coeffSubring A K)) :
    ((evF (q := q) (A := A) K r : ↥(lambdaFieldOver q K)) : L₀) = lambdaEval q (coeffSubring A K) r := rfl

theorem sigma_mem (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : L₀) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (α β γ δ : ↥(coeffSubring A K)) (Tμ Tμq : L₀)
    (hσμ : ((σ ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : L₀) = Tμ)
    (hσμq : ((σ ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : L₀) = Tμq)
    (hT : Tμ * (CharPReduction.constSeries (coeffSubring A K) γ * lambdaModC (AlgebraicClosure ℚ)
      + CharPReduction.constSeries (coeffSubring A K) δ)
      = CharPReduction.constSeries (coeffSubring A K) α * lambdaModC (AlgebraicClosure ℚ)
        + CharPReduction.constSeries (coeffSubring A K) β)
    (hTq : Tμq * (CharPReduction.constSeries (coeffSubring A K) γ * lambdaNModC (AlgebraicClosure ℚ) q
      + CharPReduction.constSeries (coeffSubring A K) δ)
      = CharPReduction.constSeries (coeffSubring A K) α * lambdaNModC (AlgebraicClosure ℚ) q
        + CharPReduction.constSeries (coeffSubring A K) β)
    (hl : redRestrict red K α * l + redRestrict red K β = l * (redRestrict red K γ * l + redRestrict red K δ))
    (hlq : redRestrict red K α * l ^ q + redRestrict red K β = l ^ q * (redRestrict red K γ * l ^ q + redRestrict red K δ))
    (hD : redRestrict red K γ * l + redRestrict red K δ ≠ 0) (hDq : redRestrict red K γ * l ^ q + redRestrict red K δ ≠ 0)
    (f : L₀) (hf : f ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) :
    ((σ ⟨f, lambdaLocalizedAtPoint_le_lambdaFieldOver red K l hq2 hl2 hf⟩ : ↥(lambdaFieldOver q K)) : L₀)
      ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) := by
  have hle := lambdaLocalizedAtPoint_le_lambdaFieldOver red K l hq2 hl2 hf
  obtain ⟨r, s, hs, hfs⟩ := hf

  set cst := CharPReduction.constSeries (coeffSubring A K) with hcst
  have key : ((lambdaFieldOver q K).subtype.comp (σ.toRingHom.comp (evF (q := q) (A := A) K)))
      = tw cst Tμ Tμq := by
    refine MvPolynomial.ringHom_ext (fun c => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, tw, eval₂Hom_C]
      have hc : ((evF (q := q) (A := A) K (C c) : ↥(lambdaFieldOver q K)) : L₀) = cst c := by
        rw [coe_evF, lambdaEval_eq_ev, ev, eval₂Hom_C]
      have : σ (evF (q := q) (A := A) K (C c)) = evF (q := q) (A := A) K (C c) :=
        hσK _ (by rw [hc]; exact ⟨⟨(c : AlgebraicClosure ℚ), c.2.2⟩, rfl⟩)
      rw [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, this]
      exact hc
    · fin_cases i <;> simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, RingHom.coe_comp, Function.comp_apply,
        RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, tw]
      · have : evF (q := q) (A := A) K (X 0) = ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ :=
          Subtype.ext (by rw [coe_evF, lambdaEval_eq_ev, ev]; simp)
        rw [this]; simpa using hσμ
      · have : evF (q := q) (A := A) K (X 1) = ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ :=
          Subtype.ext (by rw [coe_evF, lambdaEval_eq_ev, ev]; simp)
        rw [this]; simpa using hσμq
  have keyr : ∀ r, ((σ (evF (q := q) (A := A) K r) : ↥(lambdaFieldOver q K)) : L₀) = tw cst Tμ Tμq r := fun r => by
    have := congrArg (fun φ => φ r) key; simpa using this

  have eF : (⟨f, hle⟩ : ↥(lambdaFieldOver q K)) * evF (q := q) (A := A) K s = evF (q := q) (A := A) K r :=
    Subtype.ext (by simp only [Subfield.coe_mul, coe_evF]; exact hfs)
  have eσ := congrArg (fun x : ↥(lambdaFieldOver q K) => (x : L₀)) (congrArg σ eF)
  simp only [map_mul, Subfield.coe_mul, keyr] at eσ
  refine mem_of_mul_tw_eq (cst := cst) (red := redRestrict red K) (μ := lambdaModC (AlgebraicClosure ℚ))
    (μq := lambdaNModC (AlgebraicClosure ℚ) q) (α := α) (β := β) (γ := γ) (δ := δ)
    (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
    (fun f' => Iff.rfl) hT hTq hl hlq hD hDq _ r s hs eσ

theorem stab_of_data (hq2 : q ≠ 2) (hl2 : l ^ (q ^ 2) = l)
    (ϖ : ↥(coeffSubring A K)) (y : ↥(coeffSubring A K))
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : L₀) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ6 : ∀ x : ↥(lambdaFieldOver q K), σ^[6] x = x)
    (α β γ δ : ↥(coeffSubring A K)) (Tμ Tμq : L₀)
    (hσμ : ((σ ⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : L₀) = Tμ)
    (hσμq : ((σ ⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : L₀) = Tμq)
    (hTμ' : Tμ = (CharPReduction.constSeries (coeffSubring A K) α * lambdaModC (AlgebraicClosure ℚ)
        + CharPReduction.constSeries (coeffSubring A K) β)
        * (CharPReduction.constSeries (coeffSubring A K) γ * lambdaModC (AlgebraicClosure ℚ)
          + CharPReduction.constSeries (coeffSubring A K) δ)⁻¹)
    (hTμq' : Tμq = (CharPReduction.constSeries (coeffSubring A K) α * lambdaNModC (AlgebraicClosure ℚ) q
        + CharPReduction.constSeries (coeffSubring A K) β)
        * (CharPReduction.constSeries (coeffSubring A K) γ * lambdaNModC (AlgebraicClosure ℚ) q
          + CharPReduction.constSeries (coeffSubring A K) δ)⁻¹)
    (hl : redRestrict red K α * l + redRestrict red K β = l * (redRestrict red K γ * l + redRestrict red K δ))
    (hlq : redRestrict red K α * l ^ q + redRestrict red K β = l ^ q * (redRestrict red K γ * l ^ q + redRestrict red K δ))
    (hD : redRestrict red K γ * l + redRestrict red K δ ≠ 0) (hDq : redRestrict red K γ * l ^ q + redRestrict red K δ ≠ 0)
    (ζ₀ ζ₀' y' v vq : ↥(coeffSubring A K)) (hy'y : y' - y ∈ Ideal.span {ϖ})
    (hv : (γ * y' + δ) * v = 1) (hvq : (γ * y' ^ q + δ) * vq = 1)
    (hc₁ : (α * δ - β * γ) * v ^ 2 - ζ₀ ∈ Ideal.span {ϖ})
    (hc₂ : (α * δ - β * γ) * vq ^ 2 - ζ₀' ∈ Ideal.span {ϖ})
    (hCH : (α * y' + β) * v - ((α * y' ^ q + β) * vq) ^ q - ζ₀ * (y' - (y' ^ q) ^ q)
      ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))})
    (hCG : (α * y' ^ q + β) * vq - ((α * y' + β) * v) ^ q - ζ₀' * (y' ^ q - y' ^ q)
      ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))}) :
    ∃ (hSF : (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ (lambdaFieldOver q K).toSubring)
      (hσS : ∀ (b : L₀) (hb : b ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((σ ⟨b, hSF hb⟩ : ↥(lambdaFieldOver q K)) : L₀) ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
      (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
      (∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((g z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) : L₀) =
          ((σ ⟨(z : L₀), hSF z.2⟩ : ↥(lambdaFieldOver q K)) : L₀)) ∧
      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ∧
      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} := by
  classical
  have hp : q.Prime := Fact.out
  set Sr := lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) with hSr
  set cst := CharPReduction.constSeries (coeffSubring A K) with hcst
  have evC : ∀ c, lambdaEval q (coeffSubring A K) (C c) = cst c := fun c => eval₂Hom_C _ _ _
  have evX0 : lambdaEval q (coeffSubring A K) (X 0) = lambdaModC (AlgebraicClosure ℚ) := by
    rw [lambdaEval_eq_ev, ev]; simp
  have evX1 : lambdaEval q (coeffSubring A K) (X 1) = lambdaNModC (AlgebraicClosure ℚ) q := by
    rw [lambdaEval_eq_ev, ev]; simp

  have hD0 : cst γ * lambdaModC (AlgebraicClosure ℚ) + cst δ ≠ 0 := by
    intro h0
    have : lambdaEval q (coeffSubring A K) (C γ * X 0 + C δ) = 0 := by
      simp [map_add, map_mul, evC, evX0, h0]
    have := pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K _ this
    simp [pointEval_eq_pev, pev] at this
    exact hD this
  have hDq0 : cst γ * lambdaNModC (AlgebraicClosure ℚ) q + cst δ ≠ 0 := by
    intro h0
    have : lambdaEval q (coeffSubring A K) (C γ * X 1 + C δ) = 0 := by
      simp [map_add, map_mul, evC, evX1, h0]
    have := pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two hq2 red l hl2 K _ this
    simp [pointEval_eq_pev, pev] at this
    exact hDq this
  have hT : Tμ * (cst γ * lambdaModC (AlgebraicClosure ℚ) + cst δ)
      = cst α * lambdaModC (AlgebraicClosure ℚ) + cst β := by
    rw [hTμ', inv_mul_cancel_right₀ hD0]
  have hTq : Tμq * (cst γ * lambdaNModC (AlgebraicClosure ℚ) q + cst δ)
      = cst α * lambdaNModC (AlgebraicClosure ℚ) q + cst β := by
    rw [hTμq', inv_mul_cancel_right₀ hDq0]

  have hSF : Sr ≤ (lambdaFieldOver q K).toSubring := lambdaLocalizedAtPoint_le_lambdaFieldOver red K l hq2 hl2 (A := A)
  have hσS : ∀ (b : L₀) (hb : b ∈ Sr), ((σ ⟨b, hSF hb⟩ : ↥(lambdaFieldOver q K)) : L₀) ∈ Sr :=
    fun b hb => sigma_mem red K l hq2 hl2 σ hσK α β γ δ Tμ Tμq hσμ hσμq hT hTq hl hlq hD hDq b hb
  set g := restrictEquiv Sr (lambdaFieldOver q K) hSF σ hσS hσ6 with hg
  refine ⟨hSF, hσS, g, fun z => rfl, ?_⟩
  have memEv : ∀ r, lambdaEval q (coeffSubring A K) r ∈ Sr := fun r =>
    lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) r
  have memC : ∀ c, cst c ∈ Sr := fun c => by rw [← evC]; exact memEv (C c)
  let cS : ↥(coeffSubring A K) →+* ↥Sr := cst.codRestrict Sr memC
  have coe_cS : ∀ c, ((cS c : ↥Sr) : L₀) = cst c := fun c => rfl
  let μS : ↥Sr := ⟨lambdaModC (AlgebraicClosure ℚ), by rw [← evX0]; exact memEv (X 0)⟩
  let μqS : ↥Sr := ⟨lambdaNModC (AlgebraicClosure ℚ) q, by rw [← evX1]; exact memEv (X 1)⟩

  have eH : (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = μS - μqS ^ q :=
    Subtype.ext (by simp [map_sub, map_pow, evX0, evX1, μS, μqS])
  have eG : (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = μqS - μS ^ q :=
    Subtype.ext (by simp [map_sub, map_pow, evX0, evX1, μS, μqS])
  have eCc : ∀ c, (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C c),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = cS c := fun c => Subtype.ext (by rw [coe_cS]; exact evC c)
  have em1 : (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = μS - cS y :=
    Subtype.ext (by simp [map_sub, evX0, evC, μS, coe_cS])
  have em2 : (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) = μqS - cS (y ^ q) :=
    Subtype.ext (by simp [map_sub, evX1, evC, μqS, coe_cS])
  rw [eH, eG, eCc, eCc, eCc, em1, em2]
  set n : Ideal ↥Sr := Ideal.span {cS ϖ, μS - cS y, μqS - cS (y ^ q)} with hn
  set J : Ideal ↥Sr := n ^ 2 ⊔ Ideal.span {((q : ℕ) : ↥Sr)} with hJ
  have hn2 : n ^ 2 ≤ J := le_sup_left
  have hqJ : ∀ s : ↥Sr, ((q : ℕ) : ↥Sr) * s ∈ J := fun s =>
    Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  have hϖn : cS ϖ ∈ n := Ideal.subset_span (by simp)
  have hm1n : μS - cS y ∈ n := Ideal.subset_span (by simp)
  have hm2n : μqS - cS (y ^ q) ∈ n := Ideal.subset_span (by simp)

  have mapI₁ : ∀ c : ↥(coeffSubring A K), c ∈ Ideal.span {ϖ} → cS c ∈ n := fun c hc => by
    obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hc
    rw [map_mul]; exact n.mul_mem_left _ hϖn
  have mapJ : ∀ c : ↥(coeffSubring A K),
      c ∈ Ideal.span {ϖ ^ 2} ⊔ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))} → cS c ∈ J := fun c hc => by
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.1 hc
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 ha'
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hb'
    rw [map_add, map_mul, map_mul, map_pow, map_natCast]
    refine J.add_mem (hn2 ?_) (Ideal.mem_sup_right ?_)
    · exact Ideal.mul_mem_left _ _ (Ideal.pow_mem_pow hϖn 2)
    · exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

  have hgμ0 : ((g μS : ↥Sr) : L₀) = Tμ := by rw [hg, coe_restrictEquiv]; exact hσμ
  have hgμq0 : ((g μqS : ↥Sr) : L₀) = Tμq := by rw [hg, coe_restrictEquiv]; exact hσμq
  have hgT : g μS * (cS γ * μS + cS δ) = cS α * μS + cS β :=
    Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_add, coe_cS, hgμ0]; exact hT)
  have hgTq : g μqS * (cS γ * μqS + cS δ) = cS α * μqS + cS β :=
    Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_add, coe_cS, hgμq0]; exact hTq)

  have memW : (cst γ * lambdaModC (AlgebraicClosure ℚ) + cst δ)⁻¹ ∈ Sr := by
    refine ⟨1, C γ * X 0 + C δ, ?_, ?_⟩
    · simp [pointEval_eq_pev, pev]; exact hD
    · simp [map_add, map_mul, evC, evX0, inv_mul_cancel₀ hD0]
  have memWq : (cst γ * lambdaNModC (AlgebraicClosure ℚ) q + cst δ)⁻¹ ∈ Sr := by
    refine ⟨1, C γ * X 1 + C δ, ?_, ?_⟩
    · simp [pointEval_eq_pev, pev]; exact hDq
    · simp [map_add, map_mul, evC, evX1, inv_mul_cancel₀ hDq0]
  set wS : ↥Sr := ⟨_, memW⟩ with hwS
  set wqS : ↥Sr := ⟨_, memWq⟩ with hwqS
  have hw : (cS γ * μS + cS δ) * wS = 1 :=
    Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_add, coe_cS, Subring.coe_one]; exact mul_inv_cancel₀ hD0)
  have hwq : (cS γ * μqS + cS δ) * wqS = 1 :=
    Subtype.ext (by simp only [Subring.coe_mul, Subring.coe_add, coe_cS, Subring.coe_one]; exact mul_inv_cancel₀ hDq0)
  have hgμ1 : g μS = (cS α * μS + cS β) * wS := by
    calc g μS = g μS * ((cS γ * μS + cS δ) * wS) := by rw [hw, mul_one]
      _ = (g μS * (cS γ * μS + cS δ)) * wS := by ring
      _ = (cS α * μS + cS β) * wS := by rw [hgT]
  have hgμq1 : g μqS = (cS α * μqS + cS β) * wqS := by
    calc g μqS = g μqS * ((cS γ * μqS + cS δ) * wqS) := by rw [hwq, mul_one]
      _ = (g μqS * (cS γ * μqS + cS δ)) * wqS := by ring
      _ = (cS α * μqS + cS β) * wqS := by rw [hgTq]

  have hu : (cS γ * cS y' + cS δ) * cS v = 1 := by
    rw [← map_mul, ← map_add, ← map_mul, hv, map_one]
  have huq : (cS γ * cS (y' ^ q) + cS δ) * cS vq = 1 := by
    rw [← map_mul, ← map_add, ← map_mul, hvq, map_one]
  have hw' : (cS γ * (cS y' + (μS - cS y')) + cS δ) * wS = 1 := by
    have : cS y' + (μS - cS y') = μS := by ring
    rw [this]; exact hw
  have hwq' : (cS γ * (cS (y' ^ q) + (μqS - cS (y' ^ q))) + cS δ) * wqS = 1 := by
    have : cS (y' ^ q) + (μqS - cS (y' ^ q)) = μqS := by ring
    rw [this]; exact hwq
  have tay := moebius_taylor (cS α) (cS β) (cS γ) (cS δ) (cS y') (μS - cS y') (cS v) wS hu hw'
  have tayq := moebius_taylor (cS α) (cS β) (cS γ) (cS δ) (cS (y' ^ q)) (μqS - cS (y' ^ q)) (cS vq) wqS huq hwq'
  have hgμ : g μS = cS ((α * y' + β) * v) + cS ((α * δ - β * γ) * v ^ 2) * (μS - cS y')
      + (μS - cS y') ^ 2 * (-(cS γ * (cS α * cS δ - cS β * cS γ) * cS v ^ 2 * wS)) := by
    rw [hgμ1]
    have : cS y' + (μS - cS y') = μS := by ring
    rw [this] at tay
    rw [tay]; simp only [map_mul, map_add, map_sub, map_pow]
  have hgμq : g μqS = cS ((α * y' ^ q + β) * vq) + cS ((α * δ - β * γ) * vq ^ 2) * (μqS - cS (y' ^ q))
      + (μqS - cS (y' ^ q)) ^ 2 * (-(cS γ * (cS α * cS δ - cS β * cS γ) * cS vq ^ 2 * wqS)) := by
    rw [hgμq1]
    have : cS (y' ^ q) + (μqS - cS (y' ^ q)) = μqS := by ring
    rw [this] at tayq
    rw [tayq]; simp only [map_mul, map_add, map_sub, map_pow]

  have hm₁ : μS - cS y' ∈ n := by
    have : μS - cS y' = (μS - cS y) + cS (y - y') := by rw [map_sub]; ring
    rw [this]
    refine n.add_mem hm1n (mapI₁ _ ?_)
    have : y - y' = -(y' - y) := by ring
    rw [this]; exact (Ideal.span {ϖ}).neg_mem hy'y
  have hm₂ : μqS - cS (y' ^ q) ∈ n := by
    have : μqS - cS (y' ^ q) = (μqS - cS (y ^ q)) + cS (y ^ q - y' ^ q) := by rw [map_sub]; ring
    rw [this]
    refine n.add_mem hm2n (mapI₁ _ ?_)
    obtain ⟨t, ht⟩ := sub_dvd_pow_sub_pow y y' q
    rw [ht]
    refine Ideal.mul_mem_right _ _ ?_
    have : y - y' = -(y' - y) := by ring
    rw [this]; exact (Ideal.span {ϖ}).neg_mem hy'y
  have hc₁' : cS ((α * δ - β * γ) * v ^ 2) - cS ζ₀ ∈ n := by rw [← map_sub]; exact mapI₁ _ hc₁
  have hc₂' : cS ((α * δ - β * γ) * vq ^ 2) - cS ζ₀' ∈ n := by rw [← map_sub]; exact mapI₁ _ hc₂
  have hCH' : cS ((α * y' + β) * v) - cS ((α * y' ^ q + β) * vq) ^ q - cS ζ₀ * (cS y' - cS (y' ^ q) ^ q) ∈ J := by
    have : cS ((α * y' + β) * v) - cS ((α * y' ^ q + β) * vq) ^ q - cS ζ₀ * (cS y' - cS (y' ^ q) ^ q)
        = cS ((α * y' + β) * v - ((α * y' ^ q + β) * vq) ^ q - ζ₀ * (y' - (y' ^ q) ^ q)) := by
      simp only [map_sub, map_mul, map_pow]
    rw [this]; exact mapJ _ hCH
  have hCG' : cS ((α * y' ^ q + β) * vq) - cS ((α * y' + β) * v) ^ q - cS ζ₀' * (cS (y' ^ q) - cS y' ^ q) ∈ J := by
    have : cS ((α * y' ^ q + β) * vq) - cS ((α * y' + β) * v) ^ q - cS ζ₀' * (cS (y' ^ q) - cS y' ^ q)
        = cS ((α * y' ^ q + β) * vq - ((α * y' + β) * v) ^ q - ζ₀' * (y' ^ q - y' ^ q)) := by
      simp only [map_sub, map_mul, map_pow]
    rw [this]; exact mapJ _ hCG
  have core := tangency_core q hp g.toRingHom J n hn2 hqJ μS μqS (cS y') (cS (y' ^ q))
    (μS - cS y') (μqS - cS (y' ^ q)) (cS ((α * y' + β) * v)) (cS ((α * y' ^ q + β) * vq))
    (cS ((α * δ - β * γ) * v ^ 2)) (cS ((α * δ - β * γ) * vq ^ 2)) (cS ζ₀) (cS ζ₀') _ _
    (by ring) (by ring) hm₁ hm₂ hgμ hgμq hc₁' hc₂' hCH' hCG'
  simpa using core

end Assembly

section Main

local notation "L₀'" => LaurentSeries (AlgebraicClosure ℚ)

theorem isUnit_coeffSubring_of_red_ne_zero {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (c : ↥(coeffSubring A K)) (hc : redRestrict red K c ≠ 0) : IsUnit c := by
  have hp : q.Prime := Fact.out
  have hc0 : c ≠ 0 := fun h => hc (by rw [h, map_zero])
  rcases coeffSubring_eq_or_isDiscreteValuationRing A K with hK | hdvr
  ·
    have hcK : ((c : AlgebraicClosure ℚ))⁻¹ ∈ coeffSubring A K := by
      have hc' : (c : AlgebraicClosure ℚ) ∈ K.toSubalgebra.toSubring := (SetLike.ext_iff.mp hK _).mp c.2
      exact (SetLike.ext_iff.mp hK _).mpr (K.inv_mem hc')
    have hc0' : (c : AlgebraicClosure ℚ) ≠ 0 := fun h => hc0 (Subtype.ext h)
    refine ⟨⟨c, ⟨_, hcK⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
    · change (c : AlgebraicClosure ℚ) * (c : AlgebraicClosure ℚ)⁻¹ = 1; exact mul_inv_cancel₀ hc0'
    · change (c : AlgebraicClosure ℚ)⁻¹ * (c : AlgebraicClosure ℚ) = 1; exact inv_mul_cancel₀ hc0'
  ·
    haveI := hdvr
    by_contra hu
    have hmem : c ∈ IsLocalRing.maximalIdeal ↥(coeffSubring A K) := (IsLocalRing.mem_maximalIdeal _).2 hu
    have hprime : (RingHom.ker (redRestrict red K)).IsPrime := RingHom.ker_isPrime _
    have hq0 : ((q : ℕ) : ↥(coeffSubring A K)) ≠ 0 := by
      intro h
      have := congrArg (fun x : ↥(coeffSubring A K) => (x : AlgebraicClosure ℚ)) h
      simp only [Subring.coe_natCast, Subring.coe_zero, Nat.cast_eq_zero] at this
      exact hp.ne_zero this
    have hqker : ((q : ℕ) : ↥(coeffSubring A K)) ∈ RingHom.ker (redRestrict red K) := by
      rw [RingHom.mem_ker, map_natCast, CharP.cast_eq_zero]
    have hne : RingHom.ker (redRestrict red K) ≠ ⊥ := fun h => hq0 (by rw [h] at hqker; exact hqker)
    have hmax : (RingHom.ker (redRestrict red K)).IsMaximal := hprime.isMaximal hne
    have : IsLocalRing.maximalIdeal ↥(coeffSubring A K) = RingHom.ker (redRestrict red K) :=
      (IsLocalRing.eq_maximalIdeal hmax).symm
    rw [this, RingHom.mem_ker] at hmem
    exact hc hmem

theorem stab_main
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ6 : ∀ x : ↥(lambdaFieldOver q K), σ^[6] x = x)
    (hσ0 : a = 0 →
        ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
         (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))
    (hσ1728 : a = 1728 →
        ((16 * l = -1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (32 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (8 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹))) :
    ∃ (hSF : (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ (lambdaFieldOver q K).toSubring)
      (hσS : ∀ (b : LaurentSeries (AlgebraicClosure ℚ)) (hb : b ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((σ ⟨b, hSF hb⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
      (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (ζ₀ ζ₀' : ↥(coeffSubring A K)),

      (∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((g z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((σ ⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hSF z.2⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ))) ∧

      redRestrict red K ζ₀ ^ jWidth a = 1 ∧
      (∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1) ∧
      redRestrict red K ζ₀' = redRestrict red K ζ₀ ^ q ∧

      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ∧
      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))}  := by
  classical
  have hp : q.Prime := Fact.out
  have hq2 : q ≠ 2 := by omega
  have hodd : Odd q := hp.odd_of_ne_two hq2
  set red₀ := redRestrict red K with hred₀
  set cst := CharPReduction.constSeries (coeffSubring A K) with hcst
  have hunit : ∀ c : ↥(coeffSubring A K), red₀ c ≠ 0 → IsUnit c :=
    fun c hc => isUnit_coeffSubring_of_red_ne_zero red K ϖ hϖ c hc
  have hpϖ : red₀ ((q : ℕ) : ↥(coeffSubring A K)) = 0 := by rw [map_natCast, CharP.cast_eq_zero]

  have hk2 : (2 : k) ≠ 0 := by
    rw [show (2 : k) = ((2 : ℕ) : k) by norm_num, Ne, CharP.cast_eq_zero_iff k q]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hk3 : (3 : k) ≠ 0 := by
    rw [show (3 : k) = ((3 : ℕ) : k) by norm_num, Ne, CharP.cast_eq_zero_iff k q]
    intro h; have := Nat.le_of_dvd (by norm_num) h; omega
  have hkpow2 : ∀ n : ℕ, ((2 : k)) ^ n ≠ 0 := fun n => pow_ne_zero _ hk2
  have hk8 : (8 : k) ≠ 0 := by have := hkpow2 3; norm_num at this; exact this
  have hk16 : (16 : k) ≠ 0 := by have := hkpow2 4; norm_num at this; exact this
  have hk32 : (32 : k) ≠ 0 := by have := hkpow2 5; norm_num at this; exact this
  have hk256 : (256 : k) ≠ 0 := by have := hkpow2 8; norm_num at this; exact this
  have hfrobNat : ∀ n : ℕ, ((n : k)) ^ q = n := fun n => by rw [← frobenius_def, map_natCast]

  have frob_fix : ∀ (n : ℕ) (c : k), (n : k) ≠ 0 → (n : k) * l = c → c ^ q = c → l ^ q = l := by
    intro n c hn hnl hc
    have h1 : ((n : k) * l) ^ q = (n : k) * l := by rw [hnl, hc]
    rw [mul_pow, hfrobNat] at h1
    exact mul_left_cancel₀ hn h1
  have neg_one_q : ((-1 : k)) ^ q = -1 := Odd.neg_one_pow hodd

  have red_nat : ∀ n : ℕ, red₀ (n : ↥(coeffSubring A K)) = (n : k) := fun n => map_natCast red₀ n

  have h1728 : (1728 : k) ≠ 0 := by
    have : (1728 : k) = 2 ^ 6 * 3 ^ 3 := by norm_num
    rw [this]; exact mul_ne_zero (pow_ne_zero _ hk2) (pow_ne_zero _ hk3)
  rcases h01728 with rfl | rfl
  ·
    obtain ⟨hTμ, hTμq⟩ := hσ0 rfl
    have hPl : 256 * l ^ 2 - 16 * l + 1 = 0 := by
      have h := hla
      rw [zero_mul, eq_comm, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h hk256
      · have := (pow_eq_zero_iff (n := 3) (by norm_num)).1 h
        linear_combination this
    obtain ⟨hlp2, -, -, -, h1l, hprod, -⟩ := root_facts q hq l hPl
    have hPlq : 256 * (l ^ q) ^ 2 - 16 * l ^ q + 1 = 0 := by
      have h := congrArg (fun x : k => x ^ q) hPl
      have e : ((256 : k) * l ^ 2 - 16 * l + 1) ^ q = 256 * (l ^ q) ^ 2 - 16 * l ^ q + 1 := by
        rw [add_pow_char, sub_pow_char, mul_pow, mul_pow, one_pow, ← pow_mul, mul_comm 2 q, pow_mul]
        have e256 : (256 : k) ^ q = 256 := by exact_mod_cast hfrobNat 256
        have e16 : (16 : k) ^ q = 16 := by exact_mod_cast hfrobNat 16
        rw [e256, e16]
      simp only [e, zero_pow hp.ne_zero] at h
      exact h
    obtain ⟨-, -, -, -, h1lq, hprodq, -⟩ := root_facts q hq (l ^ q) hPlq
    have hPy : red₀ (256 * y ^ 2 - 16 * y + 1) = 0 := by
      have e : red₀ (256 * y ^ 2 - 16 * y + 1) = 256 * red₀ y ^ 2 - 16 * red₀ y + 1 := by
        simp only [map_add, map_sub, map_mul, map_pow, map_one, map_ofNat]
      rw [e, hy]; exact hPl
    obtain ⟨y', v, vq, hy'y, hv, hvq, hζ3, hζ1, hζ2, hc1, hc2, hCH, hCG⟩ :=
      constants_case0 (κ := k) q hq red₀ ϖ hϖ hunit hpϖ y hPy
    have sD : redRestrict red K (-256) * l + redRestrict red K 16 ≠ 0 := by
      simp only [map_neg, map_ofNat]
      have : (-256 : k) * l + 16 = 16 * (1 - 16 * l) := by ring
      rw [this]; exact mul_ne_zero hk16 h1l
    have sDq : redRestrict red K (-256) * l ^ q + redRestrict red K 16 ≠ 0 := by
      simp only [map_neg, map_ofNat]
      have : (-256 : k) * l ^ q + 16 = 16 * (1 - 16 * l ^ q) := by ring
      rw [this]; exact mul_ne_zero hk16 h1lq
    have sl : redRestrict red K 0 * l + redRestrict red K 1 = l * (redRestrict red K (-256) * l + redRestrict red K 16) := by
      simp only [map_zero, map_one, map_neg, map_ofNat, zero_mul, zero_add]; linear_combination -hprod
    have slq : redRestrict red K 0 * l ^ q + redRestrict red K 1
        = l ^ q * (redRestrict red K (-256) * l ^ q + redRestrict red K 16) := by
      simp only [map_zero, map_one, map_neg, map_ofNat, zero_mul, zero_add]; linear_combination -hprodq
    have sT : (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ = (cst 0 * lambdaModC (AlgebraicClosure ℚ) + cst 1) * (cst (-256) * lambdaModC (AlgebraicClosure ℚ) + cst 16)⁻¹ := by
      simp only [map_zero, map_one, map_neg, map_ofNat, zero_mul, zero_add, one_mul]
      congr 1; ring
    have sTq : (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ = (cst 0 * lambdaNModC (AlgebraicClosure ℚ) q + cst 1) * (cst (-256) * lambdaNModC (AlgebraicClosure ℚ) q + cst 16)⁻¹ := by
      simp only [map_zero, map_one, map_neg, map_ofNat, zero_mul, zero_add, one_mul]
      congr 1; ring
    obtain ⟨hSF, hσS, g, hgσ, hH, hG⟩ := stab_of_data red K l hq2 hlp2 ϖ y σ hσK hσ6
      0 1 (-256) 16 _ _ hTμ hTμq sT sTq sl slq sD sDq (256 * y' ^ 2) ((256 * y' ^ 2) ^ q) y' v vq hy'y
      (by convert hv using 2; ring) (by convert hvq using 2; ring)
      (by convert hc1 using 2; ring) (by convert hc2 using 2; ring)
      (by simpa using hCH) (by simpa using hCG)
    refine ⟨hSF, hσS, g, 256 * y' ^ 2, (256 * y' ^ 2) ^ q, hgσ, ?_, ?_, ?_, hH, hG⟩
    · rw [jWidth_of_eq_zero rfl]; exact hζ3
    · intro m hm0 hm3
      rw [jWidth_of_eq_zero rfl] at hm3
      interval_cases m
      · rw [pow_one]; exact hζ1
      · exact hζ2
    · rw [map_pow]
  ·
    have hjw : jWidth (1728 : k) = 2 := jWidth_of_eq_1728 rfl h1728

    have hres : red₀ (-1) ^ jWidth (1728 : k) = 1 ∧
        (∀ m : ℕ, 0 < m → m < jWidth (1728 : k) → red₀ (-1) ^ m ≠ 1) ∧ red₀ (-1) = red₀ (-1) ^ q := by
      rw [hjw, map_neg, map_one]
      refine ⟨by norm_num, ?_, by rw [neg_one_q]⟩
      intro m hm0 hm2
      interval_cases m
      rw [pow_one]
      intro h
      have : (2 : k) = 0 := by linear_combination -h
      exact hk2 this
    obtain ⟨hζe, hζprim, hζq⟩ := hres
    rcases hσ1728 rfl with ⟨hl16, hTμ, hTμq⟩ | ⟨hl32, hTμ, hTμq⟩ | ⟨hl8, hTμ, hTμq⟩
    ·
      have hlq : l ^ q = l := frob_fix 16 (-1) hk16 hl16 neg_one_q
      have hl2 : l ^ (q ^ 2) = l := by rw [pow_two, pow_mul, hlq, hlq]
      obtain ⟨u, hu⟩ := (hunit (16 : ↥(coeffSubring A K)) (by rw [map_ofNat]; exact hk16)).exists_left_inv
      set r₀ : ↥(coeffSubring A K) := -u with hr₀def
      have hru : red₀ u * 16 = 1 := by have := congrArg red₀ hu; rwa [map_mul, map_ofNat, map_one] at this
      have hr₀ : red₀ r₀ = l := by
        rw [hr₀def, map_neg]
        apply mul_left_cancel₀ hk16
        rw [hl16]; linear_combination -hru
      have hfix : (0 : ↥(coeffSubring A K)) * r₀ + 1 = r₀ * (256 * r₀ + 0) := by
        rw [hr₀def]; linear_combination (-(16 * u + 1)) * hu
      have hdet : (0 : ↥(coeffSubring A K)) * 0 - 1 * 256 = -(256 * r₀ + 0) ^ 2 := by
        rw [hr₀def]; linear_combination (256 * (16 * u + 1)) * hu
      have hDr : red₀ (256 * r₀ + 0) ≠ 0 := by
        rw [map_add, map_mul, map_ofNat, map_zero, hr₀, add_zero]
        have : (256 : k) * l = 16 * (16 * l) := by ring
        rw [this, hl16]; norm_num; exact hk16
      have hr₀p : r₀ ^ q - r₀ ∈ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))} := by
        have h := frac_pow_prime_sub_mem (R := ↥(coeffSubring A K)) q hp 1 16 u (by exact_mod_cast hu)
        simp only [Nat.cast_one, one_mul] at h
        rw [hr₀def, Odd.neg_pow hodd]
        have : -u ^ q - -u = -(u ^ q - u) := by ring
        rw [this]; exact (Ideal.span {((q : ℕ) : ↥(coeffSubring A K))}).neg_mem h
      obtain ⟨v, vq, hv, hvq, hφ, hc1, hc2, hCH, hCG⟩ :=
        constants_fixed q hp red₀ ϖ hϖ hunit hpϖ 0 1 256 0 r₀ hfix hdet hDr hr₀p
      have hy'y : r₀ - y ∈ Ideal.span {ϖ} := by
        have : red₀ (r₀ - y) = 0 := by rw [map_sub, hr₀, hred₀, hy, sub_self]
        obtain ⟨d, hd⟩ := (hϖ _).1 this
        exact Ideal.mem_span_singleton'.2 ⟨d, by rw [hd, mul_comm]⟩
      have sD : redRestrict red K 256 * l + redRestrict red K 0 ≠ 0 := by
        simp only [map_zero, map_ofNat, add_zero]
        have : (256 : k) * l = 16 * (16 * l) := by ring
        rw [this, hl16]; norm_num; exact hk16
      have sDq : redRestrict red K 256 * l ^ q + redRestrict red K 0 ≠ 0 := by rw [hlq]; exact sD
      have sl : redRestrict red K 0 * l + redRestrict red K 1 = l * (redRestrict red K 256 * l + redRestrict red K 0) := by
        simp only [map_zero, map_one, map_ofNat, zero_mul, zero_add, add_zero]; linear_combination (-(16 * l - 1)) * hl16
      have slq : redRestrict red K 0 * l ^ q + redRestrict red K 1
          = l ^ q * (redRestrict red K 256 * l ^ q + redRestrict red K 0) := by rw [hlq]; exact sl
      have sT : (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ = (cst 0 * lambdaModC (AlgebraicClosure ℚ) + cst 1) * (cst 256 * lambdaModC (AlgebraicClosure ℚ) + cst 0)⁻¹ := by
        simp only [map_zero, map_one, map_ofNat, zero_mul, zero_add, one_mul, add_zero]
      have sTq : (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹ = (cst 0 * lambdaNModC (AlgebraicClosure ℚ) q + cst 1) * (cst 256 * lambdaNModC (AlgebraicClosure ℚ) q + cst 0)⁻¹ := by
        simp only [map_zero, map_one, map_ofNat, zero_mul, zero_add, one_mul, add_zero]
      obtain ⟨hSF, hσS, g, hgσ, hH, hG⟩ := stab_of_data red K l hq2 hl2 ϖ y σ hσK hσ6
        0 1 256 0 _ _ hTμ hTμq sT sTq sl slq sD sDq (-1) (-1) r₀ v vq hy'y hv hvq
        (by rw [hc1]; simp) hc2 hCH hCG
      exact ⟨hSF, hσS, g, -1, -1, hgσ, hζe, hζprim, hζq, hH, hG⟩
    ·
      have hlq : l ^ q = l := frob_fix 32 1 hk32 hl32 (one_pow q)
      have hl2 : l ^ (q ^ 2) = l := by rw [pow_two, pow_mul, hlq, hlq]
      obtain ⟨u, hu⟩ := (hunit (32 : ↥(coeffSubring A K)) (by rw [map_ofNat]; exact hk32)).exists_left_inv
      obtain ⟨w, hw⟩ := (hunit (16 : ↥(coeffSubring A K)) (by rw [map_ofNat]; exact hk16)).exists_left_inv
      set r₀ : ↥(coeffSubring A K) := u with hr₀def
      have hru : red₀ u * 32 = 1 := by have := congrArg red₀ hu; rwa [map_mul, map_ofNat, map_one] at this
      have hrw : red₀ w * 16 = 1 := by have := congrArg red₀ hw; rwa [map_mul, map_ofNat, map_one] at this
      have hr₀ : red₀ r₀ = l := by
        apply mul_left_cancel₀ hk32
        rw [hl32, mul_comm]; exact hru
      have hfix : (-1 : ↥(coeffSubring A K)) * r₀ + w = r₀ * (0 * r₀ + 1) := by
        rw [hr₀def]; linear_combination (-w) * hu + (2 * u) * hw
      have hdet : (-1 : ↥(coeffSubring A K)) * 1 - w * 0 = -(0 * r₀ + 1) ^ 2 := by ring
      have hDr : red₀ (0 * r₀ + 1) ≠ 0 := by
        rw [map_add, map_mul, map_zero, zero_mul, zero_add, map_one]; exact one_ne_zero
      have hr₀p : r₀ ^ q - r₀ ∈ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))} := by
        have h := frac_pow_prime_sub_mem (R := ↥(coeffSubring A K)) q hp 1 32 u (by exact_mod_cast hu)
        simpa only [Nat.cast_one, one_mul] using h
      obtain ⟨v, vq, hv, hvq, hφ, hc1, hc2, hCH, hCG⟩ :=
        constants_fixed q hp red₀ ϖ hϖ hunit hpϖ (-1) w 0 1 r₀ hfix hdet hDr hr₀p
      have hy'y : r₀ - y ∈ Ideal.span {ϖ} := by
        have : red₀ (r₀ - y) = 0 := by rw [map_sub, hr₀, hred₀, hy, sub_self]
        obtain ⟨d, hd⟩ := (hϖ _).1 this
        exact Ideal.mem_span_singleton'.2 ⟨d, by rw [hd, mul_comm]⟩
      have hcw : cst w = (16 : L₀')⁻¹ := by
        apply eq_inv_of_mul_eq_one_left
        have := congrArg cst hw; rwa [map_mul, map_ofNat, map_one] at this
      have hw2 : red₀ w = 2 * l := by
        apply mul_left_cancel₀ hk16
        rw [mul_comm, hrw]; linear_combination -hl32
      have sD : redRestrict red K 0 * l + redRestrict red K 1 ≠ 0 := by
        simp only [map_zero, map_one, zero_mul, zero_add]; exact one_ne_zero
      have sDq : redRestrict red K 0 * l ^ q + redRestrict red K 1 ≠ 0 := by rw [hlq]; exact sD
      have sl : redRestrict red K (-1) * l + redRestrict red K w = l * (redRestrict red K 0 * l + redRestrict red K 1) := by
        rw [← hred₀]; simp only [map_zero, map_one, map_neg, zero_mul, zero_add, mul_one, hw2]; ring
      have slq : redRestrict red K (-1) * l ^ q + redRestrict red K w
          = l ^ q * (redRestrict red K 0 * l ^ q + redRestrict red K 1) := by rw [hlq]; exact sl
      have sT : 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) = (cst (-1) * lambdaModC (AlgebraicClosure ℚ) + cst w) * (cst 0 * lambdaModC (AlgebraicClosure ℚ) + cst 1)⁻¹ := by
        rw [hcw]; simp only [map_zero, map_one, map_neg, zero_mul, zero_add, inv_one, mul_one]; ring
      have sTq : 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q = (cst (-1) * lambdaNModC (AlgebraicClosure ℚ) q + cst w) * (cst 0 * lambdaNModC (AlgebraicClosure ℚ) q + cst 1)⁻¹ := by
        rw [hcw]; simp only [map_zero, map_one, map_neg, zero_mul, zero_add, inv_one, mul_one]; ring
      obtain ⟨hSF, hσS, g, hgσ, hH, hG⟩ := stab_of_data red K l hq2 hl2 ϖ y σ hσK hσ6
        (-1) w 0 1 _ _ hTμ hTμq sT sTq sl slq sD sDq (-1) (-1) r₀ v vq hy'y hv hvq
        (by rw [hc1]; simp) hc2 hCH hCG
      exact ⟨hSF, hσS, g, -1, -1, hgσ, hζe, hζprim, hζq, hH, hG⟩
    ·
      have hlq : l ^ q = l := frob_fix 8 1 hk8 hl8 (one_pow q)
      have hl2 : l ^ (q ^ 2) = l := by rw [pow_two, pow_mul, hlq, hlq]
      obtain ⟨u, hu⟩ := (hunit (8 : ↥(coeffSubring A K)) (by rw [map_ofNat]; exact hk8)).exists_left_inv
      set r₀ : ↥(coeffSubring A K) := u with hr₀def
      have hru : red₀ u * 8 = 1 := by have := congrArg red₀ hu; rwa [map_mul, map_ofNat, map_one] at this
      have hr₀ : red₀ r₀ = l := by
        apply mul_left_cancel₀ hk8
        rw [hl8, mul_comm]; exact hru
      have hfix : (1 : ↥(coeffSubring A K)) * r₀ + 0 = r₀ * (16 * r₀ + (-1)) := by
        rw [hr₀def]; linear_combination (-2 * u) * hu
      have hdet : (1 : ↥(coeffSubring A K)) * (-1) - 0 * 16 = -(16 * r₀ + (-1)) ^ 2 := by
        rw [hr₀def]; linear_combination (32 * u) * hu
      have hDr : red₀ (16 * r₀ + (-1)) ≠ 0 := by
        rw [map_add, map_mul, map_ofNat, map_neg, map_one, hr₀]
        have : (16 : k) * l + -1 = 2 * (8 * l) - 1 := by ring
        rw [this, hl8]; norm_num
      have hr₀p : r₀ ^ q - r₀ ∈ Ideal.span {((q : ℕ) : ↥(coeffSubring A K))} := by
        have h := frac_pow_prime_sub_mem (R := ↥(coeffSubring A K)) q hp 1 8 u (by exact_mod_cast hu)
        simpa only [Nat.cast_one, one_mul] using h
      obtain ⟨v, vq, hv, hvq, hφ, hc1, hc2, hCH, hCG⟩ :=
        constants_fixed q hp red₀ ϖ hϖ hunit hpϖ 1 0 16 (-1) r₀ hfix hdet hDr hr₀p
      have hy'y : r₀ - y ∈ Ideal.span {ϖ} := by
        have : red₀ (r₀ - y) = 0 := by rw [map_sub, hr₀, hred₀, hy, sub_self]
        obtain ⟨d, hd⟩ := (hϖ _).1 this
        exact Ideal.mem_span_singleton'.2 ⟨d, by rw [hd, mul_comm]⟩
      have sD : redRestrict red K 16 * l + redRestrict red K (-1) ≠ 0 := by
        simp only [map_neg, map_one, map_ofNat]
        have : (16 : k) * l + -1 = 2 * (8 * l) - 1 := by ring
        rw [this, hl8]; norm_num
      have sDq : redRestrict red K 16 * l ^ q + redRestrict red K (-1) ≠ 0 := by rw [hlq]; exact sD
      have sl : redRestrict red K 1 * l + redRestrict red K 0 = l * (redRestrict red K 16 * l + redRestrict red K (-1)) := by
        simp only [map_zero, map_one, map_neg, map_ofNat, one_mul, add_zero]; linear_combination (-2 * l) * hl8
      have slq : redRestrict red K 1 * l ^ q + redRestrict red K 0
          = l ^ q * (redRestrict red K 16 * l ^ q + redRestrict red K (-1)) := by rw [hlq]; exact sl
      have sT : lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ = (cst 1 * lambdaModC (AlgebraicClosure ℚ) + cst 0) * (cst 16 * lambdaModC (AlgebraicClosure ℚ) + cst (-1))⁻¹ := by
        simp only [map_zero, map_one, map_neg, map_ofNat, one_mul, add_zero, sub_eq_add_neg]
      have sTq : lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹ = (cst 1 * lambdaNModC (AlgebraicClosure ℚ) q + cst 0) * (cst 16 * lambdaNModC (AlgebraicClosure ℚ) q + cst (-1))⁻¹ := by
        simp only [map_zero, map_one, map_neg, map_ofNat, one_mul, add_zero, sub_eq_add_neg]
      obtain ⟨hSF, hσS, g, hgσ, hH, hG⟩ := stab_of_data red K l hq2 hl2 ϖ y σ hσK hσ6
        1 0 16 (-1) _ _ hTμ hTμq sT sTq sl slq sD sDq (-1) (-1) r₀ v vq hy'y hv hvq
        (by rw [hc1]; simp) hc2 hCH hCG
      exact ⟨hSF, hσS, g, -1, -1, hgσ, hζe, hζprim, hζq, hH, hG⟩

end Main

end S14STAB

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized in
set_option maxHeartbeats 3200000 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    {q : ℕ} [Fact q.Prime] (hq : 5 ≤ q) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq k] (red : A →+* k)
    (a : k) (h01728 : a = 0 ∨ a = 1728)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ K]
    (ϖ : ↥(coeffSubring A K)) (hϖ : ∀ c : ↥(coeffSubring A K), redRestrict red K c = 0 ↔ ∃ d, c = ϖ * d)
    (l : k) (hla : a * ((16 * l) ^ 2 * (16 * l - 1) ^ 2) = 256 * ((16 * l) ^ 2 - 16 * l + 1) ^ 3)
    (y : ↥(coeffSubring A K)) (hy : redRestrict red K y = l)
    (σ : ↥(lambdaFieldOver q K) ≃+* ↥(lambdaFieldOver q K))
    (hσK : ∀ x : ↥(lambdaFieldOver q K), (x : LaurentSeries (AlgebraicClosure ℚ)) ∈
        Set.range (CharPReduction.constSeries K.toSubalgebra.toSubring) → σ x = x)
    (hσ6 : ∀ x : ↥(lambdaFieldOver q K), σ^[6] x = x)
    (hσ0 : a = 0 →
        ((σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
         (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (16 - 256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹))
    (hσ1728 : a = 1728 →
        ((16 * l = -1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaModC (AlgebraicClosure ℚ))⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = (256 * lambdaNModC (AlgebraicClosure ℚ) q)⁻¹) ∨
         (32 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaModC (AlgebraicClosure ℚ) ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = 16⁻¹ - lambdaNModC (AlgebraicClosure ℚ) q) ∨
         (8 * l = 1 ∧ (σ (⟨lambdaModC (AlgebraicClosure ℚ), lambdaModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaModC (AlgebraicClosure ℚ) * (16 * lambdaModC (AlgebraicClosure ℚ) - 1)⁻¹ ∧
          (σ (⟨lambdaNModC (AlgebraicClosure ℚ) q, lambdaNModC_mem_lambdaFieldOver q K⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) = lambdaNModC (AlgebraicClosure ℚ) q * (16 * lambdaNModC (AlgebraicClosure ℚ) q - 1)⁻¹))) :
    ∃ (hSF : (lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≤ (lambdaFieldOver q K).toSubring)
      (hσS : ∀ (b : LaurentSeries (AlgebraicClosure ℚ)) (hb : b ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((σ ⟨b, hSF hb⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ)) ∈ lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))
      (g : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)) ≃+* ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) (ζ₀ ζ₀' : ↥(coeffSubring A K)),

      (∀ z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)),
        ((g z : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) : LaurentSeries (AlgebraicClosure ℚ)) =
          ((σ ⟨(z : LaurentSeries (AlgebraicClosure ℚ)), hSF z.2⟩ : ↥(lambdaFieldOver q K)) : LaurentSeries (AlgebraicClosure ℚ))) ∧

      redRestrict red K ζ₀ ^ jWidth a = 1 ∧
      (∀ m : ℕ, 0 < m → m < jWidth a → redRestrict red K ζ₀ ^ m ≠ 1) ∧
      redRestrict red K ζ₀' = redRestrict red K ζ₀ ^ q ∧

      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.X 1 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ∧
      g (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
          - (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ζ₀'),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))) * (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.X 0 ^ q),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))
        ∈ Ideal.span {(⟨lambdaEval q (coeffSubring A K) (MvPolynomial.C ϖ),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))), (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 0 - MvPolynomial.C y),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q))),
            (⟨lambdaEval q (coeffSubring A K) (MvPolynomial.X 1 - MvPolynomial.C (y ^ q)),
          lambdaEval_mem_lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q) _⟩ :
          ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} ^ 2
          ⊔ Ideal.span {((q : ℕ) : ↥(lambdaLocalizedAtPoint q (coeffSubring A K) (redRestrict red K) l (l ^ q)))} :=
  S14STAB.stab_main hq red a h01728 K ϖ hϖ l hla y hy σ hσK hσ6 hσ0 hσ1728

end S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_sub_smul_mem_sq_sup_of_stabilizer_of_eq_zero_or_eq_1728
end P2MW
export P2MW.S_ModularCurve_LambdaNodeLocalized_exists_ringEquiv_sub_smul_mem_sq_sup_of_stabilizer_of_eq_zero_or_eq_1728 (solution)
