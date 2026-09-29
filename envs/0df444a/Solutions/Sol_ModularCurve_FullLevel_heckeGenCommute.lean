-- Prove2me | solution 1 for ModularCurve.FullLevel.heckeGenCommute
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/03bafaec-066f-584d-9b60-15ab388522db

import Mathlib
import Definitions.Def_ModularCurve_FullLevelJacobian
import Theorems.Thm_ModularCurve_diamondHBar_mul
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_comm
import Theorems.Thm_ModularCurve_heckeOperatorHAlong_diamondHBar_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_heckeGenCommute
p2m_attr_erase "instance" "AlgebraicCurve.Place.instIsPrimeCenter AlgebraicCurve.Place.instIsFractionRingIntegralClosureAt AlgebraicCurve.Place.instIsTorsionFreeSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.Place.instIsDedekindDomainIntegralClosureAt AlgebraicCurve.Place.instFiniteSubtypeMemValuationSubringToValuationSubringIntegralClosureAt AlgebraicCurve.IsCurveOver.instNontrivialKaehler AlgebraicCurve.IsCurveOver.instFreeKaehler AlgebraicCurve.IsCurveOver.toHasPrincipalDivisors AlgebraicCurve.IsCurveOver.instFiniteResidue AlgebraicCurve.Place.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicValuation AlgebraicCurve.Place.instIsTrivialOnWithZeroMultiplicativeIntAdicValuation ModularCurve.PhiGen.instNeZeroPhiGenCosetA ModularCurve.instIsDomainTensorProduct AlgebraicClosure.Rat.isGalois"
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL AlgebraicCurve.Place.placeOfPrime_toValuationSubring AlgebraicCurve.Place.mem_fiberOver AlgebraicCurve.Place.fiberEquiv_symm_apply AlgebraicCurve.Place.fiberEquiv_apply AlgebraicCurve.Place.centerHeightOneSpectrum_asIdeal AlgebraicCurve.IsFrobeniusEndo.frobNormRingHom_apply ModularCurve.frobeniusPushforwardGeomLevelPic0_mk ModularCurve.coe_frobeniusGeomLevelEquiv_apply ModularCurve.coe_frobeniusPushforwardGeomLevelDegZero ModularCurve.heckeFibreGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusGeomLevel_apply_coe ModularCurve.frobeniusPullbackGeomLevelPic0OfIsCurveOver_mk ModularCurve.coe_heckeFibreGeomLevelDegZero ModularCurve.coe_frobeniusPullbackGeomLevelDegZero ModularCurve.frobeniusPullbackGeomLevelPic0_mk ModularCurve.frobeniusPullbackGeomLevel_single ModularCurve.heckeFibreGeomLevelPic0_mk ModularCurve.frobeniusPushforwardGeomLevelPic0OfIsCurveOver_mk ModularCurve.frobeniusPushforwardGeomLevel_single ModularCurve.qExpandAlgC_apply AlgebraicCurve.Place.congrEquiv_symm_apply AlgebraicCurve.RationalFunctionField.heightOneSpectrumOfIrreducible_asIdeal AlgebraicCurve.Place.congrRingEquiv_toValuationSubring AlgebraicCurve.Place.congrEquiv_apply AlgebraicCurve.Place.coe_comapSymmRingEquiv_apply AlgebraicCurve.RationalFunctionField.deg_placeOfPoint AlgebraicCurve.coe_frobeniusPushforwardDegZero AlgebraicCurve.IsFrobeniusEndo.coe_frobeniusPullbackDegZero ModularCurve.jqNModC_one ModularCurve.reduceModBivar_C_X ModularCurve.laurentMap_coeff"
p2m_attr_erase "simp" "ModularCurve.reduceModBivar_X ModularCurve.laurentMap_single ModularCurve.evalAtJInt_X ModularCurve.evalAtJMod_X ModularCurve.jqNMod_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coe_baseChangeEquiv_apply ModularCurve.baseChangeHom_tmul ModularCurve.qInftyPlaceBar_toValuationSubring ModularCurve.qSeriesBar_zero ModularCurve.qSeriesBar_add ModularCurve.cuspInftyFull_toValuationSubring ModularCurve.qInftyPlaceRat_toValuationSubring ModularCurve.qSeriesBar_mul ModularCurve.qSeriesBar_div ModularCurve.qSeriesBar_eq_zero_iff ModularCurve.coe_uniformizerBar ModularCurve.qSeriesBar_pow ModularCurve.cuspInfty_toValuationSubring ModularCurve.qSeriesBar_one ModularCurve.qSeriesBar_inv ModularCurve.qSeriesBar_sub ModularCurve.qSeriesBar_neg ModularCurve.coe_cuspidalDivisor₀ ModularCurve.eisensteinNumerator_nineteen ModularCurve.eisensteinNumerator_seventeen ModularCurve.eisensteinNumerator_eleven ModularCurve.eisensteinNumerator_five ModularCurve.eisensteinNumerator_seven ModularCurve.eisensteinNumerator_twentythree"
p2m_attr_erase "simp" "ModularCurve.eisensteinNumerator_thirteen ModularCurve.constantCoeff_dedekindEtaUnitQ ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularCurve.coe_heckeBetaBarRingHom ModularCurve.coe_heckeBetaBar ModularCurve.coe_heckeAlphaBar"

set_option autoImplicit false

noncomputable section

namespace W1pHC

open ModularCurve ModularCurve.FullLevel

variable {q : ℕ} [Fact q.Prime]

theorem pow_val_eq_pow_mod (ζ : Idx q) (n : ℕ) : ζ.val ^ n = ζ.val ^ (n % q) := by
  conv_lhs => rw [← Nat.div_add_mod n q, pow_add, pow_mul, ζ.isPrimitiveRoot.pow_eq_one, one_pow, one_mul]

theorem Idx.pow_pow (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = ζ.pow (a * b) := by
  apply Idx.ext
  rw [Idx.val_pow, Idx.val_pow, Idx.val_pow, ← pow_mul, Units.val_mul, ZMod.val_mul,
    ← pow_val_eq_pow_mod]

theorem Idx.pow_comm (a b : (ZMod q)ˣ) (ζ : Idx q) : (ζ.pow a).pow b = (ζ.pow b).pow a := by
  rw [Idx.pow_pow, Idx.pow_pow, mul_comm]

variable (q) (M' : ℕ)

omit [Fact q.Prime] in
theorem coprime_q_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime q :=
  (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_right M')

omit [Fact q.Prime] in
theorem coprime_level_of_not_dvd {ℓ : ℕ} (hℓ : ℓ.Prime) (h : ¬ ℓ ∣ q * M') : ℓ.Coprime (q ^ 2 * M') := by
  refine Nat.Coprime.mul_right (Nat.Coprime.pow_right 2 (coprime_q_of_not_dvd q M' hℓ h)) ?_
  exact (Nat.Prime.coprime_iff_not_dvd hℓ).2 fun hd => h (hd.mul_left q)

theorem heckeGenCommute_of_neZero [NeZero M'] : HeckeGenCommute q M' := by
  intro ℓ ℓ'
  by_cases h1 : (ℓ : ℕ) ∣ q * M'
  · rw [heckeGenJac_of_dvd h1, zero_mul, mul_zero]
  by_cases h2 : (ℓ' : ℕ) ∣ q * M'
  · rw [heckeGenJac_of_dvd h2, zero_mul, mul_zero]
  have hℓ : (ℓ : ℕ).Prime := ℓ.2
  have hℓ' : (ℓ' : ℕ).Prime := ℓ'.2
  have hq1 := coprime_q_of_not_dvd q M' hℓ h1
  have hq2 := coprime_q_of_not_dvd q M' hℓ' h2
  have hN1 := coprime_level_of_not_dvd q M' hℓ h1
  have hN2 := coprime_level_of_not_dvd q M' hℓ' h2
  haveI : Fact (ℓ : ℕ).Prime := ⟨hℓ⟩
  haveI : Fact (ℓ' : ℕ).Prime := ⟨hℓ'⟩
  refine AddMonoidHom.ext fun x => Jac.ext fun ζ => ?_
  show (heckeGenJac q M' ℓ (heckeGenJac q M' ℓ' x)).eval ζ =
    (heckeGenJac q M' ℓ' (heckeGenJac q M' ℓ x)).eval ζ
  rw [heckeGenJac_eval hℓ h1 hq1 hN1, heckeGenJac_eval hℓ' h2 hq2 hN2, heckeGenJac_eval hℓ' h2 hq2 hN2,
    heckeGenJac_eval hℓ h1 hq1 hN1, Idx.pow_comm]

  set y := x.eval ((ζ.pow (ZMod.unitOfCoprime (ℓ' : ℕ) hq2)⁻¹).pow (ZMod.unitOfCoprime (ℓ : ℕ) hq1)⁻¹)
  set a : (ZMod (q ^ 2 * M'))ˣ := (ZMod.unitOfCoprime (ℓ : ℕ) hN1)⁻¹
  set b : (ZMod (q ^ 2 * M'))ˣ := (ZMod.unitOfCoprime (ℓ' : ℕ) hN2)⁻¹
  rw [ModularCurve.heckeOperatorHAlong_diamondHBar_comm, ← ModularCurve.diamondHBar_mul,
    ModularCurve.heckeOperatorHAlong_comm (q ^ 2 * M') (levelH q M') ℓ ℓ', mul_comm a b,
    ModularCurve.diamondHBar_mul, ModularCurve.heckeOperatorHAlong_diamondHBar_comm]

theorem heckeGenCommute_all : HeckeGenCommute q M' := by
  rcases Nat.eq_zero_or_pos M' with rfl | hM'
  · intro ℓ ℓ'
    rw [heckeGenJac_of_dvd (show (ℓ : ℕ) ∣ q * 0 by rw [mul_zero]; exact dvd_zero _), zero_mul, mul_zero]
  · haveI : NeZero M' := ⟨hM'.ne'⟩
    exact heckeGenCommute_of_neZero q M'

end W1pHC

end

theorem solution (q : ℕ) [Fact q.Prime] (M' : ℕ) :
    ModularCurve.FullLevel.HeckeGenCommute q M' :=
  W1pHC.heckeGenCommute_all q M'

end S_ModularCurve_FullLevel_heckeGenCommute
end P2MW
export P2MW.S_ModularCurve_FullLevel_heckeGenCommute (solution)
