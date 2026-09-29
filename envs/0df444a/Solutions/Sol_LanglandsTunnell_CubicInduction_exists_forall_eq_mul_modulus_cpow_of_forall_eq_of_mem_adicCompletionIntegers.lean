-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/78c14327-5080-56dc-94bb-85fc01c3e6e6

import Definitions.Def_LanglandsTunnell_CubicInduction_LocalZeta31
import Definitions.Def_LanglandsTunnell_StandardLocalConstantsAt

import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.TateLocal MeasureTheory
open LanglandsTunnell.CubicInduction

namespace Ws31
namespace UnramShift

open NumberField.AdelicLevel

theorem cpow_aux (q : ℝ) (hq : 1 < q) (r : ℂ) (hr : r ≠ 0) (m : ℤ) :
    (((q ^ m : ℝ)) : ℂ) ^ (-(Complex.log r / Real.log q)) = r ^ (-m) := by
  have hqm : 0 < q ^ m := zpow_pos (by linarith) m
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hqm.ne'), ← Complex.ofReal_log hqm.le, Real.log_zpow,
    show r ^ (-m) = Complex.exp (Complex.log r) ^ (-m) by rw [Complex.exp_log hr], ← Complex.exp_int_mul]
  congr 1
  have : ((Real.log q : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.log_pos hq).ne'
  push_cast
  field_simp

theorem main (v : HeightOneSpectrum (𝓞 ℚ)) (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (h : ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ u = χ' u) :
    ∃ c : ℂ, ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((χ' a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c) := by

  set ϖ : (v.adicCompletion ℚ)ˣ := uniformizerUnit ℚ v with hϖ
  have hvϖ : Valued.v (ϖ : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := valued_uniformizerUnit ℚ v
  set r : ℂ := ((χ ϖ : ℂˣ) : ℂ) * (((χ' ϖ : ℂˣ) : ℂ))⁻¹ with hr
  have hr0 : r ≠ 0 := mul_ne_zero (Units.ne_zero _) (inv_ne_zero (Units.ne_zero _))

  set q : ℕ := Ideal.absNorm v.asIdeal with hq
  have hq0 : q ≠ 0 := by rw [hq, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot
  have hq1 : q ≠ 1 := by
    rw [hq, Ne, Ideal.absNorm_eq_one_iff]; exact v.isPrime.ne_top
  have hq2 : (1 : ℝ) < q := by
    have : 2 ≤ q := by omega
    exact_mod_cast (lt_of_lt_of_le one_lt_two this)
  have hlogq : Real.log q ≠ 0 := (Real.log_pos hq2).ne'
  refine ⟨Complex.log r / Real.log q, fun a => ?_⟩

  have hva0 : Valued.v (a : v.adicCompletion ℚ) ≠ 0 := (Valuation.ne_zero_iff _).mpr a.ne_zero
  set m : ℤ := Multiplicative.toAdd (WithZero.unzero hva0) with hm
  have hva : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp m := by
    rw [hm]; show _ = ((Multiplicative.ofAdd (Multiplicative.toAdd (WithZero.unzero hva0)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [ofAdd_toAdd, WithZero.coe_unzero]

  set u : (v.adicCompletion ℚ)ˣ := a * ϖ ^ m with hu
  have hvu : Valued.v (u : v.adicCompletion ℚ) = 1 := by
    rw [hu, Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, hva, hvϖ, ← WithZero.exp_zsmul,
      ← WithZero.exp_add, smul_eq_mul, mul_neg, mul_one, add_neg_cancel, WithZero.exp_zero]
  have hu1 : (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ :=
    (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr hvu.le
  have hu2 : ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ := by
    refine (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mpr ?_
    rw [Units.val_inv_eq_inv_val, map_inv₀, hvu, inv_one]
  have hχu := h u hu1 hu2

  have ha : a = u * ϖ ^ (-m) := by rw [hu, mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]

  have hmod : ((modulus (a : v.adicCompletion ℚ) : ℝ)) = (q : ℝ) ^ m := by
    rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v, coe_nnnorm, NumberField.FinitePlace.norm_def,
      WithZeroMulInt.toNNReal_neg_apply _ hva0]
    push_cast
    rfl
  clear_value u m
  have keyU : χ a = χ' a * (χ ϖ * (χ' ϖ)⁻¹) ^ (-m) := by
    rw [ha, map_mul, map_mul, map_zpow, map_zpow, hχu, mul_zpow, inv_zpow, mul_assoc (χ' u),
      mul_comm (χ ϖ ^ (-m)) ((χ' ϖ ^ (-m))⁻¹), ← mul_assoc (χ' ϖ ^ (-m)), mul_inv_cancel, one_mul]
  have key : ((χ a : ℂˣ) : ℂ) = ((χ' a : ℂˣ) : ℂ) * r ^ (-m) := by
    rw [keyU, Units.val_mul, Units.val_zpow_eq_zpow_val, Units.val_mul, Units.val_inv_eq_inv_val]
  rw [key, hmod]
  congr 1
  exact (cpow_aux q hq2 r hr0 m).symm

end Ws31.UnramShift

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ χ' : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (h : ∀ u : (v.adicCompletion ℚ)ˣ, (u : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ u = χ' u) :
    ∃ c : ℂ, ∀ a : (v.adicCompletion ℚ)ˣ,
      ((χ a : ℂˣ) : ℂ) = ((χ' a : ℂˣ) : ℂ) * ((modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ (-c) :=
  Ws31.UnramShift.main v χ χ' h

end S_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_eq_mul_modulus_cpow_of_forall_eq_of_mem_adicCompletionIntegers (solution)
