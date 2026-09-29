-- Prove2me | solution 1 for LanglandsTunnell.CubicInduction.exists_forall_apply_eq_modulus_cpow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/6d4534c4-ad7f-55ca-aaca-8586d0351504

import Definitions.Def_LanglandsTunnell_TateLocalZeta
import Definitions.Def_NumberField_AdelicLevel
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open IsDedekindDomain NumberField
p2m_open "LanglandsTunnell P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow.LanglandsTunnell"

namespace LanglandsTunnell
p2m_export "LanglandsTunnell" "TateLocal.modulus TateLocal.modulus_adicCompletion_eq_nnnorm"
namespace CubicInduction
namespace ModulusPower
p2m_open "LanglandsTunnell"

variable (v : HeightOneSpectrum (𝓞 ℚ))

private theorem one_lt_absNorm : 1 < Ideal.absNorm v.asIdeal := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have h1 : Ideal.absNorm v.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact v.isPrime.ne_top
  omega

private theorem one_lt_absNorm_real : (1 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by
  exact_mod_cast one_lt_absNorm v

private theorem norm_eq_zpow_of_valued {x : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    ‖x‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [NumberField.FinitePlace.norm_def, hx,
    show (WithZero.exp m) = ((Multiplicative.ofAdd m : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow,
    NNReal.coe_natCast]

private theorem coe_modulus_of_valued {x : v.adicCompletion ℚ} {m : ℤ} (hx : Valued.v x = WithZero.exp m) :
    (LanglandsTunnell.TateLocal.modulus x : ℝ) = (Ideal.absNorm v.asIdeal : ℝ) ^ m := by
  rw [LanglandsTunnell.TateLocal.modulus_adicCompletion_eq_nnnorm ℚ v x, coe_nnnorm, norm_eq_zpow_of_valued v hx]

private theorem exists_valued_eq_exp (a : (v.adicCompletion ℚ)ˣ) :
    ∃ m : ℤ, Valued.v (a : v.adicCompletion ℚ) = WithZero.exp m := by
  refine ⟨WithZero.log (Valued.v (a : v.adicCompletion ℚ)), (WithZero.exp_log ?_).symm⟩
  exact (Valuation.ne_zero_iff _).mpr a.ne_zero

private theorem apply_eq_one_of_valued_eq_one (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ t : (v.adicCompletion ℚ)ˣ, (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ t = 1)
    (u : (v.adicCompletion ℚ)ˣ) (hu : Valued.v (u : v.adicCompletion ℚ) = 1) : χ u = 1 := by
  refine hχ u hu.le ?_
  show Valued.v ((u⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ≤ 1
  rw [Units.val_inv_eq_inv_val, map_inv₀, hu, inv_one]

private theorem exists_valued_eq_exp_neg_one :
    ∃ π : (v.adicCompletion ℚ)ˣ, Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ) := by
  obtain ⟨p, hp⟩ := v.valuedAdicCompletion_surjective ℚ (WithZero.exp (-1 : ℤ))
  have hp0 : p ≠ 0 := by
    rintro rfl
    rw [map_zero] at hp
    exact WithZero.exp_ne_zero hp.symm
  exact ⟨Units.mk0 p hp0, hp⟩

private theorem valued_zpow_of_valued_eq_exp_neg_one (π : (v.adicCompletion ℚ)ˣ)
    (hπ : Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ)) (m : ℤ) :
    Valued.v ((π ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, hπ, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem apply_eq_zpow_of_valued (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ t : (v.adicCompletion ℚ)ˣ, (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ t = 1)
    (π : (v.adicCompletion ℚ)ˣ) (hπ : Valued.v (π : v.adicCompletion ℚ) = WithZero.exp (-1 : ℤ))
    (a : (v.adicCompletion ℚ)ˣ) {m : ℤ} (ha : Valued.v (a : v.adicCompletion ℚ) = WithZero.exp m) :
    χ a = χ π ^ (-m) := by
  have hu : Valued.v ((a * π ^ m : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) = 1 := by
    rw [Units.val_mul, map_mul, ha, valued_zpow_of_valued_eq_exp_neg_one v π hπ m, ← WithZero.exp_add,
      add_neg_cancel, WithZero.exp_zero]
  have h1 := apply_eq_one_of_valued_eq_one v χ hχ _ hu
  rw [map_mul, map_zpow] at h1
  rw [zpow_neg]
  exact eq_inv_of_mul_eq_one_left h1

private theorem ofReal_zpow_cpow_eq {N : ℝ} (hN : 1 < N) {z : ℂ} (hz : z ≠ 0) (m : ℤ) :
    (((N ^ m : ℝ)) : ℂ) ^ (Complex.log z⁻¹ / (Real.log N : ℂ)) = z ^ (-m) := by
  have hN0 : 0 < N := zero_lt_one.trans hN
  have hlog : (Real.log N : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos hN).ne'
  have hb : (((N ^ m : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (zpow_pos hN0 m).ne'
  have hs : Complex.exp ((Real.log N : ℂ) * (Complex.log z⁻¹ / (Real.log N : ℂ))) = z⁻¹ := by
    rw [mul_div_cancel₀ _ hlog, Complex.exp_log (inv_ne_zero hz)]
  rw [Complex.cpow_def_of_ne_zero hb, ← Complex.ofReal_log (zpow_pos hN0 m).le, Real.log_zpow]
  conv_rhs => rw [← inv_zpow', ← hs, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

end LanglandsTunnell.CubicInduction.ModulusPower

theorem solution
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : (v.adicCompletion ℚ)ˣ →* ℂˣ)
    (hχ : ∀ t : (v.adicCompletion ℚ)ˣ, (t : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ →
      ((t⁻¹ : (v.adicCompletion ℚ)ˣ) : v.adicCompletion ℚ) ∈ v.adicCompletionIntegers ℚ → χ t = 1) :
    ∃ s₀ : ℂ, ∀ a : (v.adicCompletion ℚ)ˣ,
      ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ≠ 0 ∧
      ((χ a : ℂˣ) : ℂ) = ((LanglandsTunnell.TateLocal.modulus (a : v.adicCompletion ℚ) : ℝ) : ℂ) ^ s₀ := by
  obtain ⟨π, hπ⟩ := LanglandsTunnell.CubicInduction.ModulusPower.exists_valued_eq_exp_neg_one v
  refine ⟨Complex.log ((χ π : ℂˣ) : ℂ)⁻¹ / (Real.log (Ideal.absNorm v.asIdeal : ℝ) : ℂ), fun a => ?_⟩
  obtain ⟨m, hm⟩ := LanglandsTunnell.CubicInduction.ModulusPower.exists_valued_eq_exp v a
  have hN := LanglandsTunnell.CubicInduction.ModulusPower.one_lt_absNorm_real v
  rw [LanglandsTunnell.CubicInduction.ModulusPower.coe_modulus_of_valued v hm]
  refine ⟨Complex.ofReal_ne_zero.mpr (zpow_pos (zero_lt_one.trans hN) m).ne', ?_⟩
  rw [LanglandsTunnell.CubicInduction.ModulusPower.apply_eq_zpow_of_valued v χ hχ π hπ a hm,
    Units.val_zpow_eq_zpow_val,
    LanglandsTunnell.CubicInduction.ModulusPower.ofReal_zpow_cpow_eq hN (Units.ne_zero (χ π)) m]

end S_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow
end P2MW
export P2MW.S_LanglandsTunnell_CubicInduction_exists_forall_apply_eq_modulus_cpow (solution)
