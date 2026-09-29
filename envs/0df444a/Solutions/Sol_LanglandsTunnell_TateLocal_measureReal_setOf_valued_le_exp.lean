-- Prove2me | solution 1 for LanglandsTunnell.TateLocal.measureReal_setOf_valued_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/bfc0ccaa-e114-58ce-b45e-72eb1af44c09

import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Theorems.Thm_LanglandsTunnell_TateLocal_modulus_adicCompletion_eq_nnnorm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
p2m_attr_erase "instance" "instFiniteResidueFieldAdicCompletionRingOfIntegersWithZeroMultiplicativeInt_definitions NumberField.instCompactSpaceAdicCompletionIntegers Rat.adicCompletion.locallyCompactSpace NumberField.instFiniteResidueFieldAdicCompletionIntegers instWeaklyLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions instLocallyCompactSpaceAdicCompletionRingOfIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instDimensionLEOneSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.instLiesOverSubtypeAdicCompletionMemValuationSubringAdicCompletionIntegersCompletionIdealAsIdeal IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsPrincipalIdealRingSubtypeMemValuationSubringAdicCompletionIntegers_definitions IsDedekindDomain.HeightOneSpectrum.adicCompletion.instIsDiscreteValuationRingSubtypeMemSubringIntegerWithZeroMultiplicativeInt_definitions IsDedekindDomain.HeightOneSpectrum.instIsRankOneDiscreteWithZeroMultiplicativeIntAdicCompletionV_definitions instCountableOfNumberField_definitions"
p2m_attr_erase "simp" "NumberField.StandardAddChar.ratArchLine_apply NumberField.StandardAddChar.AdelicTraceData.mk.sizeOf_spec NumberField.StandardAddChar.AdelicTraceData.mk.injEq AutomorphicForm.whittakerCoefficient_zero AutomorphicForm.CarrierPins.mk.injEq AutomorphicForm.CarrierPins.mk.sizeOf_spec AutomorphicForm.unipotentGL2_zero AutomorphicForm.constantTerm_const AutomorphicForm.constantTerm_zero AutomorphicForm.unipotentGL2_coe NumberField.AdelicTrace.traceDiag_apply NumberField.AdelicTrace.diag_apply"

set_option autoImplicit false

open MeasureTheory IsDedekindDomain NumberField NumberField.AdelicLevel
open scoped NNReal ENNReal Pointwise

noncomputable section

namespace LanglandsTunnell
namespace TateLocal
p2m_export "LanglandsTunnell.TateLocal" "modulus_adicCompletion_eq_nnnorm modulus modulus_of_ne_zero"
namespace BallVolumeV
p2m_open "LanglandsTunnell.TateLocal LanglandsTunnell"

variable {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))

private theorem valued_uniformizerUnit_zpow (m : ℤ) :
    Valued.v ((uniformizerUnit K v ^ m : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-m) := by
  rw [Units.val_zpow_eq_zpow_val, map_zpow₀, valued_uniformizerUnit, ← WithZero.exp_zsmul]
  congr 1
  simp

private theorem ball_eq_smul_integers (k : ℤ) :
    {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ)
          • (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hu : Valued.v ((uniformizerUnit K v ^ (-k) : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp k := by
    rw [valued_uniformizerUnit_zpow, neg_neg]
  have hu' : Valued.v ((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) = WithZero.exp (-k) :=
    valued_uniformizerUnit_zpow v k
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_smul_set, SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers]
  constructor
  · intro hx
    refine ⟨((uniformizerUnit K v ^ k : (v.adicCompletion K)ˣ) : v.adicCompletion K) * x, ?_, ?_⟩
    · rw [map_mul, hu']
      calc WithZero.exp (-k) * Valued.v x ≤ WithZero.exp (-k) * WithZero.exp k := mul_le_mul_right hx _
        _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    · rw [Units.smul_def, smul_eq_mul, ← mul_assoc, ← Units.val_mul, zpow_neg, inv_mul_cancel, Units.val_one, one_mul]
  · rintro ⟨y, hy, rfl⟩
    rw [Units.smul_def, smul_eq_mul, map_mul, hu]
    calc WithZero.exp k * Valued.v y ≤ WithZero.exp k * 1 := mul_le_mul_right hy _
      _ = WithZero.exp k := mul_one _

private theorem main_of_distribHaarChar_uniformizer [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)]
    (hϖ : distribHaarChar (v.adicCompletion K) (uniformizerUnit K v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹)
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
  have hN : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by
    exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hchar : distribHaarChar (v.adicCompletion K) (uniformizerUnit K v ^ (-k))
      = (Ideal.absNorm v.asIdeal : ℝ≥0) ^ k := by
    rw [map_zpow, hϖ, inv_zpow', neg_neg]
  have hμ : μ {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ k : ℝ≥0) * μ (v.adicCompletionIntegers K : Set (v.adicCompletion K)) := by
    rw [ball_eq_smul_integers v k, ← distribHaarChar_mul μ, hchar]
  rw [measureReal_def, measureReal_def, hμ, ENNReal.toReal_mul]
  congr 1

private theorem distribHaarChar_uniformizerUnit [MeasurableSpace (v.adicCompletion K)]
    [BorelSpace (v.adicCompletion K)] :
    distribHaarChar (v.adicCompletion K) (uniformizerUnit K v) = ((Ideal.absNorm v.asIdeal : ℝ≥0))⁻¹ := by
  have h0 : ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K) ≠ 0 := Units.ne_zero _
  have hmod :=
    modulus_adicCompletion_eq_nnnorm K v ((uniformizerUnit K v : (v.adicCompletion K)ˣ) : v.adicCompletion K)
  rw [modulus_of_ne_zero h0, Units.mk0_val] at hmod
  rw [hmod, ← NNReal.coe_inj, coe_nnnorm, NNReal.coe_inv, NNReal.coe_natCast, NumberField.FinitePlace.norm_def,
    valued_uniformizerUnit,
    show (WithZero.exp (-1 : ℤ)) = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
      from rfl,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.coe_ne_zero, WithZero.unzero_coe, toAdd_ofAdd, NNReal.coe_zpow,
    NNReal.coe_natCast, zpow_neg_one]

end LanglandsTunnell.TateLocal.BallVolumeV

end

open MeasureTheory IsDedekindDomain NumberField

open _root_.LanglandsTunnell.TateLocal _root_.P2MW.S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp.LanglandsTunnell.TateLocal in

theorem solution (K : Type) [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) [MeasurableSpace (v.adicCompletion K)] [BorelSpace (v.adicCompletion K)]
    (μ : Measure (v.adicCompletion K)) [μ.IsAddHaarMeasure] (k : ℤ) :
    μ.real {x : v.adicCompletion K | Valued.v x ≤ WithZero.exp k}
      = (Ideal.absNorm v.asIdeal : ℝ) ^ k * μ.real (v.adicCompletionIntegers K : Set (v.adicCompletion K)) :=
  LanglandsTunnell.TateLocal.BallVolumeV.main_of_distribHaarChar_uniformizer v
    (LanglandsTunnell.TateLocal.BallVolumeV.distribHaarChar_uniformizerUnit v) μ k

end S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp
end P2MW
export P2MW.S_LanglandsTunnell_TateLocal_measureReal_setOf_valued_le_exp (solution)
