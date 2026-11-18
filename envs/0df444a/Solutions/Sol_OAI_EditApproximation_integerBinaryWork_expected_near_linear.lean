-- Prove2me | solution 1 for OAI.EditApproximation.integerBinaryWork_expected_near_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:47.538311+00:00
-- url     : https://prove2.me/submissions/6ecbb9ad-ac3b-4edf-a72b-79c7650ce73d

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Data.Int.Log
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Nat.Size
import Mathlib.Data.Rat.Lemmas
import Mathlib.Logic.Equiv.Nat
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.Integration
import Mathlib.Tactic
import Definitions.Def_EditApproxScheme_01
import Definitions.Def_EditApproxScheme_02
import Definitions.Def_EditApproxScheme_03
import Definitions.Def_EditApproxScheme_04
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedExecutionTotalWork_expected_near_linear
import Theorems.Thm_OAI_EditApproximation_computedQueryLocalWork_cap
import Theorems.Thm_OAI_EditApproximation_computedQuerySetupWithWork_cost
import Theorems.Thm_OAI_EditApproximation_integerBinaryOutput_cost
import Theorems.Thm_OAI_EditApproximation_integerPreevaluationWork_near_linear

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerSymbols
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Integer word labels are encoded injectively using a sign bit. The
encoding preserves the actual unit-cost edit distance and takes one
linear pass; no constant-alphabet hypothesis is used. -/

namespace EditApproximation



theorem integerSymbolCode_bound (z : ℤ) : integerSymbolCode z ≤ 2 * z.natAbs := by
  cases z <;> simp only [integerSymbolCode, Int.natAbs] <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSampling
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Exact fair-bit sampling of the optimizer mixture

The finite-word rejection calculation follows Section 9.
The random trial is encoded from actual Boolean bits. First-success trace
probabilities determine the output law and expected number of trials.
-/

namespace EditApproximation

open Finset

theorem rejectionFailureProbability_range (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    0 ≤ rejectionFailureProbability N R ∧ rejectionFailureProbability N R < 1 := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  constructor
  · unfold rejectionFailureProbability
    positivity
  · unfold rejectionFailureProbability
    rw [div_lt_one hR, Nat.cast_sub hNR]
    have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
    linarith

/-- The actual first-success trace law has expected trial count `R/N`;
this identifies the tail-sum calculation with the terminating executions. -/
theorem rejection_first_success_expected_trials (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * N *
      (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R))) ((R : ℝ) / N) := by
  have hR : (0 : ℝ) < R := by exact_mod_cast hN.trans_le hNR
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hq := rejectionFailureProbability_range N R hN hNR
  have hnorm : ‖rejectionFailureProbability N R‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg hq.1]
    exact hq.2
  have hseries := ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).add
    (hasSum_geometric_of_lt_one hq.1 hq.2)).mul_right ((N : ℝ) / R)
  have hterm (n : ℕ) :
      ((n : ℝ) * rejectionFailureProbability N R ^ n + rejectionFailureProbability N R ^ n) *
          ((N : ℝ) / R) =
        ((n : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ n / ((R : ℝ) ^ n * R)) := by
    simp only [rejectionFailureProbability, div_pow]
    ring
  have hratio : 1 - rejectionFailureProbability N R = (N : ℝ) / R := by
    unfold rejectionFailureProbability
    rw [Nat.cast_sub hNR]
    field_simp
    ring
  have hsum : (rejectionFailureProbability N R / (1 - rejectionFailureProbability N R) ^ 2 +
        (1 - rejectionFailureProbability N R)⁻¹) * ((N : ℝ) / R) = (R : ℝ) / N := by
    rw [hratio]
    have hqeq : rejectionFailureProbability N R = 1 - (N : ℝ) / R := by linarith [hratio]
    rw [hqeq]
    field_simp [hR.ne', hNreal.ne']
    ring
  simpa only [hterm, hsum] using hseries

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Integer-computed parameters

The logarithms and fourth roots in Section 2 are computed by natural bit
lengths and nested integer square roots. No real arithmetic oracle is
used to form the algorithm's parameters.
-/

namespace EditApproximation
















theorem inputHeight_covers_length (N : ℕ) : N + 2 ≤ 2 ^ inputHeight N := by
  have hlog := Nat.le_pow_clog (by decide : 1 < 2) (N + 2)
  have hheight := Nat.le_pow_clog (by decide : 1 < 2) (Nat.clog 2 (N + 2))
  exact hlog.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hheight)

theorem inputSmallLog_bounds (N : ℕ) (hN : 0 < N) :
    heightExponent N ≤ inputSmallLog N ∧ inputSmallLog N < 2 * heightExponent N := by
  have hpos := heightExponent_pos N hN
  have hone : 1 ≤ heightExponent N := hpos
  have hrange := rejectionWord_range (heightExponent N) hpos
  simpa only [inputSmallLog, smallLogExponent, rejectionBitCount, max_eq_right hone] using hrange

theorem coarseExponent_fourth_power (ell : ℕ) :
    coarseExponent ell ^ 4 ≤ Nat.log 2 ell := by
  have ha := Nat.sqrt_le' (Nat.sqrt (Nat.log 2 ell))
  have hb := Nat.sqrt_le' (Nat.log 2 ell)
  have hsq := Nat.pow_le_pow_left ha 2
  rw [← pow_mul] at hsq
  exact hsq.trans hb

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual earlier-input cover satisfies the polynomial branching
budget at every seed, after substituting the computed time and grid
parameters. -/

namespace EditApproximation

theorem computed_smallLog_le_height (N : ℕ) : inputSmallLog N ≤ inputHeight N := by
  have hf : smallLogExponent N ≤ heightExponent N := by
    unfold smallLogExponent
    apply Nat.clog_le_of_le_pow
    exact max_le Nat.one_le_two_pow (heightExponent N).lt_two_pow_self.le
  exact pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hf

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyCutoff
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem largeAccuracyInput_pos (N : ℕ) (epsilon : ℚ) (h : largeAccuracyInput N epsilon) : 0 < N := by
  have htwo : 2 ≤ (2 : ℕ) ^ 1000 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 1 ≤ 1000)
  have hell : 2 ≤ inputSmallLog N := htwo.trans h.1
  by_contra hn
  have hzero : N = 0 := Nat.eq_zero_of_not_pos hn
  rw [hzero] at hell
  norm_num [inputSmallLog, smallLogExponent, heightExponent] at hell

theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

theorem accuracyCutoff_sufficient (N : ℕ) (epsilon : ℚ) (hepsilon : 0 < epsilon)
    (hN : accuracyCutoff epsilon ≤ N) : largeAccuracyInput N epsilon := by
  have hpositive : 0 < N := (Nat.two_pow_pos _).trans_le hN
  have he : accuracyCutoffExponent epsilon ≤ inputSmallLog N :=
    (heightExponent_above_double_power N (accuracyCutoffExponent epsilon) hN).trans
      (inputSmallLog_bounds N hpositive).1
  constructor
  · exact (le_max_left _ _).trans he
  · have hc : (10 / epsilon : ℚ) ≤ (inputSmallLog N : ℚ) :=
      (Nat.le_ceil _).trans (Nat.cast_le.mpr ((le_max_right _ _).trans he))
    exact (div_le_iff₀ hepsilon).mp hc

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Growth of the computed parameters

These are scalar estimates for the literal integer parameters of Section 10.
They do not assert an evaluator cost: the recursive-input and charged local
work bounds must be connected to these estimates separately.
-/

namespace EditApproximation

open Filter
open scoped Topology

theorem heightExponent_tendsto : Tendsto heightExponent atTop atTop := by
  refine tendsto_atTop.2 fun b => ?_
  filter_upwards [eventually_ge_atTop (2 ^ (2 ^ b))] with N hN
  exact heightExponent_above_double_power N b hN

theorem inputSmallLog_tendsto : Tendsto inputSmallLog atTop atTop := by
  apply tendsto_atTop_mono' atTop _ heightExponent_tendsto
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (inputSmallLog_bounds N hN).1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar bounds for the local enumeration exponent. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem inputHeight_real_tendsto :
    Tendsto (fun N => (inputHeight N : ℝ)) atTop atTop := by
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Function.comp_def] using
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).comp heightExponent_tendsto

/-- Every fixed polynomial in the computed small logarithm is negligible
relative to the computed height. -/
theorem smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => (2 : ℝ) ^ k *
      ((heightExponent N : ℝ) ^ k / (2 : ℝ) ^ heightExponent N)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, mul_zero] using
      ((tendsto_pow_const_div_const_pow_of_one_lt k (by norm_num : (1 : ℝ) < 2)).comp
        heightExponent_tendsto).const_mul ((2 : ℝ) ^ k)
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (pow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hbound : (inputSmallLog N : ℝ) ≤ 2 * (heightExponent N : ℝ) := by
    exact_mod_cast (inputSmallLog_bounds N hN).2.le
  have hpower := pow_le_pow_left₀ (Nat.cast_nonneg (inputSmallLog N)) hbound k
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, mul_pow, mul_div_assoc] using
    div_le_div_of_nonneg_right hpower (by positivity : (0 : ℝ) ≤ 2 ^ heightExponent N)

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

theorem height_log_sandwich (N : ℕ) (hN : 0 < N) :
    Real.log (N + 2 : ℝ) / Real.log 2 ≤ inputHeight N ∧
      (inputHeight N : ℝ) ≤ (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hcover : (N + 2 : ℝ) ≤ (2 : ℝ) ^ inputHeight N := by
    exact_mod_cast inputHeight_covers_length N
  have hlower := Real.log_le_log (by positivity : (0 : ℝ) < N + 2) hcover
  rw [Real.log_pow] at hlower
  have hL : 1 < Nat.clog 2 (N + 2) := by
    exact (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).2 (by norm_num; omega)
  have hpred := Nat.pow_pred_clog_lt_self (by decide : 1 < (2 : ℕ))
    (by omega : 1 < N + 2)
  have hpredR : (2 : ℝ) ^ (Nat.clog 2 (N + 2)).pred < N + 2 := by exact_mod_cast hpred
  have hpredlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (Nat.clog 2 (N + 2)).pred) hpredR
  rw [Real.log_pow] at hpredlog
  have hpredcast : ((Nat.clog 2 (N + 2)).pred : ℝ) = (Nat.clog 2 (N + 2) : ℝ) - 1 := by
    have hnat : (Nat.clog 2 (N + 2)).pred + 1 = Nat.clog 2 (N + 2) :=
      Nat.succ_pred_eq_of_pos (by omega)
    have hcast : ((Nat.clog 2 (N + 2)).pred : ℝ) + 1 = (Nat.clog 2 (N + 2) : ℝ) := by
      exact_mod_cast hnat
    linarith
  rw [hpredcast] at hpredlog
  have hH : (inputHeight N : ℝ) < 2 * (Nat.clog 2 (N + 2) : ℝ) := by
    have h := (rejectionWord_range (Nat.clog 2 (N + 2)) (by omega)).2
    simpa only [inputHeight, heightExponent, rejectionBitCount, Nat.cast_pow,
      Nat.cast_mul, Nat.cast_ofNat] using (Nat.cast_lt.mpr h :
      ((2 ^ rejectionBitCount (Nat.clog 2 (N + 2)) : ℕ) : ℝ) <
        ((2 * Nat.clog 2 (N + 2) : ℕ) : ℝ))
  have hlogN : Real.log 2 ≤ Real.log (N + 2 : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ N + 2))
  constructor
  · exact (div_le_iff₀ hlogtwo).2 hlower
  · have hproduct : (inputHeight N : ℝ) * Real.log 2 ≤ 4 * Real.log (N + 2 : ℝ) := by
      have hmul := mul_le_mul_of_nonneg_right hH.le hlogtwo.le
      nlinarith
    calc
      (inputHeight N : ℝ) ≤ (4 * Real.log (N + 2 : ℝ)) / Real.log 2 :=
        (le_div_iff₀ hlogtwo).2 hproduct
      _ = (4 / Real.log 2) * Real.log (N + 2 : ℝ) := by ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Numerics_NumericalWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Concrete numerical representation and arithmetic work

These are integer bit-length and exact rational-operation bounds for the
finite optimizer. They are not a RAM theorem: the costed evaluator below
counts rational arithmetic operations, while bit-operation costs also
require the charged evaluation model used by the surrounding algorithm.
-/

namespace EditApproximation

open Finset

theorem natural_product_bit_length (a b : ℕ) :
    Nat.size (a * b) ≤ Nat.size a + Nat.size b := by
  apply Nat.size_le.mpr
  calc
    a * b ≤ a * 2 ^ Nat.size b := Nat.mul_le_mul_left a (Nat.lt_size_self b).le
    _ < 2 ^ Nat.size a * 2 ^ Nat.size b :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity)
    _ = 2 ^ (Nat.size a + Nat.size b) := (pow_add _ _ _).symm

theorem natural_power_bit_length (a n : ℕ) :
    Nat.size (a ^ n) ≤ n * Nat.size a + 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have hmul := natural_product_bit_length (a ^ n) a
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! All-seed numerical dimension and source-range bounds after substituting
the computed grid size. These bounds do not use an accuracy event. -/

namespace EditApproximation

theorem wide_coordinate_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    M * (40 * P + 2) ^ 2 ≤ H ^ (2 * p + 45) := by
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    have hconstant : 42 ≤ H ^ 2 := by nlinarith
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul hconstant hPcap
      _ = H ^ (2 + (p + 20)) := (pow_add H 2 (p + 20)).symm
      _ = _ := by congr 1; omega
  calc
    _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul hM (Nat.pow_le_pow_left hbox 2)
    _ = H * H ^ ((p + 22) * 2) := by rw [pow_mul]
    _ = H ^ ((p + 22) * 2 + 1) := (pow_succ' H _).symm
    _ = _ := by congr 1; omega

theorem optimizer_parameter_budget_le (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    H + M * (40 * P + 2) ^ 2 + 4 ≤ H ^ (2 * p + 46) := by
  have hdimension := wide_coordinate_budget_le H M P p hH hM hP hPcap
  have hlarge : H ≤ H ^ (2 * p + 45) := Nat.le_pow (by omega)
  have hfour : 4 ≤ H ^ (2 * p + 45) := (by omega : 4 ≤ H).trans hlarge
  calc
    _ ≤ 3 * H ^ (2 * p + 45) := by omega
    _ ≤ H * H ^ (2 * p + 45) := Nat.mul_le_mul_right _ (by omega)
    _ = H ^ (2 * p + 45 + 1) := (pow_succ' H _).symm
    _ = _ := rfl

theorem optimizerTriangularMass_le_square (K : ℕ) : optimizerTriangularMass K ≤ K ^ 2 := by
  have htwice := optimizerTriangularMass_twice K
  have hpower : K ≤ K ^ 2 := Nat.le_pow (by decide)
  nlinarith only [htwice, hpower]

theorem localOnlineMassBound_polynomial (H M P p : ℕ) (hH : 64 ≤ H) (hM : M ≤ H)
    (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    localOnlineMassBound M P H ≤ H ^ (8000 * (p + 1)) := by
  have hG : H + M * (40 * P + 2) ^ 2 + 2 ≤ H ^ (2 * p + 46) :=
    (by omega : H + M * (40 * P + 2) ^ 2 + 2 ≤ H + M * (40 * P + 2) ^ 2 + 4).trans
      (optimizer_parameter_budget_le H M P p hH hM hP hPcap)
  calc
    _ ≤ ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ^ 2 := optimizerTriangularMass_le_square _
    _ = (H + M * (40 * P + 2) ^ 2 + 2) ^ (80 * 2) := (pow_mul _ 80 2).symm
    _ ≤ (H ^ (2 * p + 46)) ^ (80 * 2) := Nat.pow_le_pow_left hG _
    _ = H ^ ((2 * p + 46) * (80 * 2)) := (pow_mul H _ _).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

theorem computed_localOnlineMassBound_polynomial (N : ℕ) (hH : 64 ≤ inputHeight N) :
    localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N) ≤
      inputHeight N ^ (8000 * (coarseExponent (inputSmallLog N) + 1)) := by
  apply localOnlineMassBound_polynomial _ _ _ _ hH
  · exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  · exact Nat.one_le_pow _ _ (by omega)
  · exact le_rfl

theorem computed_localOnlineMassBound_bits (N : ℕ) (hH : 64 ≤ inputHeight N) :
    Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
      8000 * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 :=
  (Nat.size_le_size (computed_localOnlineMassBound_polynomial N hH)).trans
    (natural_power_bit_length _ _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual uniform source-range address fits in one logarithmic input
word eventually. The coefficient can be any fixed natural number. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computed_sourceAddressBits_div_height_tendsto (C : ℕ) :
    Tendsto (fun N =>
      ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) /
        inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (4 * (C : ℝ) + 1)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have he := (inputSmallLog_bounds N hN).1
  have hp := coarseExponent_le_smallLog N
  have hell : 1 ≤ inputSmallLog N := Nat.one_le_two_pow
  have hs : Nat.size (inputHeight N) = heightExponent N + 1 := by
    simp only [inputHeight, Nat.size_pow]
  have hsmall : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast hell
  have hpR : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show coarseExponent (inputSmallLog N) + 1 ≤ 2 * inputSmallLog N by omega)
  have hsR : (Nat.size (inputHeight N) : ℝ) ≤ 2 * inputSmallLog N := by
    exact_mod_cast (show Nat.size (inputHeight N) ≤ 2 * inputSmallLog N by omega)
  have hproduct := mul_le_mul hpR hsR (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hscaled := mul_le_mul_of_nonneg_left hproduct (Nat.cast_nonneg C : (0 : ℝ) ≤ C)
  have hnum : ((C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 : ℕ) : ℝ) ≤
      (4 * (C : ℝ) + 1) * (inputSmallLog N : ℝ) ^ 2 := by
    push_cast
    nlinarith only [hscaled, hsmall, sq_nonneg ((inputSmallLog N : ℝ) - 1)]
  have h := div_le_div_of_nonneg_right hnum (Nat.cast_nonneg (inputHeight N) : (0 : ℝ) ≤ inputHeight N)
  simpa only [mul_div_assoc] using h

theorem computed_sourceAddressBits_le_height (C : ℕ) :
    ∀ᶠ N in atTop,
      C * (coarseExponent (inputSmallLog N) + 1) * Nat.size (inputHeight N) + 1 ≤ inputHeight N := by
  filter_upwards [(computed_sourceAddressBits_div_height_tendsto C).eventually
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))] with N h
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hlt := (div_lt_one hH).mp h
  exact_mod_cast hlt.le

theorem computed_localOnlineMassBound_word :
    ∀ᶠ N in atTop,
      Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N)) ≤
        inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000,
    inputHeight_real_tendsto.eventually (eventually_ge_atTop 64)] with N hbits hH
  have hHnat : 64 ≤ inputHeight N := by exact_mod_cast hH
  exact (computed_localOnlineMassBound_bits N hHnat).trans hbits

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionRuntimeLaw
attribute [-instance] _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A probability law for terminating fair-word rejection executions.
It records the failed trial count and accepted integer, identifies their
joint masses with literal finite fair-word traces, and charges all trials. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory



theorem rejectionSuccessParameter_ne_zero (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    rejectionSuccessParameter N R hN hNR ≠ 0 := by
  intro h
  have heq := congrArg (fun p : unitInterval => (p : ℝ)) h
  have hpos : (0 : ℝ) < (N : ℝ) / R :=
    div_pos (by exact_mod_cast hN) (by exact_mod_cast hN.trans_le hNR)
  change (N : ℝ) / R = 0 at heq
  linarith

theorem rejectionSuccessParameter_complement (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    1 - (rejectionSuccessParameter N R hN hNR : ℝ) = ((R - N : ℕ) : ℝ) / R := by
  change 1 - (N : ℝ) / R = _
  rw [Nat.cast_sub hNR]
  have hR : (R : ℝ) ≠ 0 := by exact_mod_cast (hN.trans_le hNR).ne'
  field_simp [hR]

theorem rejection_trials_integrable (N R : ℕ) (hN : 0 < N) (hNR : N ≤ R) :
    Integrable (fun failures : ℕ => (failures : ℝ) + 1)
      (geometricMeasure (rejectionSuccessParameter N R hN hNR)) := by
  apply (integrable_geometricMeasure_iff (rejectionSuccessParameter_ne_zero N R hN hNR)).mpr
  have hterm (k : ℕ) :
      (1 - (rejectionSuccessParameter N R hN hNR : ℝ)) ^ k *
        (rejectionSuccessParameter N R hN hNR : ℝ) * ‖(k : ℝ) + 1‖ =
      ((k : ℝ) + 1) * N * (((R - N : ℕ) : ℝ) ^ k / ((R : ℝ) ^ k * R)) := by
    rw [Real.norm_of_nonneg (by positivity), rejectionSuccessParameter_complement]
    change (((R - N : ℕ) : ℝ) / R) ^ k * ((N : ℝ) / R) * ((k : ℝ) + 1) = _
    rw [div_pow]
    ring
  simpa only [hterm] using (rejection_first_success_expected_trials N R hN hNR).summable


end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_RejectionSelectedCost
attribute [-instance] _root_.OAI.EditApproximation.coarseFullSeedMeasure_isProbabilityMeasure _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.parentDrawLaw_probability _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalCommonCoordinateLaw_probability _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalCommonLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalScalarLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Rejection counts are independent of all accepted values. Thus even
an adaptive choice of coordinates incurs fewer than two word trials per
selected coordinate in expectation. No unused source is charged. -/

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Selected

variable {ι : Type*} [Fintype ι] (range : ι → ℕ) [∀ i, NeZero (range i)]



 theorem rejectionRuntimeArrayLaw_accepted :
    (rejectionRuntimeArrayLaw range).map Prod.snd = rejectionAcceptedLaw range := by
  unfold rejectionRuntimeArrayLaw
  simp



 theorem rejectionFailureArray_bits_integrable (i : ι) :
    Integrable (fun failures : ι → ℕ => ((failures i : ℝ) + 1) * rejectionBitCount (range i))
      (Measure.pi (rejectionFailureLaw range)) := by
  apply integrable_comp_eval (X := fun _ : ι => ℕ) (μ := rejectionFailureLaw range) (i := i)
    (f := fun failures : ℕ => ((failures : ℝ) + 1) * rejectionBitCount (range i))
  exact (rejection_trials_integrable (range i) (2 ^ rejectionBitCount (range i))
    (Nat.pos_of_ne_zero (NeZero.ne (range i)))
    (rejectionWord_range (range i) (Nat.pos_of_ne_zero (NeZero.ne (range i)))).1).mul_const _

 theorem rejectionSelectedBits_integrable (selected : ι → (∀ i, Fin (range i)) → Prop) :
    Integrable (rejectionSelectedBits range selected) (rejectionRuntimeArrayLaw range) := by
  classical
  unfold rejectionSelectedBits rejectionRuntimeArrayLaw
  apply integrable_finsetSum
  intro i _
  exact (rejectionFailureArray_bits_integrable range i).mul_prod (Integrable.of_finite (μ := rejectionAcceptedLaw range)
    (f := fun accepted => selectionIndicator (selected i accepted)))

end Selected

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_AccuracyPrefixInspection
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_width _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The uniform program inspects only a logarithmically bounded prefix
of each accuracy word. An encoding exceeding this bound takes the exact
fallback, without first scanning or retaining its unbounded suffix. -/

namespace EditApproximation

/-- One step reads a constructor of the input word. -/


 theorem inspectBitPrefix_accepts (budget : ℕ) (word : List Bool) :
    (inspectBitPrefix budget word).1 = true ↔ word.length ≤ budget := by
  induction budget generalizing word with
  | zero => cases word <;> simp [inspectBitPrefix]
  | succ budget ih =>
    cases word with
    | nil => simp [inspectBitPrefix]
    | cons bit rest => simpa only [inspectBitPrefix, List.length_cons, Nat.add_le_add_iff_right] using ih rest

/-- On acceptance the input words are already bounded; returning the
input value only retains those bounded words. -/


 theorem inspectAccuracyWithWork_spec (budget : ℕ) (epsilon : BinaryFraction) :
    (inspectAccuracyWithWork budget epsilon).1 =
      if epsilon.width ≤ budget then some epsilon else none := by
  simp only [inspectAccuracyWithWork, BinaryFraction.width, max_le_iff]
  by_cases hn : epsilon.numerator.bits.length ≤ budget <;>
    by_cases hd : epsilon.denominator.length ≤ budget
  all_goals
    have hnum := inspectBitPrefix_accepts budget epsilon.numerator.bits
    have hden := inspectBitPrefix_accepts budget epsilon.denominator
    simp_all

 theorem inspectAccuracy_eventually_accepts (epsilon : BinaryFraction) :
    ∀ᶠ N in Filter.atTop, (inspectAccuracyWithWork (inputHeight N) epsilon).1 = some epsilon := by
  filter_upwards [inputSmallLog_tendsto.eventually (Filter.eventually_ge_atTop epsilon.width)] with N hN
  rw [inspectAccuracyWithWork_spec, ite_eq_left (hN.trans (computed_smallLog_le_height N))]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUniformAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

/-- Every test is on a bounded word prefix or on the computed input
parameters. Rejected inputs use the exact suffix dynamic program. -/




 theorem physicalLargeInput_eventually (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value) :
    ∀ᶠ N in atTop, physicalLargeInput N epsilon := by
  filter_upwards [inspectAccuracy_eventually_accepts epsilon,
    eventually_ge_atTop (accuracyCutoff epsilon.value), computed_localOnlineMassBound_word] with N hi hc hw
  exact ⟨by rw [hi]; rfl, accuracyCutoff_sufficient N epsilon.value hepsilon hc, hw⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCacheWords
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Explicit multiword cache storage after substituting the computed height. -/

namespace EditApproximation

theorem computed_input_size_le_height (N : ℕ) : Nat.size N ≤ inputHeight N := by
  apply Nat.size_le.mpr
  exact (show N < N + 2 by omega).trans_le (inputHeight_covers_length N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SubexponentialTransfer
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Conversion from the computed-height bounds to asymptotics in the actual
input length. The bounds concern scalar envelopes, not an uncharged program. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem subexponential_height_to_input (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, Real.exp (f N) ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlogtwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := hf.eventually (gt_mem_nhds
    (show (0 : ℝ) < epsilon * Real.log 2 / 4 by positivity))
  filter_upwards [hsmall, eventually_ge_atTop 1] with N hsmall hN
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hfN : f N ≤ (epsilon * Real.log 2 / 4) * inputHeight N :=
    ((div_lt_iff₀ hH).1 hsmall).le
  have hheight := (height_log_sandwich N hN).2
  have hscaled := mul_le_mul_of_nonneg_left hheight
    (show (0 : ℝ) ≤ epsilon * Real.log 2 / 4 by positivity)
  have hcancel : (epsilon * Real.log 2 / 4) *
      ((4 / Real.log 2) * Real.log (N + 2 : ℝ)) = epsilon * Real.log (N + 2 : ℝ) := by
    field_simp [hlogtwo.ne']
  have hexponent : f N ≤ epsilon * Real.log (N + 2 : ℝ) :=
    hfN.trans (hscaled.trans_eq hcancel)
  rw [Real.rpow_def_of_pos (by positivity : (0 : ℝ) < N + 2)]
  apply Real.exp_le_exp.mpr
  simpa only [mul_comm] using hexponent

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_DependencyPathEnvelope
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! An explicit subpolynomial envelope for the finite dependency-path sum.
The connection between this sum and an execution is a separate obligation. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem nat_pow_eq_exp_log (a n : ℕ) (ha : 0 < a) :
    (a : ℝ) ^ n = Real.exp ((n : ℝ) * Real.log a) := by
  rw [Real.exp_nat_mul, Real.exp_log (by exact_mod_cast ha)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyRejectionWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory

section Work

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H : ℕ)

local notation "SeedState" => ClampedPhysicalSeed M J target.length N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "passes" => computedSeedPassCount N
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S
local notation "FamilyRange" => physicalFamilyRange (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)



 theorem physicalFamilyMemoBits_integrable (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ) (rootQ : TargetInterval target.length) (seed : SeedState) :
    Integrable (physicalFamilyMemoBits source target N P T S H hH bits encode rootQ seed)
      (rejectionRuntimeArrayLaw FamilyRange) := rejectionSelectedBits_integrable _ _

end Work

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarseExecution
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory

section Execution
variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P H B : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)





variable [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]

omit [NeZero M] [NeZero R] [NeZero B] in
 theorem physicalCoarseExecutionProjection_measurable :
    Measurable (physicalCoarseExecutionProjection (R := R) source target N P H B depth) := by
  unfold physicalCoarseExecutionProjection
  exact ((measurable_of_finite (physicalCoarseSeedTable source target N B depth)).comp
    measurable_fst).prodMk measurable_snd

omit [NeZero R] in
 theorem physicalCoarseExecutionProjection_law :
    (physicalCoarseExecutionLaw (R := R) source target N P H B depth).map
      (physicalCoarseExecutionProjection (R := R) source target N P H B depth) =
    physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth) := by
  unfold physicalCoarseExecutionLaw physicalCoarseExecutionProjection physicalFamilyRuntimeLaw
  change ((_ : Measure (PhysicalCoarseDraw source target B depth)).prod _).map
    (Prod.map (physicalCoarseSeedTable source target N B depth) id) = _
  rw [← Measure.map_prod_map _ _ (measurable_of_finite _) measurable_id, Measure.map_id]
  rfl

end Execution
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionLaw
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The coarse sampler execution and its returned seed share one probability space. -/

namespace EditApproximation

open MeasureTheory








 theorem computedExecutionProjection_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionProjection source target N) :=
  physicalCoarseExecutionProjection_measurable source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)

 theorem computedExecutionProjection_law (source target : List ℕ) (N : ℕ) :
    (computedExecutionLaw source target N).map (computedExecutionProjection source target N) =
      physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) (physicalCoarseSeedLaw (M := (integerParameters N).M)
          (J := intervalTreeDepth (integerParameters N).M source.length) source target N (integerParameters N).B
          (computedPhysicalCoarseDepth source target N)) :=
  physicalCoarseExecutionProjection_law source target N (integerParameters N).P
    (inputHeight N) (integerParameters N).B (computedPhysicalCoarseDepth source target N)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerOccurrenceIndex
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Uniform input preparation chooses dictionary widths from the actual
integer words. No alphabet size or polynomial exponent is an algorithm input. -/

namespace EditApproximation



theorem integerMagnitude_mem (zs : List ℤ) (z : ℤ) (hz : z ∈ zs) :
    z.natAbs ≤ integerMagnitude zs := by
  induction zs with
  | nil => simp at hz
  | cons a zs ih =>
    rcases List.mem_cons.mp hz with rfl | hz
    · exact le_max_left _ _
    · exact (ih hz).trans (le_max_right _ _)

theorem integerMagnitude_le (zs : List ℤ) (B : ℕ) (h : ∀ z ∈ zs, z.natAbs ≤ B) :
    integerMagnitude zs ≤ B := by
  induction zs with
  | nil => exact Nat.zero_le _
  | cons z zs ih =>
    exact max_le (h z List.mem_cons_self) (ih fun a ha => h a (List.mem_cons_of_mem _ ha))





theorem integerInputSymbolBits_fits (source target : List ℤ) (z : ℤ)
    (hz : z ∈ source ++ target) :
    integerSymbolCode z < 2 ^ integerInputSymbolBits source target := by
  exact ((integerSymbolCode_bound z).trans
    (Nat.mul_le_mul_left 2 (integerMagnitude_mem _ z hz))).trans_lt (Nat.lt_size_self _)

theorem integerInputSymbolBits_le (source target : List ℤ) (B : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ B) :
    integerInputSymbolBits source target ≤ Nat.size (2 * B) :=
  Nat.size_le_size (Nat.mul_le_mul_left 2 (integerMagnitude_le _ B h))



/-- Polynomially bounded input words produce logarithmic dictionary keys;
the polynomial degree is only an analysis parameter. -/
theorem integerInputSymbolBits_polynomial (source target : List ℤ) (N C : ℕ)
    (h : ∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) :
    integerInputSymbolBits source target ≤ C * Nat.size (N + 2) + 3 := by
  have hbits := integerInputSymbolBits_le source target ((N + 2) ^ C) h
  have hmul := natural_product_bit_length 2 ((N + 2) ^ C)
  have hpow := natural_power_bit_length (N + 2) C
  have htwo : Nat.size 2 = 2 := by decide
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerPreprocessing
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter
open scoped Topology



/-- Scans, integer encoding, indexed occurrence preprocessing and the
exact equality guard are charged before the local evaluator starts. -/


 theorem input_length_bits_le (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 := by
  apply Nat.size_le.mpr
  exact (inputHeight_covers_length N).trans_lt
    (Nat.pow_lt_pow_right (by decide : 1 < 2) (Nat.lt_succ_self _))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_HeightPowerWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 theorem fixed_height_power_subpolynomial (k : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, (inputHeight N : ℝ) ^ k ≤ (N + 2 : ℝ) ^ epsilon := by
  have hlog : Tendsto (fun N : ℕ => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (k : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((k : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1 <;> first | (with_reducible_and_instances rfl) | (ext N; ring)
  filter_upwards [subexponential_height_to_input _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) k (Nat.two_pow_pos _)] at hN

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerCoarseSymbolBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem integer_encoded_symbol_bits (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ,
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ a ∈ source.map integerSymbolCode ++ target.map integerSymbolCode,
        Nat.size a ≤ inputHeight N ^ 3 := by
  filter_upwards [inputHeight_real_tendsto.eventually
    (eventually_ge_atTop ((max 100 C : ℕ) : ℝ))] with N hH
  have hH' : max 100 C ≤ inputHeight N := by exact_mod_cast hH
  intro source target halphabet a ha
  rw [← List.map_append] at ha
  obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
  have hcode : Nat.size (integerSymbolCode z) ≤ integerInputSymbolBits source target :=
    Nat.size_le.mpr (integerInputSymbolBits_fits source target z hz)
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hn := input_length_bits_le N
  have hCH := Nat.mul_le_mul (show C ≤ inputHeight N by omega) hn
  have hcube : 100 * inputHeight N ^ 2 ≤ inputHeight N ^ 3 := by
    have hm := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 100 ≤ inputHeight N by omega)
    nlinarith only [hm]
  have h100 : 100 ≤ inputHeight N := by omega
  nlinarith only [hcode, hs, hCH, hcube, h100]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteProductWork
attribute [-instance] _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCommonCoordinateMeasurable _root_.OAI.EditApproximation.physicalCommonCoordinateSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The executed sampler law supports both selected rejection work and
work depending only on the accepted finite draws. -/

namespace EditApproximation
open MeasureTheory

 theorem finite_outer_integrable {α β : Type*} [Fintype α] [Countable β]
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (μ : Measure α) [IsFiniteMeasure μ] (ν : Measure β) [SFinite ν]
    (f : α × β → ℝ) (hsections : ∀ a, Integrable (fun b => f (a, b)) ν) :
    Integrable f (μ.prod ν) := by
  apply (integrable_prod_iff (measurable_of_countable f).aestronglyMeasurable).2
  exact ⟨Filter.Eventually.of_forall hsections, Integrable.of_finite⟩

section Accepted
variable {α ι : Type*} [Fintype α] [Fintype ι]
  [MeasurableSpace α] [MeasurableSingletonClass α]
  (range : ι → ℕ) [∀ i, NeZero (range i)]
  (μ : Measure α) [IsFiniteMeasure μ]

omit [Fintype α] [Fintype ι] [MeasurableSingletonClass α] [∀ i, NeZero (range i)] in
 theorem rejectionProductAccepted_measurable : Measurable (rejectionProductAccepted (α := α) range) :=
  measurable_fst.prodMk (measurable_snd.comp measurable_snd)

omit [MeasurableSingletonClass α] [IsFiniteMeasure μ] in
 theorem rejectionProductAccepted_law :
    (μ.prod (rejectionRuntimeArrayLaw range)).map (rejectionProductAccepted range) =
      μ.prod (rejectionAcceptedLaw range) := by
  change (μ.prod _).map (Prod.map id Prod.snd) = _
  rw [← Measure.map_prod_map _ _ measurable_id measurable_snd, Measure.map_id,
    rejectionRuntimeArrayLaw_accepted]

end Accepted
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter





 theorem computedFamilyRejectionWork_integrable (source target : List ℕ) (N : ℕ)
    (seed : ComputedFamilySeed source target N) :
    Integrable (fun execution : ComputedRejectionRuntime source target N =>
      computedFamilyRejectionWork source target N (seed, execution))
      (rejectionRuntimeArrayLaw (physicalFamilyRange (M := (integerParameters N).M)
        (J := intervalTreeDepth (integerParameters N).M source.length) (R := inputHeight N ^ 2)
        target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))) :=
  physicalFamilyMemoBits_integrable source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (finalTargetState target.length) seed

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedJointCoarseWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



 theorem symbolicComputedExecutionCoarseWork_integrable :
    Integrable (symbolicComputedExecutionCoarseWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedCoarseWork source target N depth encode outcome.2 outcome.1
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
end Symbolic



 theorem computedExecutionCoarseWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionCosts
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

 theorem computedExecutionRejectionWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionRejectionWork source target N) (computedExecutionLaw source target N) := by
  let incoming := physicalCoarseSeedLaw (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M source.length) source target N
    (integerParameters N).B (computedPhysicalCoarseDepth source target N)
  have hi : Integrable (computedFamilyRejectionWork source target N)
      (physicalFamilyRuntimeLaw (R := inputHeight N ^ 2) target N (integerParameters N).P
        (inputHeight N) incoming) :=
    finite_outer_integrable incoming _ (computedFamilyRejectionWork source target N)
      (computedFamilyRejectionWork_integrable source target N)
  have hj : Integrable (computedFamilyRejectionWork source target N)
      ((computedExecutionLaw source target N).map (computedExecutionProjection source target N)) := by
    rw [computedExecutionProjection_law]
    exact hi
  exact hj.comp_measurable (computedExecutionProjection_measurable source target N)

 theorem computedExecutionAccepted_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedExecutionAccepted source target N) := measurable_of_countable _

 theorem computedExecutionAcceptedWork_integrable (source target : List ℕ) (N : ℕ)
    (f : ComputedFamilyInput source target N → ℝ) :
    Integrable (f ∘ computedExecutionAccepted source target N) (computedExecutionLaw source target N) := by
  have hi : Integrable f ((computedExecutionLaw source target N).map
      (computedExecutionAccepted source target N)) := Integrable.of_finite
  exact hi.comp_measurable (computedExecutionAccepted_measurable source target N)



 theorem computedExecutionDictionaryWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionDictionaryWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyResult source target N input).dictionaryVisits)



 theorem computedExecutionAddressWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionAddressWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyAddressWork source target N input : ℝ))

/-- These are the actual coarse, rejection-bit, dictionary and address-construction counters.
The local arithmetic counter is kept separate until its kernel is composed. -/


 theorem computedExecutionNonlocalWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionNonlocalWork source target N) (computedExecutionLaw source target N) :=
  (((computedExecutionCoarseWork_integrable source target N).add
    (computedExecutionRejectionWork_integrable source target N)).add
    (computedExecutionDictionaryWork_integrable source target N)).add
    (computedExecutionAddressWork_integrable source target N)

 theorem constant_le_rpow_eventually (C epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N : ℕ in atTop, C ≤ (N + 2 : ℝ) ^ epsilon := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  exact ((tendsto_rpow_atTop hepsilon).comp ht).eventually (eventually_ge_atTop C)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarsePreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter MeasureTheory





theorem computedExecutionCoarsePreparationWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarsePreparationWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N (computedFamilyCoarsePreparationWork source target N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseSamplingWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



theorem symbolicComputedExecutionCoarseSamplingWork_integrable :
    Integrable (symbolicComputedExecutionCoarseSamplingWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedExecutionCoarseSamplingWork source target N depth encode
      (outcome.1, (fun _ => 0, outcome.2))
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)

end Symbolic



theorem computedExecutionCoarseSamplingWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseSamplingWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionCoarseSamplingWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedIndexedCoarseWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

section Symbolic
variable {M J R B : ℕ} [NeZero M] [NeZero R] [NeZero B]
  (source target : List ℕ) (N : ℕ)
  (depth : PhysicalEntry M J target.length → ℕ)
  (encode : Sum (PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2))
    (ChargedPhysicalRequest M J target.length (computedSeedPassCount N + 1)
      (inputHeight N ^ 2) (integerParameters N).T (integerParameters N).S) → ℕ)



theorem symbolicComputedExecutionIndexedCoarseWork_integrable :
    Integrable (symbolicComputedExecutionIndexedCoarseWork source target N depth encode)
      (physicalCoarseExecutionLaw (R := R) source target N (integerParameters N).P
        (inputHeight N) B depth) := by
  let μ := coarseFullSeedMeasure B depth
    (fun entry => physicalSource source entry.1)
    (fun entry => substring target entry.2.lo entry.2.hi)
  let range := physicalFamilyRange (M := M) (J := J) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
    (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)
  let f := fun outcome : PhysicalCoarseDraw source target B depth × (∀ key, Fin (range key)) =>
    symbolicComputedExecutionIndexedCoarseWork source target N depth encode
      (outcome.1, (fun _ => 0, outcome.2))
  have hf : Integrable f ((μ.prod (rejectionRuntimeArrayLaw range)).map
      (rejectionProductAccepted range)) := by
    rw [rejectionProductAccepted_law]
    exact Integrable.of_finite
  exact hf.comp_measurable (rejectionProductAccepted_measurable range)
end Symbolic



theorem computedExecutionIndexedCoarseWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionIndexedCoarseWork source target N) (computedExecutionLaw source target N) :=
  symbolicComputedExecutionIndexedCoarseWork_integrable source target N
    (computedPhysicalCoarseDepth source target N) (computedFamilyMemoCode source target N (inputHeight N ^ 2))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedReadChargedWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- Execution budget including indexed coarse computation, consumed threshold
bits, rejection sampling, dictionary operations, address construction and unit charges. -/


theorem computedExecutionReadChargedWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionReadChargedWork source target N) (computedExecutionLaw source target N) :=
  (((computedExecutionIndexedCoarseWork_integrable source target N).add
    (computedExecutionCoarseSamplingWork_integrable source target N)).add
    (computedExecutionNonlocalWork_integrable source target N)).add
    (computedExecutionCoarsePreparationWork_integrable source target N)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter



theorem computedExecutionKernelWork_integrable (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ) :
    Integrable (computedExecutionKernelWork source target N cost)
      (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N
    (fun input => (computedFamilyKernelWork source target N input (cost input) : ℝ))

/-- Execution work combines the nonlocal charges with a local kernel annotation. -/


theorem computedExecutionTotalWork_integrable (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ) :
    Integrable (computedExecutionTotalWork source target N cost)
      (computedExecutionLaw source target N) :=
  (computedExecutionReadChargedWork_integrable source target N).add
    (computedExecutionKernelWork_integrable source target N cost)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerQueryWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

/-- The actual computed widths of the encoded input index. -/
theorem integerQueryWidths (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      integerInputSymbolBits source target ≤ inputHeight N ^ 3 ∧
      integerInputPositionBits target ≤ inputHeight N ^ 3 := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop (max 100 C))] with N hlarge
  intro source target hsize halphabet
  have hH : 100 ≤ inputHeight N := (le_max_left _ _).trans (hlarge.trans (computed_smallLog_le_height N))
  have hC : C ≤ inputHeight N := (le_max_right _ _).trans (hlarge.trans (computed_smallLog_le_height N))
  have hs := integerInputSymbolBits_polynomial source target N C halphabet
  have hN := input_length_bits_le N
  have hm := Nat.mul_le_mul hC hN
  have hc : inputHeight N * (inputHeight N + 1) + 3 ≤ inputHeight N ^ 3 := by
    have h := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 3 ≤ inputHeight N by omega)
    nlinarith only [hH, h]
  refine ⟨by omega, ?_⟩
  exact (Nat.size_le_size (show target.length ≤ N from by omega)).trans
    ((computed_input_size_le_height N).trans (Nat.le_pow (by decide)))

theorem integerQueryLocalWork_cap (C : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ input key, integerQueryLocalWork source target N input key ≤
        computedLocalKernelBudget computedQueryWorkDegree N := by
  filter_upwards [computedQueryLocalWork_cap, integerQueryWidths C] with N hwork hwidth
  intro source target hsize halphabet input key
  have hw := hwidth source target hsize halphabet
  apply hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) input (integerOccurrenceIndex source target)
    (integerInputSymbolBits source target) (integerInputPositionBits target) hw.1 hw.2
    ?_ ?_ ?_ rfl key
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  · simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedOutputWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open MeasureTheory Filter

/-- Execution cost including shared binary setup and the final conversion.
The exact branch keeps its own charged dynamic program. -/


theorem computedFullOutputWork_expected_le (source target : List ℕ) (N : ℕ)
    (cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ)
    (setup : ℝ) (shared : ℕ) (output : ComputedFamilyInput source target N → ℕ)
    (fallbackOutput : ℕ) (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (budget outputBudget : ℝ)
    (hbudget : (∫ execution, computedExecutionTotalWork source target N cost execution
      ∂computedExecutionLaw source target N) ≤ budget)
    (houtput : ∀ input, (output input : ℝ) ≤ outputBudget) :
    (∫ outcome, computedFullOutputWork source target N cost setup shared output fallbackOutput outcome
      ∂computedFullLaw source target N epsilon) ≤ setup + shared + budget + outputBudget := by
  have hmap := integral_map (μ := computedExecutionLaw source target N)
    measurable_inr.aemeasurable
    (measurable_of_countable
      (computedFullOutputWork source target N cost setup shared output fallbackOutput)).aestronglyMeasurable
  simp only [computedFullLaw, hlarge, ite_true, if_true]
  rw [hmap]
  change (∫ execution, (setup + shared) + computedExecutionTotalWork source target N cost execution +
    (output (computedExecutionAccepted source target N execution) : ℝ)
    ∂computedExecutionLaw source target N) ≤ _
  have ho := computedExecutionAcceptedWork_integrable source target N (fun input => (output input : ℝ))
  change Integrable (fun execution => (output (computedExecutionAccepted source target N execution) : ℝ))
    (computedExecutionLaw source target N) at ho
  have ht := computedExecutionTotalWork_integrable source target N cost
  have hconst : Integrable (fun _ : ComputedExecutionOutcome source target N => setup + (shared : ℝ))
      (computedExecutionLaw source target N) := integrable_const _
  have hfirst : Integrable (fun execution => setup + (shared : ℝ) +
      computedExecutionTotalWork source target N cost execution) (computedExecutionLaw source target N) := hconst.add ht
  have hsplit := integral_add hfirst ho
  change (∫ execution, setup + (shared : ℝ) + computedExecutionTotalWork source target N cost execution +
    (output (computedExecutionAccepted source target N execution) : ℝ) ∂computedExecutionLaw source target N) = _ at hsplit
  rw [hsplit]
  have hsplitFirst := integral_add hconst ht
  change (∫ execution, setup + (shared : ℝ) + computedExecutionTotalWork source target N cost execution
    ∂computedExecutionLaw source target N) = _ at hsplitFirst
  rw [hsplitFirst]
  have hb : (∫ execution, (output (computedExecutionAccepted source target N execution) : ℝ)
      ∂computedExecutionLaw source target N) ≤ outputBudget := by
    calc
      _ ≤ ∫ _ : ComputedExecutionOutcome source target N, outputBudget ∂computedExecutionLaw source target N :=
        integral_mono ho (integrable_const _) (fun execution => houtput _)
      _ = outputBudget := by simp
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  linarith only [hbudget, hb]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryWork
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

theorem integerBinaryWork_expected_near_linear_oai (C : ℕ) (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) (epsilonTime : ℝ) (htime : 0 < epsilonTime) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      (∫ outcome, integerBinaryWork source target N epsilon outcome
        ∂computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon) ≤
          (N + 2 : ℝ) ^ (1 + epsilonTime) := by
  have hh : 0 < epsilonTime / 2 := half_pos htime
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C (epsilonTime / 2) hh,
    computedExecutionTotalWork_expected_near_linear computedQueryWorkDegree (epsilonTime / 2) hh,
    integerQueryLocalWork_cap C, integer_encoded_symbol_bits C,
    fixed_height_power_subpolynomial 12 (1 + epsilonTime / 2) (by linarith),
    constant_le_rpow_eventually 5 (epsilonTime / 2) hh] with N hlarge hpre hwork hcap hsymbols hpower hfive
  intro source target hsize halphabet
  have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
  have hsetup := computedQuerySetupWithWork_cost N hN hlarge.2.1.1
  have hs : ((computedQuerySetupWithWork N).2 : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    have hc : ((computedQuerySetupWithWork N).2 : ℝ) ≤ (inputHeight N : ℝ) ^ 12 := by
      exact_mod_cast hsetup
    exact hc.trans hpower
  have hten : (inputHeight N : ℝ) ^ 10 ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
    (pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ inputHeight N from Nat.one_le_pow _ _ (by decide)))
      (by decide : 10 ≤ 12)).trans hpower
  have hn : (N : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    calc
      _ ≤ (N + 2 : ℝ) := le_add_of_nonneg_right (by norm_num)
      _ = (N + 2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
        Real.rpow_le_rpow_of_exponent_le (by have := Nat.cast_nonneg (α := ℝ) N; linarith) (by linarith)
  have hf (input) : ((integerBinaryOutput source target N input).2 : ℝ) ≤
      2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by
    have hb := integerBinaryOutput_cost source target N epsilon hlarge hsize input
    have hbR : ((integerBinaryOutput source target N input).2 : ℝ) ≤ N + (inputHeight N : ℝ) ^ 10 := by
      exact_mod_cast hb
    linarith only [hbR, hn, hten]
  have hw := hwork (source.map integerSymbolCode) (target.map integerSymbolCode)
    (by simpa only [List.length_map] using hsize) (hsymbols source target halphabet)
    (integerQueryLocalWork source target N) (hcap source target hsize halphabet)
  have hfull := computedFullOutputWork_expected_le (source.map integerSymbolCode) (target.map integerSymbolCode) N
    (integerQueryLocalWork source target N) (integerPreevaluationWork source target N epsilon)
    (computedQuerySetupWithWork N).2 (fun input => (integerBinaryOutput source target N input).2) (N + 1)
    epsilon hlarge ((N + 2 : ℝ) ^ (1 + epsilonTime / 2))
    (2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2)) hw hf
  have hp := hpre source target hsize halphabet epsilon
  calc
    _ ≤ (integerPreevaluationWork source target N epsilon : ℝ) + (computedQuerySetupWithWork N).2 +
        (N + 2 : ℝ) ^ (1 + epsilonTime / 2) + 2 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := hfull
    _ ≤ 5 * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) := by linarith only [hp, hs]
    _ ≤ (N + 2 : ℝ) ^ (epsilonTime / 2) * (N + 2 : ℝ) ^ (1 + epsilonTime / 2) :=
      mul_le_mul_of_nonneg_right hfive (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.integerBinaryWork_expected_near_linear_oai := @OAI.EditApproximation.integerBinaryWork_expected_near_linear_oai
