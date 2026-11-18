-- Prove2me | solution 1 for OAI.EditApproximation.integerBinarySpace_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:44.731307+00:00
-- url     : https://prove2.me/submissions/d380406c-f1f8-4d53-ade9-af17614801e0

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
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_near_linear
import Theorems.Thm_OAI_EditApproximation_computedQueryMemoResult_storage
import Theorems.Thm_OAI_EditApproximation_computedQuerySetupWithWork_cost
import Theorems.Thm_OAI_EditApproximation_computedQueryTemporaryCells_polynomial
import Theorems.Thm_OAI_EditApproximation_integerBinaryOutput_cost
import Theorems.Thm_OAI_EditApproximation_integerPreevaluationWork_near_linear
import Theorems.Thm_OAI_EditApproximation_integerStoredDataSpace_polynomial

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryFinalSpace
attribute [-instance] _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation.BinaryFraction



theorem finalAnswerAllocation_le_work (N : ℕ) (a : BinaryFraction) :
    finalAnswerAllocation N a ≤ (finalAnswerWithWork N a).2 := by
  have hf := naturalFloorAllocation_le_work a
  have hm := naturalWordLEAllocation_le_work N.bits (naturalFloorWithWork a).1
  unfold finalAnswerAllocation finalAnswerWithWork wordMinWithWork
  dsimp only
  omega

end EditApproximation.BinaryFraction

end OAI
end

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRequestSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem two_pow_inputHeight_le (N : ℕ) : 2 ^ inputHeight N ≤ 4 * (N + 2) ^ 2 := by
  have hc : 0 < Nat.clog 2 (N + 2) :=
    Nat.clog_pos (by decide : 1 < (2 : ℕ)) (by omega)
  have hH := (rejectionWord_range (Nat.clog 2 (N + 2)) hc).2
  have hN := (rejectionWord_range (N + 2) (by omega)).2
  change inputHeight N < 2 * Nat.clog 2 (N + 2) at hH
  change 2 ^ Nat.clog 2 (N + 2) < 2 * (N + 2) at hN
  calc
    _ ≤ 2 ^ (2 * Nat.clog 2 (N + 2)) := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hH.le
    _ = (2 ^ Nat.clog 2 (N + 2)) ^ 2 := by rw [← pow_mul]; congr 1; omega
    _ ≤ (2 * (N + 2)) ^ 2 := Nat.pow_le_pow_left hN.le 2
    _ = _ := by ring

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSuffixDP
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An exact suffix dynamic program for the bounded initial input range.
Each source row is computed once; its cells minimize over target cuts.
The singleton prefix cost is the executable occurrence formula. -/

namespace EditApproximation

open EditDistortion



theorem natListMinimum_le_member (fallback value : ℕ) (values : List ℕ) (h : value ∈ values) :
    natListMinimum fallback values ≤ value := by
  induction values with
  | nil => simp only [List.not_mem_nil] at h
  | cons first rest ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (ih h)

theorem natListMinimum_lower (fallback lower : ℕ) (values : List ℕ)
    (hfallback : lower ≤ fallback) (hvalues : ∀ value ∈ values, lower ≤ value) :
    lower ≤ natListMinimum fallback values := by
  induction values with
  | nil => exact hfallback
  | cons first rest ih =>
    exact le_min (hvalues first (List.mem_cons_self))
      (ih (fun value h => hvalues value (List.mem_cons_of_mem _ h)))



theorem exactSuffixDP_length {α : Type*} [DecidableEq α] (source target : List α) :
    (exactSuffixDP source target).length = target.length + 1 := by
  cases source <;> simp only [exactSuffixDP, List.length_ofFn]

theorem ofFn_nat_getD {n j : ℕ} (f : Fin (n + 1) → ℕ) (hj : j ≤ n) :
    (List.ofFn f).getD j 0 = f ⟨j, Nat.lt_succ_of_le hj⟩ := by
  have hlt : j < (List.ofFn f).length := by simpa only [List.length_ofFn] using Nat.lt_succ_of_le hj
  rw [List.getD_eq_getElem _ _ hlt, List.getElem_ofFn]

theorem edit_nil_left_exact {α : Type*} (target : List α) : edit ([] : List α) target = target.length := by
  have hlo := (cost_length_bounds (s := true) ([] : List α) target).2
  have hup := edit_le_max_length ([] : List α) target
  simp only [List.length_nil, zero_add, max_eq_right (Nat.zero_le _)] at hlo hup
  exact Nat.le_antisymm hup hlo

theorem exactSuffixDP_spec {α : Type*} [DecidableEq α] (source target : List α) :
    ∀ j ≤ target.length, (exactSuffixDP source target).getD j 0 = edit source (target.drop j) := by
  induction source with
  | nil =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj, edit_nil_left_exact, List.length_drop]
  | cons a rest ih =>
    intro j hj
    rw [exactSuffixDP, ofFn_nat_getD _ hj]
    dsimp only
    have hcandidate (k : ℕ) (hk : k ≤ target.length - j) :
        edit (a :: rest) (target.drop j) ≤
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0 := by
      rw [singletonCost_eq_edit, ih (j + k) (by omega)]
      have h := cost_append_le (s := true) [a] ((target.drop j).take k) rest ((target.drop j).drop k)
      rw [List.take_append_drop] at h
      simpa only [cost, edit, List.singleton_append, List.drop_drop] using h
    apply Nat.le_antisymm
    · obtain ⟨left, right, hsplit, hcost⟩ := edit_append_split [a] rest (target.drop j)
      have hk : left.length ≤ target.length - j := by
        have hlen := congrArg List.length hsplit
        simp only [List.length_drop, List.length_append] at hlen
        omega
      have hleft : (target.drop j).take left.length = left := by
        rw [hsplit]
        simp only [List.take_left]
      have hright : target.drop (j + left.length) = right := by
        rw [← List.drop_drop, hsplit]
        simp only [List.drop_left]
      have hm := natListMinimum_le_member
        (singletonCost a [] + (exactSuffixDP rest target).getD j 0)
        (singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0)
        ((List.range (target.length - j + 1)).map fun k =>
          singletonCost a ((target.drop j).take k) + (exactSuffixDP rest target).getD (j + k) 0)
        (List.mem_map.mpr ⟨left.length, List.mem_range.mpr (by omega), rfl⟩)
      have hvalue : singletonCost a ((target.drop j).take left.length) +
          (exactSuffixDP rest target).getD (j + left.length) 0 = edit [a] left + edit rest right := by
        rw [hleft, singletonCost_eq_edit, ih (j + left.length) (by omega), hright]
      simpa only [List.singleton_append] using hm.trans_eq (hvalue.trans hcost.symm)
    · apply natListMinimum_lower
      · simpa only [List.take_zero, Nat.add_zero] using hcandidate 0 (Nat.zero_le _)
      · intro value hvalue
        rcases List.mem_map.mp hvalue with ⟨k, hk, rfl⟩
        exact hcandidate k (by have := List.mem_range.mp hk; omega)



end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Simultaneous seed failure with the computed parameters

The count includes every dyadic guess, complete coarse-tree node and shift.
Independent finite entry streams realize the actual full table law.
Symbolic recursion indices carry exact equalities to the computed parameters.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory

theorem twice_square_le_two_pow (r : ℕ) (hr : 8 ≤ r) : 2 * r ^ 2 ≤ 2 ^ r := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
    rw [pow_succ 2 r]
    nlinarith

theorem computed_coarse_B_upper (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    (integerParameters N).B ≤ 2 ^ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  have hp : coarseExponent (inputSmallLog N) ≤ 2 * heightExponent N := by
    have hsqrt := (Nat.sqrt_le_self (Nat.sqrt (Nat.log 2 (inputSmallLog N)))).trans
      (Nat.sqrt_le_self (Nat.log 2 (inputSmallLog N)))
    exact hsqrt.trans ((Nat.log_le_self _ _).trans (by omega))
  have hpoly := twice_square_le_two_pow (heightExponent N) hr
  have hexponent : heightExponent N * coarseExponent (inputSmallLog N) ≤ inputHeight N := by
    have hmul := Nat.mul_le_mul_left (heightExponent N) hp
    change _ ≤ 2 ^ heightExponent N
    nlinarith
  change (2 ^ heightExponent N) ^ coarseExponent (inputSmallLog N) ≤ 2 ^ inputHeight N
  rw [← pow_mul]
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hexponent

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

theorem two_hundred_le_two_pow_thousand : 200 ≤ (2 : ℕ) ^ 1000 := by
  have h := pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by decide : 8 ≤ 1000)
  exact le_trans (by decide : 200 ≤ (2 : ℕ) ^ 8) h

open MeasureTheory ProbabilityTheory

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_ExactSuffixDPWork
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.physicalCommonCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A costed implementation of the exact cut dynamic program. The counter
counts symbol comparisons and list-cell visits, with explicit outer-loop
overhead. Each counted transition uses a fixed number of word operations;
the surrounding RAM realization supplies that constant. Suffix lookups and
occurrence scans are charged rather than treated as constant-time arrays. -/

namespace EditApproximation











theorem dpLength_spec {α : Type*} (word : List α) :
    (dpLength word).1 = word.length ∧ (dpLength word).2 = word.length + 1 := by
  induction word with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    constructor <;> simp only [dpLength, List.length_cons, ih.1, ih.2]

theorem dpDrop_spec {α : Type*} (n : ℕ) (word : List α) :
    (dpDrop n word).1 = word.drop n ∧ (dpDrop n word).2 ≤ word.length + 1 := by
  induction n generalizing word with
  | zero => simp only [dpDrop, List.drop_zero, le_add_iff_nonneg_left, Nat.zero_le, and_self]
  | succ n ih =>
    cases word with
    | nil => simp only [dpDrop, List.drop_nil, List.length_nil, le_refl, and_self]
    | cons first rest =>
      have h := ih rest
      exact ⟨h.1, by simpa only [dpDrop, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpTake_spec {α : Type*} (n : ℕ) (word : List α) :
    (dpTake n word).1 = word.take n ∧ (dpTake n word).2 ≤ word.length + 1 := by
  induction n generalizing word with
  | zero => simp only [dpTake, List.take_zero, le_add_iff_nonneg_left, Nat.zero_le, and_self]
  | succ n ih =>
    cases word with
    | nil => simp only [dpTake, List.take_nil, List.length_nil, le_refl, and_self]
    | cons first rest =>
      have h := ih rest
      exact ⟨congrArg (List.cons first) h.1,
        by simpa only [dpTake, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpGetD_spec (word : List ℕ) (n : ℕ) :
    (dpGetD word n).1 = word.getD n 0 ∧ (dpGetD word n).2 ≤ word.length + 1 := by
  induction word generalizing n with
  | nil => simp [dpGetD]
  | cons first rest ih =>
    cases n with
    | zero => simp [dpGetD]
    | succ n =>
      have h := ih n
      exact ⟨h.1, by simpa only [dpGetD, List.length_cons] using Nat.add_le_add_right h.2 1⟩

theorem dpMember_spec {α : Type*} [DecidableEq α] (a : α) (word : List α) :
    (dpMember a word).1 = decide (a ∈ word) ∧ (dpMember a word).2 ≤ word.length + 1 := by
  induction word with
  | nil => simp [dpMember]
  | cons first rest ih =>
    by_cases h : a = first
    · simp [dpMember, h]
    · constructor
      · simp only [dpMember, h, ite_false, if_false, ih.1, List.mem_cons, false_or]
      · simpa only [dpMember, h, ite_false, if_false, List.length_cons] using Nat.add_le_add_right ih.2 1



theorem dpSingleton_spec {α : Type*} [DecidableEq α] (a : α) (word : List α) :
    (dpSingleton a word).1 = singletonCost a word ∧ (dpSingleton a word).2 ≤ 2 * word.length + 4 := by
  by_cases h : word = []
  · subst word; simp [dpSingleton, singletonCost]
  · constructor
    · simp only [dpSingleton, singletonCost, h, ite_false, if_false, occurrenceDeficit, (dpLength_spec word).1,
        (dpMember_spec a word).1, decide_eq_true_eq]
    · have hc := (dpLength_spec word).2
      have hm := (dpMember_spec a word).2
      simp only [dpSingleton, h, ite_false, if_false]
      omega



theorem dpMinimum_spec (fallback : ℕ) (values : List ℕ) :
    (dpMinimum fallback values).1 = natListMinimum fallback values ∧
      (dpMinimum fallback values).2 = values.length + 1 := by
  induction values with
  | nil => exact ⟨rfl, rfl⟩
  | cons first rest ih =>
    constructor <;> simp only [dpMinimum, natListMinimum, ih.1, ih.2, List.length_cons]



theorem dpCandidate_value {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j k : ℕ) :
    (dpCandidate a target previous j k).1 =
      singletonCost a ((target.drop j).take k) + previous.getD (j + k) 0 := by
  simp only [dpCandidate, (dpSingleton_spec _ _).1, (dpDrop_spec _ _).1,
    (dpTake_spec _ _).1, (dpGetD_spec _ _).1]

theorem dpCandidate_work {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (hprevious : previous.length = target.length + 1) (j k : ℕ) :
    (dpCandidate a target previous j k).2 ≤ 12 * (target.length + 1) := by
  have hs := (dpDrop_spec j target).2
  have hp := (dpTake_spec k (dpDrop j target).1).2
  have ho := (dpSingleton_spec a (dpTake k (dpDrop j target).1).1).2
  have hg := (dpGetD_spec previous (j + k)).2
  have hsl : (dpDrop j target).1.length ≤ target.length := by
    rw [(dpDrop_spec _ _).1, List.length_drop]; omega
  have hpl : (dpTake k (dpDrop j target).1).1.length ≤ target.length := by
    rw [(dpTake_spec _ _).1, List.length_take]
    exact (min_le_right _ _).trans hsl
  simp only [dpCandidate]
  rw [hprevious] at hg
  omega

theorem nat_pair_sum_bound {ι : Type*} (values : List ι) (cost : ι → ℕ) (budget : ℕ)
    (h : ∀ value ∈ values, cost value ≤ budget) :
    (values.map cost).sum ≤ values.length * budget := by
  induction values with
  | nil => simp
  | cons first rest ih =>
    have hf := h first List.mem_cons_self
    have hr := ih (fun value hv => h value (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    nlinarith



theorem dpCell_value {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j : ℕ) :
    (dpCell a target previous j).1 =
      natListMinimum (singletonCost a [] + previous.getD j 0)
        ((List.range (target.length - j + 1)).map fun k =>
          singletonCost a ((target.drop j).take k) + previous.getD (j + k) 0) := by
  simp only [dpCell, (dpMinimum_spec _ _).1, dpCandidate_value, List.take_zero, Nat.add_zero,
    List.map_map, Function.comp_def]

theorem dpCell_work {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (hprevious : previous.length = target.length + 1) (j : ℕ) :
    (dpCell a target previous j).2 ≤ 40 * (target.length + 1) ^ 2 := by
  let candidates := (List.range (target.length - j + 1)).map (dpCandidate a target previous j)
  have hsum := nat_pair_sum_bound candidates Prod.snd (12 * (target.length + 1)) (by
    intro candidate hc
    rcases List.mem_map.mp hc with ⟨k, _, rfl⟩
    exact dpCandidate_work a target previous hprevious j k)
  have hcount : candidates.length ≤ target.length + 1 := by
    simp only [candidates, List.length_map, List.length_range]; omega
  have hf := dpCandidate_work a target previous hprevious j 0
  have hm := (dpMinimum_spec (dpCandidate a target previous j 0).1 (candidates.map Prod.fst)).2
  simp only [List.length_map] at hm
  have hl := (dpLength_spec target).2
  change (dpCandidate a target previous j 0).2 + (candidates.map Prod.snd).sum +
    (dpMinimum (dpCandidate a target previous j 0).1 (candidates.map Prod.fst)).2 +
    (dpLength target).2 + 3 * candidates.length + 4 ≤ _
  have hprod := Nat.mul_le_mul_right (12 * (target.length + 1)) hcount
  nlinarith



theorem chargedSuffixDP_value {α : Type*} [DecidableEq α] (source target : List α) :
    (chargedSuffixDP source target).1 = exactSuffixDP source target := by
  induction source with
  | nil => rfl
  | cons a rest ih =>
    simp only [chargedSuffixDP, exactSuffixDP, List.map_ofFn, Function.comp_def, dpCell_value, ih]

theorem chargedSuffixDP_work {α : Type*} [DecidableEq α] (source target : List α) :
    (chargedSuffixDP source target).2 ≤ 50 * (source.length + 1) * (target.length + 1) ^ 3 := by
  induction source with
  | nil =>
    have hcube : target.length + 1 ≤ (target.length + 1) ^ 3 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by omega : 1 ≤ target.length + 1) (by decide : 1 ≤ 3)
    simp only [chargedSuffixDP, List.length_nil]
    omega
  | cons a rest ih =>
    let previous := chargedSuffixDP rest target
    let cells := List.ofFn fun j : Fin (target.length + 1) => dpCell a target previous.1 j.val
    have hprevious : previous.1.length = target.length + 1 := by
      rw [chargedSuffixDP_value, exactSuffixDP_length]
    have hsum := nat_pair_sum_bound cells Prod.snd (40 * (target.length + 1) ^ 2) (by
      intro cell hc
      rcases List.mem_ofFn.mp hc with ⟨j, rfl⟩
      exact dpCell_work a target previous.1 hprevious j.val)
    have hcount : cells.length = target.length + 1 := List.length_ofFn
    have hl := (dpLength_spec target).2
    change previous.2 + (cells.map Prod.snd).sum + 2 * (dpLength target).2 +
      2 * cells.length + 3 ≤ _
    change previous.2 ≤ _ at ih
    rw [hcount] at hsum ⊢
    simp only [List.length_cons]
    nlinarith [show 0 ≤ target.length by omega]

/-- Every retained row has linear length, and every stored distance fits
the input length bound; the traversal counter is polynomial even with lists. -/
theorem chargedSuffixDP_storage {α : Type*} [DecidableEq α] (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N) :
    (chargedSuffixDP source target).1.length ≤ N + 1 ∧
      (∀ j ≤ target.length, (chargedSuffixDP source target).1.getD j 0 ≤ N) ∧
      (chargedSuffixDP source target).2 ≤ 50 * (N + 1) ^ 4 := by
  rw [chargedSuffixDP_value]
  constructor
  · rw [exactSuffixDP_length]; omega
  constructor
  · intro j hj
    rw [exactSuffixDP_spec source target j hj]
    apply (EditDistortion.edit_le_max_length _ _).trans
    simp only [List.length_drop]
    exact max_le (by omega) (by omega)
  · have h := chargedSuffixDP_work source target
    have hn : source.length + 1 ≤ N + 1 := by omega
    have hm : target.length + 1 ≤ N + 1 := by omega
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_left 50 hn) (Nat.pow_le_pow_left hm 3)
    exact h.trans (by simpa only [show (N + 1) ^ 4 = (N + 1) * (N + 1) ^ 3 by ring,
      Nat.mul_assoc] using hmul)

theorem dpTake_allocation {α : Type*} (n : ℕ) (word : List α) :
    (dpTake n word).1.length ≤ (dpTake n word).2 := by
  induction n generalizing word with
  | zero => simp [dpTake]
  | succ n ih =>
    cases word with
    | nil => simp [dpTake]
    | cons first rest => simpa only [dpTake, List.length_cons] using Nat.add_le_add_right (ih rest) 1



theorem dpCandidate_allocation {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j k : ℕ) :
    dpCandidateAllocation target j k ≤ (dpCandidate a target previous j k).2 := by
  have h := dpTake_allocation k (dpDrop j target).1
  simp only [dpCandidateAllocation, dpCandidate]
  omega

theorem nat_list_sum_mono {ι : Type*} (values : List ι) (f g : ι → ℕ)
    (h : ∀ value ∈ values, f value ≤ g value) : (values.map f).sum ≤ (values.map g).sum := by
  induction values with
  | nil => exact le_rfl
  | cons first rest ih =>
    have hf := h first List.mem_cons_self
    have hr := ih (fun value hv => h value (List.mem_cons_of_mem _ hv))
    simp only [List.map_cons, List.sum_cons]
    omega

/-- Candidate pairs, natural candidate values, the index range and prefix
lists are counted as materialized cells. The fallback prefix is retained. -/


theorem dpCell_allocation {α : Type*} [DecidableEq α] (a : α) (target : List α)
    (previous : List ℕ) (j : ℕ) : dpCellAllocation target j ≤ (dpCell a target previous j).2 := by
  have hf := dpCandidate_allocation a target previous j 0
  have hs := nat_list_sum_mono (List.range (target.length - j + 1))
    (dpCandidateAllocation target j) (fun k => (dpCandidate a target previous j k).2)
    (fun k _ => dpCandidate_allocation a target previous j k)
  simp only [dpCell, (dpMinimum_spec _ _).2, List.length_map, List.length_range,
    List.map_map, Function.comp_def]
  unfold dpCellAllocation
  omega

/-- Total materialized list cells over the whole run. This also bounds
the simultaneously live materialized cells under any deallocation policy. -/


theorem suffixDPAllocation_le_work {α : Type*} [DecidableEq α] (source target : List α) :
    suffixDPAllocation source target ≤ (chargedSuffixDP source target).2 := by
  induction source with
  | nil => simp only [suffixDPAllocation, chargedSuffixDP]; omega
  | cons a rest ih =>
    let previous := chargedSuffixDP rest target
    let cells := List.ofFn fun j : Fin (target.length + 1) => dpCell a target previous.1 j.val
    have hs : (List.ofFn fun j : Fin (target.length + 1) => dpCellAllocation target j.val).sum ≤
        (cells.map Prod.snd).sum := by
      simp only [cells, List.map_ofFn, List.sum_ofFn]
      exact Finset.sum_le_sum (fun j _ => dpCell_allocation a target previous.1 j.val)
    have hl := (dpLength_spec target).2
    have hc : cells.length = target.length + 1 := List.length_ofFn
    change suffixDPAllocation rest target + _ + _ ≤
      previous.2 + (cells.map Prod.snd).sum + 2 * (dpLength target).2 + 2 * cells.length + 3
    change suffixDPAllocation rest target ≤ previous.2 at ih
    omega

theorem suffixDPAllocation_polynomial {α : Type*} [DecidableEq α] (source target : List α)
    (N : ℕ) (hsize : source.length + target.length ≤ N) :
    suffixDPAllocation source target ≤ 50 * (N + 1) ^ 4 :=
  (suffixDPAllocation_le_work source target).trans (chargedSuffixDP_storage source target N hsize).2.2

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoAddressWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
namespace FiniteQuery

/-- Annotate exactly the requests made by an existing adaptive run. -/


 theorem requestWork_le {ι κ : Type*} (ask : ι → BinaryMemo ℚ → RecursiveMemoResult κ)
    (cost : ι → BinaryMemo ℚ → ℕ) (C : ℕ)
    (hcost : ∀ key memory, cost key memory ≤ C * (ask key memory).requests)
    (program : FiniteQuery ι) (memory : BinaryMemo ℚ) :
    requestWork ask cost program memory ≤ C * (run ask program memory).requests := by
  induction program generalizing memory with
  | done value => simp only [requestWork, run, Nat.mul_zero, le_refl]
  | read key next ih =>
    have hfirst := hcost key memory
    have hrest := ih (ask key memory).value (ask key memory).memory
    simp only [requestWork, run, Nat.mul_add]
    exact Nat.add_le_add hfirst hrest

end FiniteQuery

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedRetainedValues
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_height_polynomial (N : ℕ) : inputHeight N ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := Nat.lt_two_pow_self.le
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseRangeCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Copy a range from an indexed immutable input. Each step charges the
source read, copied symbol bits, and literal binary address increment. -/


theorem coarseRangeCopyWithWork_value (read : ℕ → ℕ) (start length : ℕ) :
    (coarseRangeCopyWithWork read start length).1 =
      List.ofFn (fun i : Fin length => read (start + i.val)) := by
  induction length generalizing start with
  | zero => simp only [coarseRangeCopyWithWork, List.ofFn_zero]
  | succ length ih =>
    simp only [coarseRangeCopyWithWork, binaryNaturalAddWithWork_value, ih, List.ofFn_succ,
      Fin.val_zero, Nat.add_zero, Fin.val_succ, Nat.add_comm, Nat.add_left_comm]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSliceCopy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarseRangeCopyWithWork_slice (input : List ℕ) (lo hi : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ input.length) :
    (coarseRangeCopyWithWork (fun i => input[i]?.getD 0) lo (hi - lo)).1 = substring input lo hi := by
  rw [coarseRangeCopyWithWork_value]
  apply List.ext_getElem
  · simp only [List.length_ofFn, substring, List.length_take, List.length_drop]
    rw [min_eq_left hhi]
  · intro i hi1 hi2
    have hil : i < hi - lo := by simpa only [List.length_ofFn] using hi1
    have hip : lo + i < input.length := by omega
    simp only [List.getElem_ofFn, substring, List.getElem_take, List.getElem_drop,
      List.getElem?_eq_getElem hip, Option.getD_some]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInputGuard
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- This guard uses interval endpoints before either input slice is copied. -/


theorem coarseInputGuardWithWork_value (sourceLo sourceHi targetLo targetHi : ℕ) :
    (coarseInputGuardWithWork sourceLo sourceHi targetLo targetHi).1 =
      decide (2 * (sourceHi - sourceLo) < targetHi - targetLo) := by
  apply Bool.eq_iff_iff.mpr
  simp only [coarseInputGuardWithWork, saturatingSubtractWithWork_value,
    binaryNaturalMulWithWork_value, decide_eq_true_eq, binaryNaturalCompareWithWork_lt]

/-- The optional copied pair is absent on the long-target branch. -/


theorem coarsePreparedSlicesWithWork_value (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).1 =
      if 2 * (sourceHi - sourceLo) < targetHi - targetLo then none else
      some (substring source sourceLo sourceHi, substring target targetLo targetHi) := by
  simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, decide_eq_true_eq]
  split_ifs
  · rfl
  · simp only [coarseRangeCopyWithWork_slice source sourceLo sourceHi hslo hshi,
      coarseRangeCopyWithWork_slice target targetLo targetHi htlo hthi]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_RankedMemoKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

/-- Count local arithmetic only on a cache miss, following exactly the
recursive evaluator's returned values, requests and intermediate memories. -/


 theorem rankedMemoKernelWork_le {κ : Type*} (rank : κ → ℕ)
    (program : (key : κ) → FiniteQuery {child : κ // rank child < rank key})
    (bits : ℕ) (encode cost : κ → ℕ) (C : ℕ) (hcost : ∀ key, cost key ≤ C)
    (key : κ) (memory : BinaryMemo ℚ) :
    rankedMemoKernelWork rank program bits encode cost key memory ≤
      C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
  have hall : ∀ level key, rank key = level → ∀ memory,
      rankedMemoKernelWork rank program bits encode cost key memory ≤
        C * (rankedMemoEvaluate rank program bits encode key memory).requests := by
    intro level
    induction level using Nat.strong_induction_on with
    | h level ih =>
      intro key hlevel memory
      rw [rankedMemoKernelWork, rankedMemoEvaluate]
      split
      · rename_i result hfound
        simp only
        exact Nat.zero_le _
      · rename_i hfound
        simp only
        have hchildren : ∀ (child : {child : κ // rank child < rank key}) previous,
            rankedMemoKernelWork rank program bits encode cost child.val previous ≤
              C * (rankedMemoEvaluate rank program bits encode child.val previous).requests := by
          intro child previous
          exact ih (rank child.val) (by simpa only [← hlevel] using child.property) child.val rfl previous
        have hr := FiniteQuery.requestWork_le
          (fun child previous => rankedMemoEvaluate rank program bits encode child.val previous)
          (fun child previous => rankedMemoKernelWork rank program bits encode cost child.val previous)
          C hchildren (program key) memory
        have hk := hcost key
        rw [Nat.mul_add, Nat.mul_one]
        omega
  exact hall (rank key) key rfl memory

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedKernelWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter



/-- Local arithmetic annotations follow the actual memo run, hence are
incurred once per cache miss, with the original program and draw values. -/


theorem computedFamilyKernelWork_le (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N)
    (cost : ComputedFamilyMemoKey source target N → ℕ) (C : ℕ)
    (hcost : ∀ key, cost key ≤ C) :
    computedFamilyKernelWork source target N input cost ≤
      C * (computedFamilyResult source target N input).requests :=
  rankedMemoKernelWork_le _ _ _ _ cost C hcost _ _

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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInputStorage
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem storedNaturalBits_le (values : List ℕ) (A : ℕ)
    (h : ∀ a ∈ values, Nat.size a ≤ A) :
    storedNaturalBits values ≤ 1 + values.length * (A + 1) := by
  have hs : (values.map fun a => Nat.size a + 1).sum ≤ values.length * (A + 1) := by
    induction values with
    | nil => simp
    | cons a values ih =>
      have ha := h a List.mem_cons_self
      have ht := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
  exact Nat.add_le_add_left hs 1



theorem coarsePreparedInputStorage_le (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi A : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ A) :
    coarsePreparedInputStorage source target sourceLo sourceHi targetLo targetHi ≤
      3 + (source.length + target.length) * (A + 1) := by
  have hs : storedNaturalBits (substring source sourceLo sourceHi) ≤ 1 + source.length * (A + 1) := by
    apply (storedNaturalBits_le _ A (by
      intro a ha
      exact hsymbol a (List.mem_append_left _ (List.mem_of_mem_take (List.mem_of_mem_drop ha))))).trans
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  have ht : storedNaturalBits (substring target targetLo targetHi) ≤ 1 + target.length * (A + 1) := by
    apply (storedNaturalBits_le _ A (by
      intro a ha
      exact hsymbol a (List.mem_append_right _ (List.mem_of_mem_take (List.mem_of_mem_drop ha))))).trans
    apply Nat.add_le_add_left
    apply Nat.mul_le_mul_right
    simp only [substring, List.length_drop, List.length_take]
    exact (Nat.sub_le _ _).trans (min_le_right _ _)
  unfold coarsePreparedInputStorage
  rw [coarsePreparedSlicesWithWork_value source target sourceLo sourceHi targetLo targetHi hslo hshi htlo hthi]
  split_ifs
  · simp only; omega
  · simp only
    nlinarith only [hs, ht]

theorem coarsePreparedInputStorage_polynomial (source target : List ℕ)
    (N sourceLo sourceHi targetLo targetHi : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) :
    coarsePreparedInputStorage source target sourceLo sourceHi targetLo targetHi ≤ (N + 2) ^ 16 := by
  have h := coarsePreparedInputStorage_le source target sourceLo sourceHi targetLo targetHi
    (inputHeight N ^ 3) hslo hshi htlo hthi hsymbol
  let X := N + 2
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hH := Nat.pow_le_pow_left (computed_height_polynomial N) 3
  rw [← pow_mul] at hH
  change inputHeight N ^ 3 ≤ X ^ 12 at hH
  have h1 : 1 ≤ X ^ 12 := one_le_pow₀ (by omega)
  have hm := Nat.mul_le_mul (show source.length + target.length ≤ X by dsimp only [X]; omega)
    (show inputHeight N ^ 3 + 1 ≤ 2 * X ^ 12 by omega)
  have hp : 1 ≤ X ^ 13 := one_le_pow₀ (by omega)
  have hc : 5 ≤ X ^ 3 := (by decide : 5 ≤ (2 : ℕ) ^ 3).trans (Nat.pow_le_pow_left hX 3)
  calc
    _ ≤ 5 * X ^ 13 := by nlinarith only [h, hm, hp]
    _ ≤ X ^ 3 * X ^ 13 := Nat.mul_le_mul_right _ hc
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarsePolynomial
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
namespace BinaryFraction
open Filter

theorem computedCoarseBranching_polynomial (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) : (integerParameters N).B ≤ (N + 2) ^ 4 := by
  have h4 : 4 ≤ (N + 2) ^ 2 := by nlinarith only [Nat.zero_le N]
  calc
    _ ≤ 2 ^ inputHeight N := computed_coarse_B_upper N hN hell
    _ ≤ 4 * (N + 2) ^ 2 := two_pow_inputHeight_le N
    _ ≤ (N + 2) ^ 2 * (N + 2) ^ 2 := Nat.mul_le_mul_right _ h4
    _ = _ := by rw [← pow_add]

end BinaryFraction
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInitialStorage
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem coarseHistoryKeyCost_le {α β ι : Type*} (cost : ι → ℕ) (C : ℕ)
    (hcost : ∀ entry, cost entry ≤ C) (key : Sum α (Sum ι β)) :
    coarseHistoryKeyCost cost key ≤ C := by
  rcases key with scalar | entry | table
  · exact Nat.zero_le _
  · exact hcost entry
  · exact Nat.zero_le _

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseHistorySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
attribute [-simp] _root_.OAI.EditApproximation.queryChargedReadHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

theorem computedFamilyCoarseArrayCapacity_bound (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseArrayCapacity source target N input ≤
      (N + 2) ^ 37 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  exact coarseHistoryKeyCost_le _ _ (fun _ => le_rfl)

theorem computedFamilyCoarseArrayCapacity_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseArrayCapacity source target N input ≤ (N + 2) ^ 39 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 37 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseArrayCapacity_bound source target N input
    _ ≤ (N + 2) ^ 37 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseControlSpace
attribute [-simp] _root_.OAI.EditApproximation.queryChargedReadHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

theorem computedFamilyCoarseControlCapacity_bound (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseControlCapacity source target N input ≤
      (N + 2) ^ 182 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  exact coarseHistoryKeyCost_le _ _ (fun _ => le_rfl)

theorem computedFamilyCoarseControlCapacity_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseControlCapacity source target N input ≤ (N + 2) ^ 184 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 182 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseControlCapacity_bound source target N input
    _ ≤ (N + 2) ^ 182 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseScratchSpace
attribute [-simp] _root_.OAI.EditApproximation.queryChargedReadHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter

theorem computedFamilyCoarseScratchCapacity_bound (source target : List ℕ) (N : ℕ)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseScratchCapacity source target N input ≤
      (N + 2) ^ 181 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  exact coarseHistoryKeyCost_le _ _ (fun _ => le_rfl)

theorem computedFamilyCoarseScratchCapacity_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseScratchCapacity source target N input ≤ (N + 2) ^ 183 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 181 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseScratchCapacity_bound source target N input
    _ ≤ (N + 2) ^ 181 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQuerySetupSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open BinaryFraction

namespace BinaryFraction



theorem onlineParametersAllocation_le_work (word : List Bool) (hpos : 0 < bitWordValue word) :
    onlineParametersAllocation word ≤ (onlineParametersWithWork word hpos).2 := by
  have h5 := bitPowerAllocation_le_work word 5
  have h4 := bitPowerAllocation_le_work word 4
  unfold onlineParametersAllocation onlineParametersWithWork
  dsimp only
  omega



theorem refinementDecrementAllocation_le_work (word : List Bool) (hpos : 0 < bitWordValue word) :
    refinementDecrementAllocation word ≤ (refinementDecrementWithWork word hpos).2 :=
  Nat.add_le_add_right (bitPowerAllocation_le_work word 10) 1

end BinaryFraction



theorem scheduledRefinementAllocation_le_work (N pass : ℕ) :
    scheduledRefinementAllocation N pass ≤ (scheduledRefinementWordWithWork N pass).2 := by
  unfold scheduledRefinementAllocation scheduledRefinementWordWithWork
  split_ifs
  · have h := signedPowerTwoAllocation_le_work
      ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass - smallLogExponent N : ℕ) : ℤ)
    dsimp only
    omega
  · decide



theorem refinementParameterAllocation_le_work (N pass : ℕ) (word : List Bool)
    (hpos : 0 < bitWordValue word) :
    refinementParameterAllocation N pass word ≤ (refinementParameterWordsWithWork N pass word hpos).2 := by
  have ho := onlineParametersAllocation_le_work word hpos
  have hf := scheduledRefinementAllocation_le_work N pass
  have hd := refinementDecrementAllocation_le_work word hpos
  unfold refinementParameterAllocation refinementParameterWordsWithWork
  dsimp only
  omega



theorem refinementBaseAllocation_le_work (word : List Bool) :
    refinementBaseAllocation word ≤ (refinementBaseWithWork word).2 := by
  have hp := bitPowerAllocation_le_work word 10
  have hi := bitAddAllocation_le_work (bitPowerWithWork word 10).1 [true] false
  have ht := trimBitWordAllocation_le_work (bitAddWithWork (bitPowerWithWork word 10).1 [true] false).1
  unfold refinementBaseAllocation refinementBaseWithWork
  dsimp only
  omega



theorem computedQueryPassAllocation_le_work (N pass : ℕ) :
    computedQueryPassAllocation N pass ≤ (computedQueryPassWithWork N pass).2 := by
  have hs := signedPowerTwoAllocation_le_work
    ((dyadicSeedExponent (smallLogExponent N) (computedSeedInitialExponent N) pass : ℕ) : ℤ)
  have hp := refinementParameterAllocation_le_work N pass (inputSmallLog N).bits
    (by rw [bitWordValue_bits]; exact Nat.two_pow_pos _)
  unfold computedQueryPassAllocation computedQueryPassWithWork scheduledSeedWordWithWork
  dsimp only
  omega



theorem computedQuerySetupAllocation_le_work (N : ℕ) :
    computedQuerySetupAllocation N ≤ (computedQuerySetupWithWork N).2 := by
  have hv := vectorMapAllocation_le_work (computedSeedPassCount N + 1)
    (fun i => computedQueryPassWithWork N i.val) (fun i => computedQueryPassAllocation N i.val)
    (fun i => computedQueryPassAllocation_le_work N i.val)
  have hb := refinementBaseAllocation_le_work (inputSmallLog N).bits
  unfold computedQuerySetupAllocation computedQuerySetupWithWork
  dsimp only
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseCopySpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.queryChargedReadHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation
open Filter



theorem physicalCoarseInputStorage_polynomial {M J : ℕ} (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3)
    (entry : PhysicalEntry M J target.length) :
    physicalCoarseInputStorage source target entry ≤ (N + 2) ^ 16 := by
  unfold physicalCoarseInputStorage
  exact coarsePreparedInputStorage_polynomial source target N
    (physicalSourceInterval source.length entry.1).lo
    (physicalSourceInterval source.length entry.1).hi entry.2.lo entry.2.hi
    (physicalSourceInterval source.length entry.1).ordered
    (physicalSourceInterval source.length entry.1).valid entry.2.ordered entry.2.valid hsize hsymbol



theorem computedFamilyCoarseCopyStorage_bound (source target : List ℕ) (N : ℕ)
    (hsize : source.length + target.length ≤ N)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3)
    (input : ComputedFamilyInput source target N) :
    computedFamilyCoarseCopyStorage source target N input ≤
      (N + 2) ^ 16 * (computedFamilyResult source target N input).requests := by
  apply computedFamilyKernelWork_le
  apply coarseHistoryKeyCost_le
  intro entry
  exact physicalCoarseInputStorage_polynomial source target N hsize hsymbol entry

theorem computedFamilyCoarseCopyStorage_polynomial :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ input : ComputedFamilyInput source target N,
      computedFamilyCoarseCopyStorage source target N input ≤ (N + 2) ^ 18 := by
  filter_upwards [computedFamilyResult_requests_near_linear 1 (by norm_num)] with N hr
  intro source target hsize hsymbol input
  have hrequests : (computedFamilyResult source target N input).requests ≤ (N + 2) ^ 2 := by
    have h := hr source target hsize input
    norm_num at h
    exact_mod_cast h
  calc
    _ ≤ (N + 2) ^ 16 * (computedFamilyResult source target N input).requests :=
      computedFamilyCoarseCopyStorage_bound source target N hsize hsymbol input
    _ ≤ (N + 2) ^ 16 * (N + 2) ^ 2 := Nat.mul_le_mul_left _ hrequests
    _ = _ := by rw [← pow_add]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinarySpace
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem integerFinalAllocation_le_work (source target : List ℤ) (N : ℕ)
    (input : ComputedFamilyInput (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerFinalAllocation source target N input ≤ (integerBinaryOutput source target N input).2 := by
  unfold integerFinalAllocation integerBinaryOutput computedQueryAnswerWithWork
  split
  · exact Nat.zero_le _
  · exact (BinaryFraction.finalAnswerAllocation_le_work _ _).trans (by dsimp only; omega)

private theorem sum_cells_le (values : List ℕ) (B : ℕ) (h : ∀ x ∈ values, x ≤ B) :
    values.sum ≤ values.length * B := by
  induction values with
  | nil => simp
  | cons x xs ih =>
    have hx := h x List.mem_cons_self
    have ht := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

private theorem embed_space_power (X K e a : ℕ) (hX : 2 ≤ X) (he : e ≤ K) (ha : a ≤ X ^ e) :
    a ≤ X ^ K := ha.trans (Nat.pow_le_pow_right (by omega) he)

private theorem bounded_space_sum (X K : ℕ) (terms : List ℕ) (hX : 2 ≤ X)
    (hl : terms.length ≤ 16) (ht : ∀ a ∈ terms, a ≤ X ^ K) :
    terms.sum ≤ X ^ (K + 4) := by
  have hs := sum_cells_le terms (X ^ K) ht
  have h16 : 16 ≤ X ^ 4 := (by decide : 16 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
  calc
    _ ≤ terms.length * X ^ K := hs
    _ ≤ X ^ 4 * X ^ K := Nat.mul_le_mul_right _ (hl.trans h16)
    _ = _ := by rw [← pow_add]; congr 1; omega

theorem integerBinarySpace_polynomial_oai (C : ℕ) (epsilon : BinaryFraction)
    (hepsilon : 0 < epsilon.value) :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℤ, source.length + target.length ≤ N →
      (∀ z ∈ source ++ target, z.natAbs ≤ (N + 2) ^ C) →
      ∀ outcome, integerBinarySpace source target N epsilon outcome ≤ (N + 2) ^ (C + 65564) := by
  filter_upwards [physicalLargeInput_eventually epsilon hepsilon,
    integerPreevaluationWork_near_linear C 1 (by norm_num), integerStoredDataSpace_polynomial C,
    integerQueryWidths C, computedQueryTemporaryCells_polynomial, integer_encoded_symbol_bits C,
    computedFamilyCoarseCopyStorage_polynomial, computedFamilyCoarseArrayCapacity_polynomial,
    computedFamilyCoarseScratchCapacity_polynomial, computedFamilyCoarseControlCapacity_polynomial]
    with N hlarge hpre hstored hwidth htemp hsymbols hcopy harray hscratch hcontrol
  intro source target hsize halphabet outcome
  let X := N + 2
  let K := C + 65560
  change _ ≤ X ^ (C + 65564)
  rw [← show K + 4 = C + 65564 by dsimp only [K]]
  have hX : 2 ≤ X := by dsimp only [X]; omega
  have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
  have hell := hlarge.2.1.1
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hsz : (source.map integerSymbolCode).length + (target.map integerSymbolCode).length ≤ N := by
    simpa only [List.length_map] using hsize
  have hs (a) (ha : a ∈ source.map integerSymbolCode) : a < 2 ^ integerInputSymbolBits source target := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  have ht (a) (ha : a ∈ target.map integerSymbolCode) : a < 2 ^ integerInputSymbolBits source target := by
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  have hp : (target.map integerSymbolCode).length ≤ 2 ^ integerInputPositionBits target := by
    simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le
  have hpre2 : integerPreevaluationWork source target N epsilon ≤ X ^ 2 := by
    have h := hpre source target hsize halphabet epsilon
    norm_num at h
    exact_mod_cast h
  have hpreK : 8 * integerPreevaluationWork source target N epsilon ≤ X ^ K := by
    apply embed_space_power X K 5 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X ^ 3 * X ^ 2 := Nat.mul_le_mul ((by decide : 8 ≤ (2 : ℕ) ^ 3).trans
        (Nat.pow_le_pow_left hX 3)) hpre2
      _ = _ := by rw [← pow_add]
  have hstoredK : 2 * integerStoredDataSpace source target ≤ X ^ K := by
    apply embed_space_power X K (C + 23) _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X * X ^ (C + 22) := Nat.mul_le_mul hX (hstored source target hsize halphabet)
      _ = _ := by rw [← pow_succ']
  have hlinearK : 8 * (N + 1) ≤ X ^ K := by
    apply embed_space_power X K 4 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ X ^ 3 * X := Nat.mul_le_mul ((by decide : 8 ≤ (2 : ℕ) ^ 3).trans
        (Nat.pow_le_pow_left hX 3)) (by dsimp only [X]; omega)
      _ = _ := by rw [← pow_succ]
  have hdpK : suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) ≤ X ^ K := by
    apply embed_space_power X K 10 _ hX (by dsimp only [K]; omega)
    calc
      _ ≤ 50 * (N + 1) ^ 4 := suffixDPAllocation_polynomial _ _ N hsz
      _ ≤ X ^ 6 * X ^ 4 := Nat.mul_le_mul ((by decide : 50 ≤ (2 : ℕ) ^ 6).trans
        (Nat.pow_le_pow_left hX 6)) (Nat.pow_le_pow_left (by dsimp only [X]; omega) 4)
      _ = _ := by rw [← pow_add]
  have hfallback : 8 * integerPreevaluationWork source target N epsilon +
      2 * integerStoredDataSpace source target +
      suffixDPAllocation (source.map integerSymbolCode) (target.map integerSymbolCode) + 8 * (N + 1) ≤
      X ^ (K + 4) := by
    have hu : 4 ≤ X ^ 4 := (by decide : 4 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
    calc
      _ ≤ 4 * X ^ K := by omega
      _ ≤ X ^ 4 * X ^ K := Nat.mul_le_mul_right _ hu
      _ = _ := by rw [← pow_add, Nat.add_comm 4 K]
  simp only [integerBinarySpace, hlarge, ite_true, if_true]
  cases outcome with
  | inl unitValue => exact hfallback
  | inr execution =>
    let input := computedExecutionAccepted (source.map integerSymbolCode) (target.map integerSymbolCode) N execution
    have hwidths := hwidth source target hsize halphabet
    have hmemo := computedQueryMemoResult_storage (source.map integerSymbolCode) (target.map integerSymbolCode) N
      (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)
      input hN hell hf hsz hlarge.2.2 hs ht hp rfl
    have htmp := htemp (source.map integerSymbolCode) (target.map integerSymbolCode) hsz input
      (integerOccurrenceIndex source target) (integerInputSymbolBits source target) (integerInputPositionBits target)
      hwidths.1 hwidths.2 hs ht hp rfl
    have hset := (computedQuerySetupAllocation_le_work N).trans (computedQuerySetupWithWork_cost N hN hell)
    have hH48 : inputHeight N ^ 12 ≤ X ^ 48 :=
      (Nat.pow_le_pow_left (computed_height_polynomial N) 12).trans_eq (by rw [← pow_mul])
    have hsetupK := embed_space_power X K 48 _ hX (by dsimp only [K]; omega) (hset.trans hH48)
    have hmemoK := embed_space_power (N + 2) K 65557
      (computedQueryMemoResult (source.map integerSymbolCode) (target.map integerSymbolCode) N
        (integerOccurrenceIndex source target) (integerInputSymbolBits source target)
        (integerInputPositionBits target) input).memory.fractionStorage hX
      ((by decide : 65557 ≤ 65560).trans (Nat.le_add_left 65560 C)) hmemo
    have htmpK := embed_space_power X K 20 _ hX (by dsimp only [K]; omega) htmp
    have hcopyK := embed_space_power X K 18 _ hX (by dsimp only [K]; omega)
      (hcopy _ _ hsz (hsymbols source target halphabet) input)
    have harrayK := embed_space_power X K 39 _ hX (by dsimp only [K]; omega) (harray _ _ hsz input)
    have hscratchK := embed_space_power X K 183 _ hX (by dsimp only [K]; omega) (hscratch _ _ hsz input)
    have hcontrolK := embed_space_power X K 184 _ hX (by dsimp only [K]; omega) (hcontrol _ _ hsz input)
    have hbufferK : 4 * (inputHeight N + (integerParameters N).B + 4) ≤ X ^ K := by
      have hH : inputHeight N ≤ X ^ 4 := computed_height_polynomial N
      have hB : (integerParameters N).B ≤ X ^ 4 :=
        BinaryFraction.computedCoarseBranching_polynomial N hN
          (two_hundred_le_two_pow_thousand.trans hell)
      have h4 : 4 ≤ X ^ 4 := (by decide : 4 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
      have h16 : 16 ≤ X ^ 4 := (by decide : 16 ≤ (2 : ℕ) ^ 4).trans (Nat.pow_le_pow_left hX 4)
      apply embed_space_power X K 8 _ hX (by dsimp only [K]; omega)
      calc
        _ ≤ 4 * (X ^ 4 + X ^ 4 + X ^ 4) :=
          Nat.mul_le_mul_left 4 (Nat.add_le_add (Nat.add_le_add hH hB) h4)
        _ = 12 * X ^ 4 := by ring
        _ ≤ 16 * X ^ 4 := Nat.mul_le_mul_right _ (by decide : 12 ≤ 16)
        _ ≤ X ^ 4 * X ^ 4 := Nat.mul_le_mul_right _ h16
        _ = _ := by rw [← pow_add]
    have houtK : integerFinalAllocation source target N input ≤ X ^ K := by
      have hout := (integerFinalAllocation_le_work source target N input).trans
        (integerBinaryOutput_cost source target N epsilon hlarge hsize input)
      have hH40 : inputHeight N ^ 10 ≤ X ^ 40 :=
        (Nat.pow_le_pow_left (computed_height_polynomial N) 10).trans_eq (by rw [← pow_mul])
      have hn : N ≤ X ^ 40 := (by dsimp only [X]; omega : N ≤ X).trans (Nat.le_pow (by decide))
      apply embed_space_power X K 41 _ hX (by dsimp only [K]; omega)
      calc
        _ ≤ 2 * X ^ 40 := by omega
        _ ≤ X * X ^ 40 := Nat.mul_le_mul_right _ hX
        _ = _ := by rw [← pow_succ']
    apply bounded_space_sum X K _ hX (by change 12 ≤ 16; decide)
    intro a ha
    simp only [integerAcceptedSpaceTerms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hpreK
    · exact hstoredK
    · exact hsetupK
    · exact hmemoK
    · exact htmpK
    · exact hcopyK
    · exact harrayK
    · exact hscratchK
    · exact hcontrolK
    · exact hbufferK
    · exact houtK
    · exact hlinearK

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.integerBinarySpace_polynomial_oai := @OAI.EditApproximation.integerBinarySpace_polynomial_oai
