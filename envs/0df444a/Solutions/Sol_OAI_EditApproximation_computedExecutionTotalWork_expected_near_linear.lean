-- Prove2me | solution 1 for OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:34:05.037018+00:00
-- url     : https://prove2.me/submissions/c086b7f0-02e0-43e8-8fe8-a63003e5e19a

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
import Definitions.Def_EditApproxScheme_05
import Definitions.Def_EditApproxScheme_06
import Definitions.Def_EditApproxScheme_08
import Definitions.Def_EditApproxScheme_09
import Definitions.Def_EditApproxScheme_10
import Definitions.Def_EditApproxScheme_11
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedExecutionCoarseSamplingWork_expected_near_linear
import Theorems.Thm_OAI_EditApproximation_computedExecutionIndexedCoarseWork_expected_near_linear
import Theorems.Thm_OAI_EditApproximation_computedExecutionNonlocalWork_expected_near_linear
import Theorems.Thm_OAI_EditApproximation_computedFamilyCoarseInputWork_le
import Theorems.Thm_OAI_EditApproximation_computedFamilyResult_requests_le
import Theorems.Thm_OAI_EditApproximation_weighted_dependency_div_height_tendsto

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryArithmeticWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Literal Boolean ripple addition. The counter counts Boolean gates and
bit writes, not unit-cost arithmetic on unbounded integers. -/

namespace EditApproximation







theorem bitAddWithWork_cost (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem bitAddWithWork_length (left right : List Bool) (carry : Bool) :
    (bitAddWithWork left right carry).1.length ≤ max left.length right.length + 1 := by
  induction left generalizing right carry with
  | nil =>
    simp only [bitAddWithWork]
    induction right generalizing carry with
    | nil => cases carry <;> simp [bitAddNilLeftWithWork]
    | cons b bs ih =>
      simp only [bitAddNilLeftWithWork, List.length_cons, List.length_nil, Nat.zero_max]
      have h := ih (bitCarry false b carry)
      simp only [List.length_nil, Nat.zero_max] at h
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      simp only [bitAddWithWork, List.length_cons, List.length_nil, Nat.max_zero]
      have h := ih [] (bitCarry a false carry)
      simp only [List.length_nil, Nat.max_zero] at h
      omega
    | cons b bs =>
      simp only [bitAddWithWork, List.length_cons]
      have h := ih bs (bitCarry a b carry)
      omega

theorem binaryNaturalAddWithWork_cost (a b : ℕ) :
    (binaryNaturalAddWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalAddWithWork, Nat.size_eq_bits_len] using
    bitAddWithWork_cost a.bits b.bits false



theorem bitMulWithWork_length (left right : List Bool) :
    (bitMulWithWork left right).1.length ≤ 2 * left.length + right.length + 1 := by
  induction left with
  | nil => simp [bitMulWithWork]
  | cons bit bits ih =>
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      omega
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      have h := bitAddWithWork_length (false :: (bitMulWithWork bits right).1) right false
      simp only [List.length_cons] at h
      omega

theorem bitMulWithWork_cost (left right : List Bool) :
    (bitMulWithWork left right).2 ≤ 20 * (left.length + 1) * (left.length + right.length + 1) := by
  induction left with
  | nil => simp [bitMulWithWork]; omega
  | cons bit bits ih =>
    have hlength := bitMulWithWork_length bits right
    have hadd := bitAddWithWork_cost (false :: (bitMulWithWork bits right).1) right false
    simp only [List.length_cons] at hadd
    cases bit
    · simp only [bitMulWithWork, Bool.false_eq_true, ↓reduceIte, List.length_cons]
      nlinarith only [ih]
    · simp only [bitMulWithWork, ↓reduceIte, List.length_cons]
      nlinarith only [ih, hlength, hadd]



theorem binaryNaturalMulWithWork_cost (a b : ℕ) :
    (binaryNaturalMulWithWork a b).2 ≤ 20 * (Nat.size a + 1) * (Nat.size a + Nat.size b + 1) := by
  simpa only [binaryNaturalMulWithWork, Nat.size_eq_bits_len] using bitMulWithWork_cost a.bits b.bits

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySubtractWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Ripple-borrow subtraction, used after the magnitude comparison in
signed-integer addition. No unit-cost operation on unbounded integers is
used by this Boolean routine. -/

namespace EditApproximation





theorem bitSubtractWithWork_cost (left right : List Bool) (borrow : Bool) :
    (bitSubtractWithWork left right borrow).2.2 ≤ 9 * (left.length + right.length) + 1 := by
  induction left generalizing right borrow with
  | nil =>
    induction right generalizing borrow with
    | nil => simp [bitSubtractWithWork, bitSubtractNilLeftWithWork]
    | cons b bs ih =>
      have h := ih (bitBorrow false b borrow)
      simp only [bitSubtractWithWork, bitSubtractNilLeftWithWork, List.length_cons, List.length_nil] at *
      omega
  | cons a as ih =>
    cases right with
    | nil =>
      have h := ih [] (bitBorrow a false borrow)
      simp only [bitSubtractWithWork, List.length_cons, List.length_nil] at *
      omega
    | cons b bs =>
      have h := ih bs (bitBorrow a b borrow)
      simp only [bitSubtractWithWork, List.length_cons] at *
      omega



theorem binaryNaturalSubtractWithWork_cost (a b : ℕ) :
    (binaryNaturalSubtractWithWork a b).2 ≤ 9 * (Nat.size a + Nat.size b) + 1 := by
  simpa only [binaryNaturalSubtractWithWork, Nat.size_eq_bits_len] using
    bitSubtractWithWork_cost a.bits b.bits false

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeParameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Depth of the computed interval tree

The branching factor is the power of two prescribed by the algorithm.
Ceiling logarithms count physical levels, including empty intervals.
-/

namespace EditApproximation

open Finset



theorem computed_branching_bounds (N : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) :
    2 ≤ (integerParameters N).M ∧
      inputSmallLog N ≤ 50 * (heightExponent N / 20) ∧
      heightExponent N / 20 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hquot := Nat.mod_lt (heightExponent N) (by decide : 0 < 20)
  have hsplit := Nat.mod_add_div (heightExponent N) 20
  have hk : 1 ≤ heightExponent N / 20 := by omega
  have hpow : 2 ≤ 2 ^ (heightExponent N / 20) := by
    simpa using pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) hk
  have hexp : heightExponent N ≤ inputHeight N := by
    exact (Nat.lt_pow_self (by decide : 1 < 2)).le
  exact ⟨hpow, by omega, (Nat.div_le_self _ _).trans hexp⟩

theorem computed_tree_depth_bound (N nx : ℕ) (hN : 0 < N) (hnx : nx ≤ N)
    (hell : 200 ≤ inputSmallLog N) :
    intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤ 100 * inputHeight N := by
  let k := heightExponent N / 20
  have hbranch := computed_branching_bounds N hN hell
  have hbound : max 1 nx ≤ 2 ^ inputHeight N := by
    apply max_le Nat.one_le_two_pow
    exact hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
  have hlog : Nat.clog 2 (max 1 nx) ≤ inputHeight N :=
    (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2 hbound
  have hdepth : intervalTreeDepth (integerParameters N).M nx =
      (Nat.clog 2 (max 1 nx) + (k - 1)) / k := by
    exact Nat.clog_pow_left 2 k (max 1 nx)
  have hproduct := Nat.div_mul_le_self (Nat.clog 2 (max 1 nx) + (k - 1)) k
  rw [← hdepth] at hproduct
  have hscale := Nat.mul_le_mul_left
    (intervalTreeDepth (integerParameters N).M nx) hbranch.2.1
  change intervalTreeDepth (integerParameters N).M nx * inputSmallLog N ≤
    intervalTreeDepth (integerParameters N).M nx * (50 * k) at hscale
  have hkH : k ≤ inputHeight N := hbranch.2.2
  have hsub : k - 1 ≤ k := Nat.sub_le _ _
  nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinaryLocalGrid
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Local endpoint lists executed with binary division, multiplication,
subtraction and validity comparisons. Only the bounded grid-index range
is visited. -/

namespace EditApproximation



theorem saturatingSubtractWithWork_cost (a b : ℕ) :
    (saturatingSubtractWithWork a b).2 ≤ 13 * (Nat.size a + Nat.size b) + 4 := by
  have htest := binaryNaturalCompareWithWork_cost a b
  have hsub := binaryNaturalSubtractWithWork_cost a b
  unfold saturatingSubtractWithWork
  dsimp only
  split_ifs <;> omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalLeaves
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramOnlineGuard_decidable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Exact source leaves remain exact throughout the actual physical warmup. -/

namespace EditApproximation

open Finset

theorem physicalSource_length_eq {α : Type*} {M J : ℕ} (source : List α)
    (node : PhysicalNode M J) : (physicalSource source node).length =
      (physicalSourceInterval source.length node).hi - (physicalSourceInterval source.length node).lo := by
  simp only [physicalSource, substring, List.length_drop, List.length_take,
    Nat.min_eq_left (physicalSourceInterval source.length node).valid]

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
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! A computable fixed-accuracy cutoff. The algorithm tests the small-log
conditions directly; it does not construct the double exponential bound. -/

namespace EditApproximation





theorem heightExponent_above_double_power (N exponent : ℕ) (h : 2 ^ (2 ^ exponent) ≤ N) :
    exponent ≤ heightExponent N := by
  have hfirst := Nat.clog_mono_right 2 (h.trans (Nat.le_add_right N 2))
  rw [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ))] at hfirst
  have hsecond := Nat.clog_mono_right 2 hfirst
  simpa only [Nat.clog_pow _ _ (by decide : 1 < (2 : ℕ)), heightExponent] using hsecond

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

theorem inputSmallLog_real_tendsto :
    Tendsto (fun N => (inputSmallLog N : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp inputSmallLog_tendsto

theorem log_smallLog_div_smallLog_tendsto :
    Tendsto (fun N => Real.log (inputSmallLog N : ℝ) / inputSmallLog N) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputSmallLog_real_tendsto

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterLocalAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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

theorem computed_branching_square_le_height (N : ℕ) :
    ((integerParameters N).M : ℝ) ^ 2 ≤ inputHeight N := by
  have hexponent : heightExponent N / 20 * 2 ≤ heightExponent N := by omega
  have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [integerParameters, inputHeight, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul] using h

/-- This directly controls the scalar exponent `M q ell` occurring in the
local wide-action enumeration. -/
theorem branching_smallLog_polynomial_div_height_tendsto (k : ℕ) :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      (inputSmallLog N : ℝ) ^ k / inputHeight N) atTop (𝓝 0) := by
  have hupper : Tendsto (fun N => Real.sqrt
      ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (smallLog_polynomial_div_height_tendsto (2 * k)).sqrt
  apply squeeze_zero' (Eventually.of_forall fun N =>
    div_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _))
      (Nat.cast_nonneg _)) _ hupper
  apply Eventually.of_forall
  intro N
  apply Real.le_sqrt_of_sq_le
  have hH : (0 : ℝ) < inputHeight N := by
    exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hM := computed_branching_square_le_height N
  have hproduct := mul_le_mul_of_nonneg_right hM
    (pow_nonneg (Nat.cast_nonneg (inputSmallLog N)) (2 * k))
  rw [div_pow, mul_pow, ← pow_mul, Nat.mul_comm k 2]
  apply (div_le_iff₀ (sq_pos_of_pos hH)).2
  calc
    ((integerParameters N).M : ℝ) ^ 2 * (inputSmallLog N : ℝ) ^ (2 * k) ≤
        (inputHeight N : ℝ) * (inputSmallLog N : ℝ) ^ (2 * k) := hproduct
    _ = ((inputSmallLog N : ℝ) ^ (2 * k) / inputHeight N) *
        (inputHeight N : ℝ) ^ 2 := by field_simp [hH.ne']

theorem coarseExponent_le_smallLog (N : ℕ) :
    coarseExponent (inputSmallLog N) ≤ inputSmallLog N := by
  have h := coarseExponent_fourth_power (inputSmallLog N)
  have hp : coarseExponent (inputSmallLog N) ≤ coarseExponent (inputSmallLog N) ^ 4 := by
    exact Nat.le_pow (by decide : 0 < 4)
  exact hp.trans (h.trans (Nat.log_le_self 2 _))

theorem local_enumeration_exponent_div_height_tendsto :
    Tendsto (fun N => ((integerParameters N).M : ℝ) *
      ((coarseExponent (inputSmallLog N) : ℝ) + 1) * inputSmallLog N / inputHeight N)
      atTop (𝓝 0) := by
  have hupper := (branching_smallLog_polynomial_div_height_tendsto 2).const_mul 2
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hupper
  apply Eventually.of_forall
  intro N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have hprod := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hq (Nat.cast_nonneg (inputSmallLog N)))
    (Nat.cast_nonneg (integerParameters N).M)
  have hdiv := div_le_div_of_nonneg_right hprod (Nat.cast_nonneg (inputHeight N))
  first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

theorem inputHeight_real_log (N : ℕ) :
    Real.log (inputHeight N : ℝ) = (heightExponent N : ℝ) * Real.log 2 := by
  simp only [inputHeight, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]

theorem encoding_exponent_div_height_tendsto :
    Tendsto (fun N => ((coarseExponent (inputSmallLog N) : ℝ) + 1) *
      Real.log (inputHeight N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := (smallLog_polynomial_div_height_tendsto 2).const_mul (2 * Real.log 2)
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (by positivity)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := heightExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hp : (coarseExponent (inputSmallLog N) : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast coarseExponent_le_smallLog N
  have hell : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hq : (coarseExponent (inputSmallLog N) : ℝ) + 1 ≤ 2 * inputSmallLog N := by linarith
  have he : (heightExponent N : ℝ) ≤ inputSmallLog N := by
    exact_mod_cast (inputSmallLog_bounds N hN).1
  have hprod := mul_le_mul hq he (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ 2 * inputSmallLog N)
  have hlog := mul_le_mul_of_nonneg_right hprod (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2))
  rw [inputHeight_real_log]
  have hdiv := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (inputHeight N))
  first | (convert hdiv using 1 <;> first | (with_reducible_and_instances rfl) | ring) | exact (le_of_eq (by ring)).trans (hdiv.trans (le_of_eq (by ring)))

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterDependencyAsymptotics
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The actual pass/index count and the exponents in the dependency-path
bound. These statements concern computed numbers, independently of the
proof that an evaluator satisfies the dependency budgets. -/

namespace EditApproximation

open Filter
open scoped Topology

/-- A uniform depth upper bound is obtained by using the total length as
the source length. -/
theorem tree_logSmallLog_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) *
      Real.log (inputSmallLog N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  have hupper := log_smallLog_div_smallLog_tendsto.const_mul 100
  simp only [mul_zero] at hupper
  apply squeeze_zero' (Eventually.of_forall fun N => by
    apply div_nonneg
    · apply mul_nonneg (Nat.cast_nonneg _)
      apply Real.log_nonneg
      exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
    · exact Nat.cast_nonneg _) _ hupper
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  have hbound : (computedMaxTreeDepth N : ℝ) * inputSmallLog N ≤ 100 * (inputHeight N : ℝ) := by
    exact_mod_cast computed_tree_depth_bound N N hN le_rfl hell
  have hlog : 0 ≤ Real.log (inputSmallLog N : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_two_pow (n := smallLogExponent N)
  have hH : (0 : ℝ) < inputHeight N := by exact_mod_cast Nat.two_pow_pos (heightExponent N)
  have hellpos : (0 : ℝ) < inputSmallLog N := by exact_mod_cast Nat.two_pow_pos (smallLogExponent N)
  have hscaled := mul_le_mul_of_nonneg_right hbound hlog
  rw [← mul_div_assoc]
  apply (div_le_div_iff₀ hH hellpos).2
  nlinarith only [hscaled]

theorem tree_depth_div_height_tendsto :
    Tendsto (fun N => (computedMaxTreeDepth N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ tree_logSmallLog_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputSmallLog_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact le_mul_of_one_le_right (Nat.cast_nonneg _) hlog

theorem dependency_index_div_height_tendsto :
    Tendsto (fun N => (computedDependencyIndexCount N : ℝ) / inputHeight N) atTop (𝓝 0) := by
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    _ weighted_dependency_div_height_tendsto
  filter_upwards [(Real.tendsto_log_atTop.comp inputHeight_real_tendsto).eventually
    (eventually_ge_atTop 1)] with N hlog
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  calc
    (computedDependencyIndexCount N : ℝ) ≤
        ((coarseExponent (inputSmallLog N) : ℝ) + 1) * computedDependencyIndexCount N := by
      have hm : (0 : ℝ) ≤ (coarseExponent (inputSmallLog N) : ℝ) * computedDependencyIndexCount N :=
        mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      nlinarith only [hm]
    _ ≤ _ := le_mul_of_one_le_right (by positivity) hlog

/-- Every fixed choice of the two branching-budget constants yields a
sublinear logarithmic overhead in the dependency-path bound. -/
theorem computedDependencyOverheadExponent_tendsto (C₁ C₂ : ℝ) :
    Tendsto (fun N => computedDependencyOverheadExponent C₁ C₂ N / inputHeight N)
      atTop (𝓝 0) := by
  have htwo : Tendsto (fun N => 2 / (inputHeight N : ℝ)) atTop (𝓝 0) := by
    simpa only [Pi.inv_apply, mul_zero, div_eq_mul_inv] using inputHeight_real_tendsto.inv_tendsto_atTop.const_mul 2
  have h := (((tree_depth_div_height_tendsto.add dependency_index_div_height_tendsto).add htwo).const_mul
    (1 + Real.log 2)).add ((tree_logSmallLog_div_height_tendsto.const_mul C₁).add
      (weighted_dependency_div_height_tendsto.const_mul C₂))
  simp only [zero_add, mul_zero] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  unfold computedDependencyOverheadExponent
  ring

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

theorem sublinear_height_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ (N : ℕ) in atTop, (N + 2 : ℝ) * Real.exp (f N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [subexponential_height_to_input f hf epsilon hepsilon] with N hN
  rw [Real.rpow_add (by positivity : (0 : ℝ) < N + 2), Real.rpow_one]
  exact mul_le_mul_of_nonneg_left hN (by positivity)

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWidthEnvelope
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A parameter-only majorant for every executed dependency tree. It is
independent of the accepted random values and of all accuracy events. -/

namespace EditApproximation

open Filter
open scoped Topology

theorem computedWidthEnvelope_nonneg (N : ℕ) : 0 ≤ computedWidthEnvelope N := by
  unfold computedWidthEnvelope
  positivity

theorem computedWidthEnvelope_mul_exp_near_linear (f : ℕ → ℝ)
    (hf : Tendsto (fun N => f N / inputHeight N) atTop (𝓝 0))
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * Real.exp (f N) ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := ((computedDependencyOverheadExponent_tendsto 257 512).add
    (hlog.const_mul 2)).add hf
  simp only [mul_zero, add_zero] at hlimit
  have hfinal := sublinear_height_near_linear
    (fun N => computedDependencyOverheadExponent 257 512 N +
      2 * Real.log (inputHeight N : ℝ) + f N) (by
        convert hlimit using 1
        all_goals try with_reducible_and_instances rfl
        ext N
        ring) epsilon hepsilon
  filter_upwards [hfinal] with N hN
  convert hN using 1
  all_goals try with_reducible_and_instances rfl
  unfold computedWidthEnvelope
  rw [Real.exp_add, Real.exp_add]
  have hp : Real.exp (2 * Real.log (inputHeight N : ℝ)) = (inputHeight N : ℝ) ^ 2 := by
    simpa using (nat_pow_eq_exp_log (inputHeight N) 2 (Nat.two_pow_pos _)).symm
  rw [hp]
  ring

theorem computedWidthEnvelope_weighted_near_linear (C : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, computedWidthEnvelope N * (inputHeight N : ℝ) ^ C ≤
      (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hlog : Tendsto (fun N => Real.log (inputHeight N : ℝ) / inputHeight N)
      atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp inputHeight_real_tendsto
  have hlimit := hlog.const_mul (C : ℝ)
  simp only [mul_zero] at hlimit
  have hf : Tendsto (fun N => ((C : ℝ) * Real.log (inputHeight N : ℝ)) / inputHeight N)
      atTop (𝓝 0) := by convert hlimit using 1 <;> first | (with_reducible_and_instances rfl) | (ext N; ring)
  filter_upwards [computedWidthEnvelope_mul_exp_near_linear _ hf epsilon hepsilon] with N hN
  rwa [← nat_pow_eq_exp_log (inputHeight N) C (Nat.two_pow_pos _)] at hN

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseGlobalSeed
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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

theorem computed_coarse_height_large (N : ℕ) (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    256 ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hr : 8 ≤ heightExponent N := by omega
  change 2 ^ 8 ≤ 2 ^ heightExponent N
  exact Nat.pow_le_pow_right (by decide : 0 < 2) hr

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

theorem coarseRangeCopyWithWork_cost (read : ℕ → ℕ) (limit A S start length : ℕ)
    (hbits : ∀ i ≤ limit, Nat.size i ≤ A)
    (hsymbol : ∀ i < limit, Nat.size (read i) ≤ S) (hspan : start + length ≤ limit) :
    (coarseRangeCopyWithWork read start length).2 ≤ (length + 1) * (40 * (A + 1) + S) := by
  induction length generalizing start with
  | zero => simp only [coarseRangeCopyWithWork]; omega
  | succ length ih =>
    have hstart : start < limit := by omega
    have ha := hbits start (by omega)
    have hs := hsymbol start hstart
    have hc := binaryNaturalAddWithWork_cost start 1
    rw [show Nat.size 1 = 1 by decide] at hc
    have hr := ih (start + 1) (by omega)
    simp only [coarseRangeCopyWithWork, binaryNaturalAddWithWork_value]
    nlinarith only [ha, hs, hc, hr, Nat.zero_le A, Nat.zero_le S]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseSliceCopy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarseRangeCopyWithWork_input_cost (input : List ℕ) (lo hi A S : ℕ)
    (hlo : lo ≤ hi) (hhi : hi ≤ input.length) (haddress : Nat.size input.length ≤ A)
    (hsymbol : ∀ a ∈ input, Nat.size a ≤ S) :
    (coarseRangeCopyWithWork (fun i => input[i]?.getD 0) lo (hi - lo)).2 ≤
      (hi - lo + 1) * (40 * (A + 1) + S) := by
  apply coarseRangeCopyWithWork_cost _ input.length A S
  · intro i hi
    exact (Nat.size_le_size hi).trans haddress
  · intro i hi
    simp only [List.getElem?_eq_getElem hi, Option.getD_some]
    exact hsymbol _ (List.getElem_mem hi)
  · omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInputGuard
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

theorem coarseInputGuardWithWork_cost (sourceLo sourceHi targetLo targetHi A : ℕ)
    (hslo : Nat.size sourceLo ≤ A) (hshi : Nat.size sourceHi ≤ A)
    (htlo : Nat.size targetLo ≤ A) (hthi : Nat.size targetHi ≤ A) :
    (coarseInputGuardWithWork sourceLo sourceHi targetLo targetHi).2 ≤ 1000 * (A + 1) := by
  have hs := saturatingSubtractWithWork_cost sourceHi sourceLo
  have ht := saturatingSubtractWithWork_cost targetHi targetLo
  have hsw : Nat.size (sourceHi - sourceLo) ≤ A :=
    (Nat.size_le_size (Nat.sub_le _ _)).trans hshi
  have htw : Nat.size (targetHi - targetLo) ≤ A :=
    (Nat.size_le_size (Nat.sub_le _ _)).trans hthi
  have hm := binaryNaturalMulWithWork_cost 2 (sourceHi - sourceLo)
  have hmw := natural_product_bit_length 2 (sourceHi - sourceLo)
  have hc := binaryNaturalCompareWithWork_cost (2 * (sourceHi - sourceLo)) (targetHi - targetLo)
  rw [show Nat.size 2 = 2 by decide] at hm hmw
  simp only [coarseInputGuardWithWork, saturatingSubtractWithWork_value, binaryNaturalMulWithWork_value]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Coarse_CoarseInputPreparation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem coarsePreparedSlicesWithWork_cost (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi A S : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hsbits : Nat.size source.length ≤ A) (htbits : Nat.size target.length ≤ A)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ S) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).2 ≤
      1000 * (A + 1) + (3 * (sourceHi - sourceLo) + 2) * (40 * (A + 1) + S) := by
  have hg := coarseInputGuardWithWork_cost sourceLo sourceHi targetLo targetHi A
    ((Nat.size_le_size (hslo.trans hshi)).trans hsbits) ((Nat.size_le_size hshi).trans hsbits)
    ((Nat.size_le_size (htlo.trans hthi)).trans htbits) ((Nat.size_le_size hthi).trans htbits)
  by_cases hlong : 2 * (sourceHi - sourceLo) < targetHi - targetLo
  · simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, hlong, decide_true, ite_true, if_true]
    exact hg.trans (Nat.le_add_right _ _)
  · have hs := coarseRangeCopyWithWork_input_cost source sourceLo sourceHi A S hslo hshi hsbits
      (fun a ha => hsymbol a (List.mem_append_left target ha))
    have ht := coarseRangeCopyWithWork_input_cost target targetLo targetHi A S htlo hthi htbits
      (fun a ha => hsymbol a (List.mem_append_right source ha))
    simp only [coarsePreparedSlicesWithWork, coarseInputGuardWithWork_value, hlong, decide_false, Bool.false_eq_true, ite_false, if_false]
    have hm := Nat.mul_le_mul_right (40 * (A + 1) + S)
      (show (sourceHi - sourceLo + 1) + (targetHi - targetLo + 1) ≤
        3 * (sourceHi - sourceLo) + 2 by omega)
    nlinarith only [hg, hs, ht, hm]

theorem coarsePreparedSlicesWithWork_height_bound (source target : List ℕ)
    (sourceLo sourceHi targetLo targetHi H : ℕ)
    (hslo : sourceLo ≤ sourceHi) (hshi : sourceHi ≤ source.length)
    (htlo : targetLo ≤ targetHi) (hthi : targetHi ≤ target.length)
    (hH : 100 ≤ H) (hsbits : Nat.size source.length ≤ H ^ 3)
    (htbits : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    (coarsePreparedSlicesWithWork source target sourceLo sourceHi targetLo targetHi).2 ≤
      H ^ 6 * (sourceHi - sourceLo + 1) := by
  have hc := coarsePreparedSlicesWithWork_cost source target sourceLo sourceHi targetLo targetHi
    (H ^ 3) (H ^ 3) hslo hshi htlo hthi hsbits htbits hsymbol
  have hp : 1 ≤ H ^ 3 := one_le_pow₀ (by omega)
  have hs : 5000 ≤ H ^ 3 := by
    have h := Nat.pow_le_pow_left hH 3
    norm_num at h
    omega
  have hm : 5000 * H ^ 3 ≤ H ^ 6 := by
    calc
      _ ≤ H ^ 3 * H ^ 3 := Nat.mul_le_mul_right _ hs
      _ = _ := by rw [← pow_add]
  have hmul := Nat.mul_le_mul_right (sourceHi - sourceLo + 1) hm
  nlinarith only [hc, hp, hmul, Nat.zero_le (sourceHi - sourceLo)]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open Filter MeasureTheory

private theorem power_succ_add_one (x : ℝ) (hx : 2 ≤ x) (n : ℕ) :
    x ^ n + 1 ≤ x ^ (n + 1) := by
  have hnonneg : 0 ≤ x ^ n := pow_nonneg (by linarith) _
  have hone : 1 ≤ x ^ n := one_le_pow₀ (by linarith)
  calc
    _ ≤ x ^ n + x ^ n := add_le_add le_rfl hone
    _ = x ^ n * 2 := by ring
    _ ≤ x ^ n * x := mul_le_mul_of_nonneg_left hx hnonneg
    _ = _ := (pow_succ _ _).symm


 theorem computedFamilyResult_requests_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 92 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize input
  have hH : (2 : ℝ) ≤ inputHeight N := by
    exact_mod_cast (show 2 ≤ inputHeight N from
      ((by decide : 2 ≤ 200).trans two_hundred_le_two_pow_thousand).trans (hell.trans (computed_smallLog_le_height N)))
  have hp : (inputHeight N : ℝ) ^ 91 + 1 ≤ (inputHeight N : ℝ) ^ 92 := by
    exact power_succ_add_one (inputHeight N) hH 91
  calc
    _ ≤ ((inputHeight N : ℝ) ^ 91 + 1) * computedWidthEnvelope N :=
      computedFamilyResult_requests_le source target N (by omega) hell hsize hB input
    _ ≤ (inputHeight N : ℝ) ^ 92 * computedWidthEnvelope N :=
      mul_le_mul_of_nonneg_right hp (computedWidthEnvelope_nonneg N)
    _ ≤ _ := by simpa only [mul_comm] using hw



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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedCoarseInputWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter MeasureTheory

theorem computedFamilyCoarseInputWork_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
        computedFamilyCoarseInputWork source target N input ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedWidthEnvelope_weighted_near_linear 0 epsilon hepsilon,
    eventually_ge_atTop 1, inputSmallLog_tendsto.eventually (eventually_ge_atTop (2 ^ 1000)),
    computed_localOnlineMassBound_word] with N hw hN hell hB
  intro source target hsize input
  exact (computedFamilyCoarseInputWork_le source target N (by omega) hell hsize hB input).trans (by simpa only [pow_zero, mul_one] using hw)

theorem computedExecutionCoarseInputWork_integrable (source target : List ℕ) (N : ℕ) :
    Integrable (computedExecutionCoarseInputWork source target N) (computedExecutionLaw source target N) :=
  computedExecutionAcceptedWork_integrable source target N (computedFamilyCoarseInputWork source target N)

theorem computedExecutionCoarseInputWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∫ execution, computedExecutionCoarseInputWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyCoarseInputWork_near_linear epsilon hepsilon] with N hN
  intro source target hsize
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionCoarseInputWork_integrable source target N) (integrable_const _)
        (fun execution => hN source target hsize _)
    _ = _ := by simp

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

 theorem inputLength_register_word (N : ℕ) : Nat.size (N + 2) ≤ inputHeight N + 1 :=
  input_length_bits_le N

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalCoarsePreparation
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.chargedPhysicalCodeWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalFamilyCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalTableCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalBoundedWithWork_value _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.querySupportedChildWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation



theorem physicalCoarsePreparationCost_bound {M J : ℕ} (source target : List ℕ) (H : ℕ)
    (hH : 100 ≤ H) (hs : Nat.size source.length ≤ H ^ 3) (ht : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3)
    (entry : PhysicalEntry M J target.length) :
    physicalCoarsePreparationCost source target entry ≤ H ^ 6 * ((physicalSource source entry.1).length + 1) := by
  unfold physicalCoarsePreparationCost
  rw [physicalSource_length_eq]
  exact coarsePreparedSlicesWithWork_height_bound source target
    (physicalSourceInterval source.length entry.1).lo (physicalSourceInterval source.length entry.1).hi
    entry.2.lo entry.2.hi H (physicalSourceInterval source.length entry.1).ordered
    (physicalSourceInterval source.length entry.1).valid entry.2.ordered entry.2.valid hH hs ht hsymbol

section Coarse
variable {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List ℕ) (N P H T S passes copies : ℕ)
  (factor : ℕ → ℚ) (multiplier : ℕ → ℕ) (tau eta kappa delta : ℚ)
  (initial : PhysicalEntry M J target.length → ℕ)
  (draw : PhysicalFamilyScalarDraw (M := M) (J := J) (R := R)
    target N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80) passes copies)

local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) copies T S
local notation "readGroup" => physicalFamilyGroupRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "readInteger" => physicalFamilyOnlineRead (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes copies
local notation "answer" => physicalFamilyAnswer target N P ell exponent H (ell ^ 80) passes copies draw



theorem physicalFamilyCoarsePreparationWork_bound (bits : ℕ) (encode : Sum Key Table → ℕ)
    (root : Table) (hH : 100 ≤ H) (hs : Nat.size source.length ≤ H ^ 3)
    (ht : Nat.size target.length ≤ H ^ 3)
    (hsymbol : ∀ a ∈ source ++ target, Nat.size a ≤ H ^ 3) :
    physicalFamilyCoarsePreparationWork source target N P H T S passes copies factor multiplier
      tau eta kappa delta initial draw bits encode root ≤
      (H : ℝ) ^ 6 * physicalFamilyCoarseInputWork source target N P H T S passes copies factor multiplier
        tau eta kappa delta initial draw bits encode root := by
  classical
  unfold physicalFamilyCoarsePreparationWork physicalFamilyCoarseInputWork
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro entry _
  have hc : (physicalCoarsePreparationCost source target entry : ℝ) ≤
      (H : ℝ) ^ 6 * ((physicalSource source entry.1).length + 1 : ℕ) := by
    exact_mod_cast physicalCoarsePreparationCost_bound source target H hH hs ht hsymbol entry
  have hp := mul_le_mul_of_nonneg_left hc
    (show 0 ≤ selectionIndicator (Sum.inr (Sum.inl entry) ∈
      (chargedRandomMemoEvaluate source target N P ell exponent H (ell ^ 80) T S (passes + 1)
        copies factor multiplier tau eta kappa delta readGroup readInteger initial answer bits encode root).freshKeys) by
      unfold selectionIndicator; split <;> norm_num)
  exact hp.trans_eq (by ring)

end Coarse
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

theorem computedExecutionCoarsePreparationWork_bound :
    ∀ᶠ N : ℕ in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ execution : ComputedExecutionOutcome source target N,
      computedExecutionCoarsePreparationWork source target N execution ≤
        (inputHeight N : ℝ) ^ 6 * computedExecutionCoarseInputWork source target N execution := by
  filter_upwards [eventually_ge_atTop 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 200)] with N hN hell
  intro source target hsize hsymbol execution
  have hH : 100 ≤ inputHeight N := (by decide : 100 ≤ 256).trans
    (computed_coarse_height_large N (by omega) hell)
  have hl : Nat.size N ≤ inputHeight N + 1 :=
    (Nat.size_le_size (Nat.le_add_right N 2)).trans (inputLength_register_word N)
  have hp : inputHeight N + 1 ≤ inputHeight N ^ 3 := by
    have h : inputHeight N ≤ inputHeight N ^ 2 := Nat.le_pow (by decide)
    have hh := Nat.mul_le_mul_right (inputHeight N ^ 2) (show 2 ≤ inputHeight N by omega)
    nlinarith only [h, hh, hH]
  exact physicalFamilyCoarsePreparationWork_bound source target N (integerParameters N).P (inputHeight N)
    (integerParameters N).T (integerParameters N).S (computedSeedPassCount N) (inputHeight N ^ 2)
    (scheduledSeedFactor N) (scheduledSeedMultiplier N)
    (rationalParameters (inputSmallLog N)).tau (rationalParameters (inputSmallLog N)).eta
    (rationalParameters (inputSmallLog N)).kappa (rationalParameters (inputSmallLog N)).delta
    (clampedSeedNat (computedExecutionAccepted source target N execution).1)
    (computedExecutionAccepted source target N execution).2 (16384 * inputHeight N + 5)
    (computedFamilyMemoCode source target N (inputHeight N ^ 2)) (computedFinalRoot source target N)
    hH ((Nat.size_le_size (by omega : source.length ≤ N)).trans (hl.trans hp))
    ((Nat.size_le_size (by omega : target.length ≤ N)).trans (hl.trans hp)) hsymbol

theorem computedExecutionCoarsePreparationWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      (∫ execution, computedExecutionCoarsePreparationWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have he : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionCoarsePreparationWork_bound,
    computedExecutionCoarseInputWork_expected_near_linear (epsilon / 2) he,
    fixed_height_power_subpolynomial 6 (epsilon / 2) he] with N hb hi hp
  intro source target hsize hsymbol
  have hm := integral_mono (computedExecutionCoarsePreparationWork_integrable source target N)
    ((computedExecutionCoarseInputWork_integrable source target N).const_mul ((inputHeight N : ℝ) ^ 6))
    (hb source target hsize hsymbol)
  rw [integral_const_mul] at hm
  calc
    _ ≤ (inputHeight N : ℝ) ^ 6 * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      hm.trans (mul_le_mul_of_nonneg_left (hi source target hsize) (by positivity))
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hp (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedLocalKernelWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
open scoped Topology

 theorem computedLocalKernelExponent_tendsto (D : ℕ) :
    Tendsto (fun N => computedLocalKernelExponent D N / inputHeight N) atTop (𝓝 0) := by
  have h := ((local_enumeration_exponent_div_height_tendsto.const_mul (100 * Real.log 2)).add
    (encoding_exponent_div_height_tendsto.const_mul 100000)).const_mul (D : ℝ)
  simp only [mul_zero, zero_add] at h
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  ext N
  unfold computedLocalKernelExponent
  ring

private theorem localKernelBudget_exp_scalar (D H M p ell : ℕ) (hH : 0 < H)
    (hlog : Real.log (H : ℝ) ≤ (ell : ℝ) * Real.log 2) :
    ((H ^ localKernelPowerExponent M p D : ℕ) : ℝ) ≤
      Real.exp ((D : ℝ) * ((100 * Real.log 2) * (M : ℝ) * ((p : ℝ) + 1) * ell +
        100000 * ((p : ℝ) + 1) * Real.log (H : ℝ))) := by
  rw [Nat.cast_pow, nat_pow_eq_exp_log H _ hH]
  apply Real.exp_le_exp.mpr
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  have hp : (0 : ℝ) ≤ (p : ℝ) + 1 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hlog
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 100) hM) hp)
  have hD : (0 : ℝ) ≤ (D : ℝ) := Nat.cast_nonneg _
  unfold localKernelPowerExponent
  push_cast
  nlinarith only [mul_nonneg hD (sub_nonneg.mpr hmul)]

 theorem computedLocalKernelBudget_exp_bound (D N : ℕ) (hN : 0 < N) :
    (computedLocalKernelBudget D N : ℝ) ≤ Real.exp (computedLocalKernelExponent D N) := by
  have hlog : Real.log (inputHeight N : ℝ) ≤ (inputSmallLog N : ℝ) * Real.log 2 := by
    rw [inputHeight_real_log]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast (inputSmallLog_bounds N hN).1)
      (Real.log_nonneg (by norm_num))
  exact localKernelBudget_exp_scalar D (inputHeight N) (integerParameters N).M
    (coarseExponent (inputSmallLog N)) (inputSmallLog N) (Nat.two_pow_pos _) hlog

 theorem computedLocalKernelBudget_subpolynomial (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, (computedLocalKernelBudget D N : ℝ) ≤ (N + 2 : ℝ) ^ epsilon := by
  filter_upwards [subexponential_height_to_input (computedLocalKernelExponent D)
    (computedLocalKernelExponent_tendsto D) epsilon hepsilon, eventually_ge_atTop 1] with N he hN
  exact (computedLocalKernelBudget_exp_bound D N (by omega)).trans he

 theorem computedLocalKernelBudget_requests_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ input : ComputedFamilyInput source target N,
      ((computedFamilyResult source target N input).requests : ℝ) * computedLocalKernelBudget D N ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedFamilyResult_requests_near_linear (epsilon / 2) hh,
    computedLocalKernelBudget_subpolynomial D (epsilon / 2) hh] with N hr hk
  intro source target hsize input
  calc
    _ ≤ (N + 2 : ℝ) ^ (1 + epsilon / 2) * (N + 2 : ℝ) ^ (epsilon / 2) :=
      mul_le_mul (hr source target hsize input) hk (Nat.cast_nonneg _) (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

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

theorem computedFamilyKernelWork_near_linear (D : ℕ) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ (input : ComputedFamilyInput source target N)
      (cost : ComputedFamilyMemoKey source target N → ℕ),
      (∀ key, cost key ≤ computedLocalKernelBudget D N) →
      (computedFamilyKernelWork source target N input cost : ℝ) ≤
        (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedLocalKernelBudget_requests_near_linear D epsilon hepsilon] with N hN
  intro source target hsize input cost hcost
  have h := computedFamilyKernelWork_le source target N input cost
    (computedLocalKernelBudget D N) hcost
  have hr : (computedFamilyKernelWork source target N input cost : ℝ) ≤
      (computedLocalKernelBudget D N : ℝ) * (computedFamilyResult source target N input).requests := by
    exact_mod_cast h
  exact hr.trans (by simpa only [mul_comm] using hN source target hsize input)

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

theorem computedExecutionReadChargedWork_expected_near_linear (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      (∫ execution, computedExecutionReadChargedWork source target N execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh : 0 < epsilon / 2 := half_pos hepsilon
  filter_upwards [computedExecutionIndexedCoarseWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionCoarseSamplingWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionNonlocalWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionCoarsePreparationWork_expected_near_linear (epsilon / 2) hh,
    constant_le_rpow_eventually 4 (epsilon / 2) hh] with N hc hs hn hp hfour
  intro source target hsize hsymbol
  have hiC := computedExecutionIndexedCoarseWork_integrable source target N
  have hiS := computedExecutionCoarseSamplingWork_integrable source target N
  have hiN := computedExecutionNonlocalWork_integrable source target N
  have hiP := computedExecutionCoarsePreparationWork_integrable source target N
  change integral (computedExecutionLaw source target N)
    (((computedExecutionIndexedCoarseWork source target N + computedExecutionCoarseSamplingWork source target N) +
      computedExecutionNonlocalWork source target N) + computedExecutionCoarsePreparationWork source target N) ≤ _
  rw [integral_add' ((hiC.add hiS).add hiN) hiP, integral_add' (hiC.add hiS) hiN, integral_add' hiC hiS]
  calc
    _ ≤ 4 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hc source target hsize hsymbol, hs source target hsize, hn source target hsize, hp source target hsize hsymbol]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right hfour (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedExecutionKernelWork
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value
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

theorem computedExecutionKernelWork_expected_near_linear (D : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      ∀ cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ,
      (∀ input key, cost input key ≤ computedLocalKernelBudget D N) →
      (∫ execution, computedExecutionKernelWork source target N cost execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  filter_upwards [computedFamilyKernelWork_near_linear D epsilon hepsilon] with N hN
  intro source target hsize cost hcost
  calc
    _ ≤ ∫ _ : ComputedExecutionOutcome source target N, (N + 2 : ℝ) ^ (1 + epsilon)
        ∂computedExecutionLaw source target N :=
      integral_mono (computedExecutionKernelWork_integrable source target N cost)
        (integrable_const _) (fun execution => hN source target hsize
          (computedExecutionAccepted source target N execution) _ (hcost _))
    _ = _ := by simp

theorem computedExecutionTotalWork_expected_near_linear_oai (D : ℕ)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∀ᶠ N in atTop, ∀ source target : List ℕ, source.length + target.length ≤ N →
      (∀ a ∈ source ++ target, Nat.size a ≤ inputHeight N ^ 3) →
      ∀ cost : ComputedFamilyInput source target N → ComputedFamilyMemoKey source target N → ℕ,
      (∀ input key, cost input key ≤ computedLocalKernelBudget D N) →
      (∫ execution, computedExecutionTotalWork source target N cost execution
        ∂computedExecutionLaw source target N) ≤ (N + 2 : ℝ) ^ (1 + epsilon) := by
  have hh := half_pos hepsilon
  filter_upwards [computedExecutionReadChargedWork_expected_near_linear (epsilon / 2) hh,
    computedExecutionKernelWork_expected_near_linear D (epsilon / 2) hh,
    constant_le_rpow_eventually 2 (epsilon / 2) hh] with N hn hk htwo
  intro source target hsize hsymbol cost hcost
  change integral (computedExecutionLaw source target N)
    (computedExecutionReadChargedWork source target N + computedExecutionKernelWork source target N cost) ≤ _
  rw [integral_add' (computedExecutionReadChargedWork_integrable source target N)
    (computedExecutionKernelWork_integrable source target N cost)]
  calc
    _ ≤ 2 * (N + 2 : ℝ) ^ (1 + epsilon / 2) := by
      linarith only [hn source target hsize hsymbol, hk source target hsize cost hcost]
    _ ≤ (N + 2 : ℝ) ^ (epsilon / 2) * (N + 2 : ℝ) ^ (1 + epsilon / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg (by positivity) _)
    _ = _ := by rw [← Real.rpow_add (by positivity)]; congr 1; ring

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear_oai := @OAI.EditApproximation.computedExecutionTotalWork_expected_near_linear_oai
