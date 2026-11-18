-- Prove2me | solution 1 for OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:38:34.39423+00:00
-- url     : https://prove2.me/submissions/66be4d3d-8ee4-4f89-ba28-e2c5c7ab668c

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
import Definitions.Def_EditApproxScheme_12
import Definitions.Def_EditApproxScheme_13
import Definitions.Def_EditApproxScheme_14
import Definitions.Def_EditApproxScheme_15
import Definitions.Def_EditApproxScheme_16
import Definitions.Def_OAIQ361V3Ea004
import Theorems.Thm_OAI_EditApproximation_computedQueryAnswerWithWork_value
import Theorems.Thm_OAI_EditApproximation_local_physical_conditional_accuracy
import Theorems.Thm_OAI_EditApproximation_physicalFamilyRuntimeAnswer_event

section
-- module Solutions.OAIQ361V3_EA.EditDistance_Metric
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Unrestricted edit scripts, metric inequalities, and common subsequences
-/

namespace EditDistortion

universe u v

variable {Alpha : Type u} {Beta : Type v} {s : Bool}

namespace Step

theorem map (f : Alpha → Beta) {x y : List Alpha} (h : Step s x y) :
    Step s (x.map f) (y.map f) := by
  cases h with
  | insert p q a => simpa using Step.insert (substitutions := s) (p.map f) (q.map f) (f a)
  | delete p q a => simpa using Step.delete (substitutions := s) (p.map f) (q.map f) (f a)
  | substitute hs p q a b =>
    simpa using Step.substitute hs (p.map f) (q.map f) (f a) (f b)

end Step

namespace Script

theorem map (f : Alpha → Beta) {n : ℕ} {x y : List Alpha} (h : Script s n x y) :
    Script s n (x.map f) (y.map f) := by
  induction h with
  | nil x => exact .nil _
  | cons e h ih => exact .cons (e.map f) ih

end Script



theorem cost_map_le (f : Alpha → Beta) (x y : List Alpha) :
    cost s (x.map f) (y.map f) ≤ cost s x y :=
  cost_le ((cost_spec x y).map f)

end EditDistortion

namespace EditDistortion

universe u v
variable {Alpha : Type u} {Beta : Type v} {s : Bool}

theorem cost_map_eq_of_leftInverse (f : Alpha → Beta) (g : Beta → Alpha)
    (h : Function.LeftInverse g f) (x y : List Alpha) :
    cost s (x.map f) (y.map f) = cost s x y := by
  apply Nat.le_antisymm (cost_map_le f x y)
  have H := cost_map_le (s := s) g (x.map f) (y.map f)
  simpa only [List.map_map, h.comp_eq_id, List.map_id] using H

end EditDistortion

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



theorem integerSymbolCode_eq (z : ℤ) : integerSymbolCode z = Equiv.intEquivNat z := by
  cases z <;> rfl

theorem integerSymbolCode_bound (z : ℤ) : integerSymbolCode z ≤ 2 * z.natAbs := by
  cases z <;> simp only [integerSymbolCode, Int.natAbs] <;> omega

theorem integerSymbols_edit (source target : List ℤ) :
    EditDistortion.edit (source.map integerSymbolCode) (target.map integerSymbolCode) =
      EditDistortion.edit source target := by
  apply EditDistortion.cost_map_eq_of_leftInverse integerSymbolCode Equiv.intEquivNat.symm
  intro z
  rw [integerSymbolCode_eq]
  exact Equiv.intEquivNat.symm_apply_apply z

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_TreeAccounting
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Finite comparison-tree accounting

A complete tree is indexed by its physical depth and child labels. Terminal
comparison costs may be carried forward, with zero costs in the other child
slots. The identities apply to that representation without any probability
or sampling hypothesis.
-/

namespace EditApproximation

open Finset

/-- The explicit small-growth bound used for the comparison frontiers. -/
theorem small_growth_pow {x : ℝ} (n : ℕ) (hx : 0 ≤ x)
    (hsmall : (n : ℝ) * x ≤ 1 / 2) :
    (1 + x) ^ n ≤ 1 + 2 * n * x := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hn : (n : ℝ) * x ≤ 1 / 2 := by
      push_cast at hsmall
      nlinarith
    have hprev := mul_le_mul_of_nonneg_right (ih hn) (by positivity : 0 ≤ 1 + x)
    rw [pow_succ]
    apply hprev.trans
    push_cast
    have hprod : 0 ≤ x * (1 - 2 * n * x) := by
      apply mul_nonneg hx
      nlinarith
    nlinarith

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ParameterSlack
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Explicit slack at the large-input cutoff

The cutoff is handled symbolically: no expression with an astronomically
large exponent is expanded. The small-growth estimate supplies the
induction step. This proves the generous polynomial-versus-binary bound
used throughout the manuscript's numerical estimates.
-/

namespace EditApproximation

theorem polynomial_binary_growth_step (degree m : ℕ)
    (hsize : 4 * degree ≤ 2 * m + 1) :
    (2 * (m : ℝ) + 3) ^ degree ≤ 2 * (2 * (m : ℝ) + 1) ^ degree := by
  let d : ℝ := 2 * m + 1
  have hd : 0 < d := by dsimp [d] <;> positivity
  have hsizeR : 4 * (degree : ℝ) ≤ d := by
    dsimp only [d]
    exact_mod_cast hsize
  have hsmall : (degree : ℝ) * (2 / d) ≤ 1 / 2 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  have hbound : (1 + 2 / d) ^ degree ≤ 2 :=
    (small_growth_pow degree (by positivity) hsmall).trans (by nlinarith)
  have hrew : 2 * (m : ℝ) + 3 = d * (1 + 2 / d) := by
    dsimp [d]
    field_simp
    ring
  rw [hrew, mul_pow]
  have hmul := mul_le_mul_of_nonneg_left hbound (pow_nonneg hd.le degree)
  simpa only [d, mul_comm] using hmul

theorem astronomical_polynomial_bound (ell : ℕ) (hell : 2 ^ 1000 ≤ ell) :
    (ell : ℝ) ^ 20000 ≤ (2 : ℝ) ^ (ell / 2) := by
  let m0 : ℕ := 2 ^ 999
  have hbaseSize : (2 * (m0 : ℝ) + 1) ≤ (2 : ℝ) ^ 1001 := by
    have hm0 : (m0 : ℝ) = (2 : ℝ) ^ 999 := by
      simp only [m0, Nat.cast_pow, Nat.cast_ofNat]
    have hone : (1 : ℝ) ≤ m0 := by rw [hm0]; exact one_le_pow₀ (by norm_num)
    have hbig : (2 : ℝ) ^ 1001 = 4 * (m0 : ℝ) := by
      rw [show 1001 = 999 + 2 by decide, pow_add, ← hm0]
      norm_num only [pow_two]
      ring
    rw [hbig]
    calc
      2 * (m0 : ℝ) + 1 ≤ 2 * (m0 : ℝ) + m0 := add_le_add le_rfl hone
      _ = 3 * (m0 : ℝ) := by ring
      _ ≤ 4 * (m0 : ℝ) := mul_le_mul_of_nonneg_right (by norm_num)
        ((by norm_num : (0 : ℝ) ≤ 1).trans hone)
  have hbasePower := pow_le_pow_left₀ (by positivity : 0 ≤ 2 * (m0 : ℝ) + 1)
    hbaseSize 20000
  rw [← pow_mul] at hbasePower
  have hexponent : 1001 * 20000 ≤ m0 := by
    have hsmall : 1001 * 20000 ≤ (2 : ℕ) ^ 25 := by norm_num
    exact hsmall.trans (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by decide : 25 ≤ 999))
  have hbase : (2 * (m0 : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m0 :=
    hbasePower.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent)
  have hgrowth : ∀ m : ℕ, m0 ≤ m → (2 * (m : ℝ) + 1) ^ 20000 ≤ (2 : ℝ) ^ m := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact hbase
    | succ m hm ih =>
      have hsize0 : 4 * 20000 ≤ 2 * m0 + 1 := by omega
      have hstep := polynomial_binary_growth_step 20000 m (by omega)
      calc
        (2 * ((m + 1 : ℕ) : ℝ) + 1) ^ 20000 = (2 * (m : ℝ) + 3) ^ 20000 := by
          congr 1
          push_cast
          ring
        _ ≤ 2 * (2 * (m : ℝ) + 1) ^ 20000 := hstep
        _ ≤ 2 * (2 : ℝ) ^ m := mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (2 : ℝ) ^ (m + 1) := by rw [pow_succ]; ring
  have hcutoff : 2 ^ 1000 = 2 * m0 := by
    dsimp only [m0]
    rw [show 1000 = 999 + 1 by decide, pow_succ]
    exact Nat.mul_comm _ _
  have hm : m0 ≤ ell / 2 := by omega
  have hellR : (ell : ℝ) ≤ 2 * ((ell / 2 : ℕ) : ℝ) + 1 := by
    exact_mod_cast (show ell ≤ 2 * (ell / 2) + 1 by omega)
  exact (pow_le_pow_left₀ (Nat.cast_nonneg ell) hellR 20000).trans (hgrowth _ hm)

theorem astronomical_parameter_slack (ell : ℕ) (H : ℝ)
    (hell : 2 ^ 1000 ≤ ell) (hH : (2 : ℝ) ^ (ell / 2) ≤ H) :
    (ell : ℝ) ^ 20000 ≤ H :=
  (astronomical_polynomial_bound ell hell).trans hH

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
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

theorem inputHeight_binary_slack (N : ℕ) (hN : 0 < N) :
    (2 : ℝ) ^ (inputSmallLog N / 2) ≤ inputHeight N := by
  have hlogs := inputSmallLog_bounds N hN
  have hexponent : inputSmallLog N / 2 ≤ heightExponent N := by omega
  have hpower := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexponent
  simpa only [inputHeight, Nat.cast_pow, Nat.cast_ofNat] using hpower

theorem inputHeight_polynomial_slack (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) :
    (inputSmallLog N : ℝ) ^ 20000 ≤ inputHeight N :=
  astronomical_parameter_slack _ _ hell (inputHeight_binary_slack N hN)

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



theorem intervalTreeDepth_power_le (M nx : ℕ) (hM : 2 ≤ M) :
    M ^ intervalTreeDepth M nx ≤ M * max 1 nx := by
  by_cases hx : max 1 nx = 1
  · have hz : Nat.clog M 1 = 0 := by
      apply Nat.eq_zero_of_le_zero
      exact (Nat.clog_le_iff_le_pow hM).2 (by first | (simp; done) | exact WithTop.coe_le_coe.2 le_top | exact_mod_cast le_top)
    simpa only [intervalTreeDepth, hx, hz, pow_zero, mul_one] using
      (by omega : 1 ≤ M)
  · have hx1 : 1 < max 1 nx := by omega
    have hdepth := Nat.clog_pos hM hx1
    have hpred := Nat.pow_pred_clog_lt_self hM hx1
    unfold intervalTreeDepth
    rw [← Nat.succ_pred_eq_of_pos hdepth,
      pow_succ]
    nlinarith

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_BandGroupSampling
attribute [-instance] _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-!
# Executable shared group estimates

All dyadic powers in the prescribed closed range are enumerated, including
negative exponents. A scale is evaluated exactly when its sample count
reaches the child count; otherwise one shared array of uniform labels is
used for every member of the group. The selected member is the first
minimizer in the fixed list order.
-/

namespace EditApproximation

open Finset MeasureTheory ProbabilityTheory



theorem groupDyadicScales_length (M b : ℕ) (F : ℚ) :
    (groupDyadicScales M b F).length =
      (Int.log 2 (64 * F * b) - Int.clog 2 ((b : ℚ) / M) + 1).toNat := by
  simp only [groupDyadicScales, List.length_map, integerClosedRange, List.length_range]

theorem groupDyadicScales_length_dyadic (eM eb eF : ℕ) :
    (groupDyadicScales (2 ^ eM) (2 ^ eb) ((2 : ℚ) ^ eF)).length = 7 + eM + eF := by
  have hlower : ((2 ^ eb : ℕ) : ℚ) / (2 ^ eM : ℕ) = (2 : ℚ) ^ ((eb : ℤ) - eM) := by
    rw [Nat.cast_pow, Nat.cast_pow, Nat.cast_ofNat, zpow_sub₀ (by norm_num : (2 : ℚ) ≠ 0),
      zpow_natCast, zpow_natCast]
  have hupper : (64 : ℚ) * (2 : ℚ) ^ eF * (2 ^ eb : ℕ) =
      (2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, zpow_natCast, pow_add, pow_add]
    norm_num
  have hlog : Int.log 2 ((2 : ℚ) ^ ((6 + eF + eb : ℕ) : ℤ)) = ((6 + eF + eb : ℕ) : ℤ) := by
    simpa only [Nat.cast_ofNat] using Int.log_zpow (R := ℚ) (by decide : 1 < 2) ((6 + eF + eb : ℕ) : ℤ)
  have hclog : Int.clog 2 ((2 : ℚ) ^ ((eb : ℤ) - eM)) = (eb : ℤ) - eM := by
    simpa only [Nat.cast_ofNat] using Int.clog_zpow (R := ℚ) (by decide : 1 < 2) ((eb : ℤ) - eM)
  rw [groupDyadicScales_length, hlower, hupper, hlog, hclog]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SeedFactorSchedule
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! The literal dyadic factor schedule stops at A<=F. Each active pass
replaces A by 4A/F and uses the integer factor a=A/F. -/

namespace EditApproximation




theorem dyadicSeedPassCount_le_initial (f initial : ℕ) (hf : 3 ≤ f) :
    dyadicSeedPassCount f initial ≤ initial := by
  apply (ceilDiv_le_iff_le_mul (by omega : 0 < f - 2)).2
  exact (Nat.sub_le initial f).trans (Nat.le_mul_of_pos_left _ (by omega : 0 < f - 2))

theorem computedSeedPassCount_le_height (N : ℕ) (hN : 0 < N)
    (hell : 2 ^ 1000 ≤ inputSmallLog N) : computedSeedPassCount N ≤ inputHeight N := by
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hell
    omega
  have hlogs := (inputSmallLog_bounds N hN).1
  have hp : coarseExponent (inputSmallLog N) ≤ inputSmallLog N :=
    (Nat.sqrt_le_self _).trans ((Nat.sqrt_le_self _).trans (Nat.log_le_self _ _))
  have hell4 : 4 ≤ inputSmallLog N :=
    (by decide : 4 ≤ (2 : ℕ) ^ 3).trans
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hf)
  have hmul := Nat.mul_le_mul (show coarseExponent (inputSmallLog N) + 4 ≤ 2 * inputSmallLog N by omega) hlogs
  have hsmall : computedSeedInitialExponent N ≤ inputSmallLog N ^ 3 := by
    unfold computedSeedInitialExponent
    apply hmul.trans
    have h := Nat.mul_le_mul_right (inputSmallLog N ^ 2) (by omega : 2 ≤ inputSmallLog N)
    nlinarith only [h]
  have hpoly := inputHeight_polynomial_slack N hN hell
  have hellOne : (1 : ℝ) ≤ inputSmallLog N := by exact_mod_cast (show 1 ≤ inputSmallLog N from (by decide : 1 ≤ (4 : ℕ)).trans hell4)
  have hpower : (inputSmallLog N : ℝ) ^ 3 ≤ (inputSmallLog N : ℝ) ^ 20000 :=
    pow_le_pow_right₀ hellOne (by decide : 3 ≤ 20000)
  have hH : inputSmallLog N ^ 3 ≤ inputHeight N := by exact_mod_cast hpower.trans hpoly
  exact (dyadicSeedPassCount_le_initial _ _ hf).trans (hsmall.trans hH)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalInputEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width binary keys for gathered child states. The encoding uses
mixed radix arithmetic on the child label and the two state endpoints. -/

namespace EditApproximation

theorem childInputCode_bound {M n : ℕ} (input : Fin M × TargetInterval n) :
    childInputCode input < M * (n + 1) ^ 2 := by
  have hlow := input.2.ordered.trans input.2.valid
  have hhigh := input.2.valid
  have hlabel := input.1.isLt
  have hM : 0 < M := by omega
  have hinner : input.2.lo + (n + 1) * input.2.hi < (n + 1) ^ 2 := by
    nlinarith only [hlow, hhigh]
  unfold childInputCode
  nlinarith only [hlabel, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hinner)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalNodeEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Computable base-M node labels and mixed-radix table-entry keys.
Equal source intervals at different physical nodes keep distinct keys. -/

namespace EditApproximation



theorem treeLayerCode_bound (M d : ℕ) (path : TreeLayer M d) :
    treeLayerCode M d path < M ^ d := by
  induction d with
  | zero => exact Nat.zero_lt_one
  | succ d ih =>
    have hp := ih path.1
    have hi := path.2.isLt
    change path.2.val + M * treeLayerCode M d path.1 < M ^ (d + 1)
    rw [pow_succ]
    nlinarith only [hi, Nat.mul_le_mul_left M (Nat.succ_le_of_lt hp)]

theorem treeLayerCode_injective (M d : ℕ) : Function.Injective (treeLayerCode M d) := by
  induction d with
  | zero => intro first second _; cases first; cases second; rfl
  | succ d ih =>
    rintro ⟨first, i⟩ ⟨second, j⟩ heq
    obtain ⟨hlabel, hpath⟩ := mixedRadix_injective i.isLt j.isLt heq
    exact Prod.ext (ih hpath) (Fin.ext hlabel)



theorem physicalNode_layer_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    treeLayerCode M node.1.val node.2 < M ^ J :=
  (treeLayerCode_bound M node.1.val node.2).trans_le
    (pow_le_pow_right₀ hM (Nat.le_of_lt_succ node.1.isLt))

theorem physicalNodeCode_injective {M J : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalNodeCode M J) := by
  rintro ⟨depth, path⟩ ⟨depth', path'⟩ heq
  obtain ⟨hp, hd⟩ := mixedRadix_injective
    (physicalNode_layer_bound hM ⟨depth, path⟩)
    (physicalNode_layer_bound hM ⟨depth', path'⟩) heq
  have hdepth : depth = depth' := Fin.ext hd
  subst depth'
  have hpath := treeLayerCode_injective M depth.val hp
  change path = path' at hpath
  subst path'
  rfl

theorem physicalNodeCode_bound {M J : ℕ} (hM : 1 ≤ M) (node : PhysicalNode M J) :
    physicalNodeCode node < M ^ J * (J + 1) := by
  have hpath := physicalNode_layer_bound hM node
  have hdepth := node.1.isLt
  unfold physicalNodeCode
  nlinarith only [hpath, Nat.mul_le_mul_left (M ^ J) (Nat.succ_le_of_lt hdepth)]



theorem physicalEntryCode_injective {M J n : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@physicalEntryCode M J n) := by
  rintro ⟨node, q⟩ ⟨node', q'⟩ heq
  obtain ⟨hq, hn⟩ := mixedRadix_injective
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q))
    (by simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), q')) heq
  have hstate := childInputCode_injective 1 n hq
  have hqeq : q = q' := congrArg (fun pair : Fin 1 × TargetInterval n => pair.2) hstate
  exact Prod.ext (physicalNodeCode_injective hM hn) hqeq

theorem physicalEntryCode_bound {M J n : ℕ} (hM : 1 ≤ M) (state : PhysicalEntry M J n) :
    physicalEntryCode state < (n + 1) ^ 2 * (M ^ J * (J + 1)) := by
  have hstate : childInputCode ((0 : Fin 1), state.2) < (n + 1) ^ 2 := by
    simpa only [Nat.one_mul] using childInputCode_bound ((0 : Fin 1), state.2)
  have hnode := physicalNodeCode_bound hM state.1
  unfold physicalEntryCode
  nlinarith only [hstate, Nat.mul_le_mul_left ((n + 1) ^ 2) (Nat.succ_le_of_lt hnode)]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestEncoding
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Fixed-width keys for the bounded physical cache. Their construction
uses only the request's coordinates, without enumerating table entries. -/

namespace EditApproximation
namespace PhysicalTableRequest





theorem code_injective {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ) :
    Function.Injective (fun request : {r : PhysicalTableRequest M J n // Bounded passes copies T S r} =>
      code copies T S request.val) := by
  intro first second heq
  obtain ⟨hindex, hrest⟩ := mixedRadix_injective
    (Nat.lt_succ_of_le first.2.2.2) (Nat.lt_succ_of_le second.2.2.2) heq
  obtain ⟨hcopy, hrest⟩ := mixedRadix_injective first.2.2.1 second.2.2.1 hrest
  obtain ⟨hentry, hpass⟩ := mixedRadix_injective
    (physicalEntryCode_bound hM (first.1.node, first.1.state))
    (physicalEntryCode_bound hM (second.1.node, second.1.state)) hrest
  have he := physicalEntryCode_injective hM hentry
  have hnode := congrArg Prod.fst he
  have hstate := congrArg Prod.snd he
  apply Subtype.ext
  cases first with
  | mk first hf =>
    cases second with
    | mk second hs =>
      cases first
      cases second
      simp only at hpass hcopy hnode hindex hstate
      cases hpass
      cases hcopy
      cases hnode
      cases hindex
      cases hstate
      rfl

theorem code_bound {M J n : ℕ} (hM : 1 ≤ M) (passes copies T S : ℕ)
    (request : PhysicalTableRequest M J n) (hrequest : Bounded passes copies T S request) :
    code copies T S request < capacity M J n passes copies T S := by
  have he := physicalEntryCode_bound hM (request.node, request.state)
  change physicalEntryCode (request.node, request.state) < entryCapacity M J n at he
  have hinner : physicalEntryCode (request.node, request.state) +
      entryCapacity M J n * request.pass < entryCapacity M J n * passes := by
    nlinarith only [he, Nat.mul_le_mul_left (entryCapacity M J n) (Nat.succ_le_of_lt hrequest.1)]
  have hmiddle : request.copy + copies *
      (physicalEntryCode (request.node, request.state) + entryCapacity M J n * request.pass) <
        copies * (entryCapacity M J n * passes) := by
    nlinarith only [hrequest.2.1, Nat.mul_le_mul_left copies (Nat.succ_le_of_lt hinner)]
  unfold code capacity
  nlinarith only [hrequest.2.2, Nat.mul_le_mul_left (T + S + 1) (Nat.succ_le_of_lt hmiddle)]

end PhysicalTableRequest
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedPhysicalRequest
attribute [-instance] _root_.OAI.EditApproximation.PhysicalTableRequest.decidableBounded _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalOnlineMass_nezero _root_.OAI.EditApproximation.physicalLocalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalLocalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalLocalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalProgramBandMass_nezero _root_.OAI.EditApproximation.physicalProgramCoordinateFintype _root_.OAI.EditApproximation.physicalProgramCoordinateLaw_probability _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSingleton _root_.OAI.EditApproximation.physicalProgramCoordinateMeasurableSpace _root_.OAI.EditApproximation.physicalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Coarse seed computations are explicit cache requests, alongside the
bounded warmup/refinement requests. Their rank is below every table request,
so first exposure of a same-node coarse entry is a genuine leaf of the lazy program. -/

namespace EditApproximation



namespace ChargedPhysicalRequest









 theorem code_injective {M J ny passes copies T S : ℕ} (hM : 1 ≤ M) :
    Function.Injective (@code M J ny passes copies T S) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hentry : physicalEntryCode left = physicalEntryCode right := by
        change 2 * physicalEntryCode left = 2 * physicalEntryCode right at heq
        omega
      exact congrArg Sum.inl (physicalEntryCode_injective hM hentry)
    | inr right =>
      change 2 * physicalEntryCode left = 2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * PhysicalTableRequest.code copies T S left.val + 1 = 2 * physicalEntryCode right at heq
      omega
    | inr right =>
      have htable : PhysicalTableRequest.code copies T S left.val =
          PhysicalTableRequest.code copies T S right.val := by
        change 2 * PhysicalTableRequest.code copies T S left.val + 1 =
          2 * PhysicalTableRequest.code copies T S right.val + 1 at heq
        omega
      exact congrArg Sum.inr (PhysicalTableRequest.code_injective hM passes copies T S htable)

 theorem code_bound {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < capacity M J ny passes copies T S := by
  cases request with
  | inl entry =>
    have h := physicalEntryCode_bound hM entry
    change physicalEntryCode entry < PhysicalTableRequest.entryCapacity M J ny at h
    simp only [code, capacity]
    omega
  | inr request =>
    have h := PhysicalTableRequest.code_bound hM passes copies T S request.val request.property
    simp only [code, capacity]
    omega

 theorem code_fits {M J ny passes copies T S : ℕ} (hM : 1 ≤ M)
    (request : ChargedPhysicalRequest M J ny passes copies T S) :
    code request < 2 ^ bits M J ny passes copies T S :=
  (code_bound hM request).trans_le
    ((Nat.le_succ _).trans (Nat.le_pow_clog (by decide : 1 < 2) _))

end ChargedPhysicalRequest

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedGroupNumerical
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Computed parameters discharge the group scale-count and H^-4 tail bounds. -/

namespace EditApproximation

theorem computed_group_scale_count (N eb : ℕ) (hN : 0 < N) (hell : 8 ≤ inputSmallLog N) :
    (groupDyadicScales (integerParameters N).M (2 ^ eb) (inputSmallLog N)).length ≤
      2 * inputSmallLog N := by
  have hlogs := (inputSmallLog_bounds N hN).1
  have hsmall : smallLogExponent N ≤ inputSmallLog N :=
    (smallLogExponent N).lt_two_pow_self.le
  have hdiv := Nat.div_le_div_right (c := 20) hlogs
  change (groupDyadicScales (2 ^ (heightExponent N / 20)) (2 ^ eb)
    ((2 ^ smallLogExponent N : ℕ) : ℚ)).length ≤ _
  rw [Nat.cast_pow, Nat.cast_ofNat, groupDyadicScales_length_dyadic]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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

theorem computed_history_budget_le_height_sq (N : ℕ) (hH : 4 ≤ inputHeight N) :
    (integerParameters N).T + (integerParameters N).S + 1 ≤ inputHeight N ^ 2 := by
  have hT : (integerParameters N).T ≤ 2 * inputHeight N := by
    change 2 ^ ((3 * heightExponent N + 3) / 4) ≤ 2 * 2 ^ heightExponent N
    calc
      _ ≤ 2 ^ (heightExponent N + 1) :=
        pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hS : (integerParameters N).S ≤ inputHeight N := Nat.div_le_self _ _
  nlinarith only [hT, hS, hH]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalRequestBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The cache key width is linear in the input height, once the actual
pass and copy bounds are substituted. The numerical capacity is only a
bound: no array of that capacity is allocated. -/

namespace EditApproximation

theorem computed_entryCapacity_bound (N nx ny : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N) :
    PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (5 * inputHeight N) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hM : M ≤ H := pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) (Nat.div_le_self _ _)
  have hMH : M ≤ 2 ^ H := hM.trans (Nat.lt_two_pow_self.le)
  have hnx' : max 1 nx ≤ 2 ^ H := max_le Nat.one_le_two_pow
    (hnx.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N)))
  have htree : M ^ J ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ M * max 1 nx := intervalTreeDepth_power_le M nx (computed_branching_bounds N hN hell).1
      _ ≤ 2 ^ H * 2 ^ H := Nat.mul_le_mul hMH hnx'
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hJ : J ≤ H := by
    have hj := computed_tree_depth_bound N nx hN hnx hell
    change J * inputSmallLog N ≤ 100 * H at hj
    nlinarith only [hj, hell]
  have hJ' : J + 1 ≤ 2 ^ H := (Nat.add_le_add_right hJ 1).trans (Nat.lt_two_pow_self)
  have hny' : ny + 1 ≤ 2 ^ H := (by omega : ny + 1 ≤ N + 2).trans (inputHeight_covers_length N)
  unfold PhysicalTableRequest.entryCapacity
  calc
    (ny + 1) ^ 2 * (M ^ J * (J + 1)) ≤ (2 ^ H) ^ 2 * (2 ^ (2 * H) * 2 ^ H) :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hny' 2) (Nat.mul_le_mul htree hJ')
    _ = 2 ^ (5 * H) := by rw [← pow_mul, ← pow_add, ← pow_add]; congr 1; omega

theorem computed_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    PhysicalTableRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 1 := by
  let H := inputHeight N
  have hH : 4 ≤ H := (by omega : 4 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hstride := (computed_history_budget_le_height_sq N hH).trans hHpow
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hcapacity : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 2 ^ (11 * H) := by
    unfold PhysicalTableRequest.capacity
    calc
      _ ≤ 2 ^ (2 * H) * (2 ^ (2 * H) * (2 ^ (5 * H) * 2 ^ (2 * H))) :=
        Nat.mul_le_mul hstride
          (Nat.mul_le_mul (hcopies.trans hHpow) (Nat.mul_le_mul hentry (hpasses.trans hHpow)))
      _ = _ := by rw [← pow_add, ← pow_add, ← pow_add]; congr 1; omega
  unfold PhysicalTableRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).2
  calc
    _ ≤ 2 ^ (11 * H) + 2 ^ (11 * H) := Nat.add_le_add hcapacity Nat.one_le_two_pow
    _ = _ := by
      change 2 ^ (11 * H) + 2 ^ (11 * H) = 2 ^ (11 * H + 1)
      rw [pow_succ]
      omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_ChargedRequestSpace
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.vector_map_get
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial retained-cache bound for every execution. The estimate
uses only fixed-width key insertion and computed parameter sizes, and
therefore does not depend on an approximation success event. -/

namespace EditApproximation

theorem computed_charged_request_bits_le (N nx ny passes copies : ℕ) (hN : 0 < N)
    (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hpasses : passes ≤ inputHeight N ^ 2) (hcopies : copies ≤ inputHeight N ^ 2) :
    ChargedPhysicalRequest.bits (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S ≤ 11 * inputHeight N + 3 := by
  let H := inputHeight N
  have hentry := computed_entryCapacity_bound N nx ny hN hell hnx hny
  have hbits := computed_request_bits_le N nx ny passes copies hN hell hnx hny hpasses hcopies
  have htable : PhysicalTableRequest.capacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny passes copies
      (integerParameters N).T (integerParameters N).S + 1 ≤ 2 ^ (11 * H + 1) := by
    exact (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).mp hbits
  have hentry' : PhysicalTableRequest.entryCapacity (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) ny ≤ 2 ^ (11 * H + 1) :=
    hentry.trans (pow_le_pow_right₀ (by decide : 1 ≤ (2 : ℕ)) (by omega))
  unfold ChargedPhysicalRequest.bits
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < (2 : ℕ))).2
  unfold ChargedPhysicalRequest.capacity
  have hp : 2 ^ (11 * H + 3) = 4 * 2 ^ (11 * H + 1) := by
    rw [show 11 * H + 3 = (11 * H + 1) + 2 by omega, pow_add]
    norm_num
    omega
  change 2 * (_ + _) + 1 ≤ 2 ^ (11 * H + 3)
  rw [hp]
  omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_SourceRankedEncoding
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! An explicit parity tag separates source coordinates and table keys.
The code is computed from coordinates without enumerating the key type. -/

namespace EditApproximation.SourceRanked

variable {σ κ : Type*}



 theorem keyCode_injective (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (hs : Function.Injective sourceCode) (ht : Function.Injective tableCode) :
    Function.Injective (keyCode sourceCode tableCode) := by
  intro left right h
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have heq : sourceCode left = sourceCode right := by
        change 2 * sourceCode left = 2 * sourceCode right at h
        omega
      exact congrArg Sum.inl (hs heq)
    | inr right =>
      change 2 * sourceCode left = 2 * tableCode right + 1 at h
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * tableCode left + 1 = 2 * sourceCode right at h
      omega
    | inr right =>
      have heq : tableCode left = tableCode right := by
        change 2 * tableCode left + 1 = 2 * tableCode right + 1 at h
        omega
      exact congrArg Sum.inr (ht heq)

end EditApproximation.SourceRanked

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

theorem largeAccuracyInput_real (N : ℕ) (epsilon : ℚ) (h : largeAccuracyInput N epsilon) :
    2 ^ 1000 ≤ inputSmallLog N ∧ 10 ≤ (inputSmallLog N : ℝ) * (epsilon : ℝ) :=
  ⟨h.1, by exact_mod_cast h.2⟩

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedWarmupReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.physicalLocalGroupArrayLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A polynomial earlier-edge bound for the complete charged warmup
query. It includes all preceding-pass copy reads and pass-zero coarse
reads used by its initial cones. -/

namespace EditApproximation

theorem computed_dyadicScales_length (N : ℕ) (hH : 2 ≤ inputHeight N) :
    (dyadicScales N).length ≤ inputHeight N ^ 2 := by
  have hlog : Nat.log 2 N ≤ inputHeight N := by
    apply (Nat.log_le_clog 2 N).trans
    apply (Nat.clog_mono_right 2 (Nat.le_add_right N 2)).trans
    exact Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) (Nat.clog 2 (N + 2))
  simp only [dyadicScales, List.length_map, List.length_range]
  nlinarith only [hlog, hH]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

/-! Scalar-source addresses are computed from physical coordinates by
integer pairing. No enumeration of the probability space is performed. -/

namespace EditApproximation

variable {M J N n exponent F Q R B : ℕ}



 theorem physicalScalarCode_injective (hM : 1 ≤ M) :
    Function.Injective (@physicalScalarCode M J N n exponent F Q R B) := by
  intro left right heq
  rcases left with ⟨left, li⟩
  rcases right with ⟨right, ri⟩
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hp : Nat.pair (physicalEntryCode (left.1.1.val, left.1.2.2))
          (Nat.pair left.1.2.1.val (Nat.pair left.2.val.val li.val)) =
          Nat.pair (physicalEntryCode (right.1.1.val, right.1.2.2))
          (Nat.pair right.1.2.1.val (Nat.pair right.2.val.val ri.val)) := by
        change 2 * _ = 2 * _ at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨he, hs⟩
      rcases Nat.pair_eq_pair.mp hs with ⟨hs, hr⟩
      rcases Nat.pair_eq_pair.mp hr with ⟨hr, ht⟩
      have he := physicalEntryCode_injective hM he
      have hn : left.1.1 = right.1.1 := Subtype.ext (congrArg Prod.fst he)
      have hq := congrArg Prod.snd he
      have hs : left.1.2.1 = right.1.2.1 := Fin.ext hs
      have hr : left.2 = right.2 := Subtype.ext (Fin.ext hr)
      have ht : li = ri := Fin.ext ht
      rcases left with ⟨⟨node, scale, q⟩, range⟩
      rcases right with ⟨⟨node', scale', q'⟩, range'⟩
      dsimp only at hn hq hs hr
      subst node'
      subst scale'
      subst q'
      subst range'
      cases ht
      rfl
    | inr right =>
      change 2 * _ = 2 * _ + 1 at heq
      omega
  | inr left =>
    cases right with
    | inl right =>
      change 2 * _ + 1 = 2 * _ at heq
      omega
    | inr right =>
      have hp : Nat.pair (physicalNodeCode left.1.val)
          (Nat.pair left.2.1.val (Nat.pair left.2.2.1.val (Nat.pair left.2.2.2.val
            (Nat.pair li.1.val (Nat.pair li.2.1.val li.2.2.val))))) =
          Nat.pair (physicalNodeCode right.1.val)
          (Nat.pair right.2.1.val (Nat.pair right.2.2.1.val (Nat.pair right.2.2.2.val
            (Nat.pair ri.1.val (Nat.pair ri.2.1.val ri.2.2.val))))) := by
        change 2 * _ + 1 = 2 * _ + 1 at heq
        omega
      rcases Nat.pair_eq_pair.mp hp with ⟨hn, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hs, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hx, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hy, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨ht, hp⟩
      rcases Nat.pair_eq_pair.mp hp with ⟨hl, hv⟩
      have hn : left.1 = right.1 := Subtype.ext (physicalNodeCode_injective hM hn)
      have hs : left.2.1 = right.2.1 := Fin.ext hs
      have hx : left.2.2.1 = right.2.2.1 := Fin.ext hx
      have hy : left.2.2.2 = right.2.2.2 := Fin.ext hy
      rcases left with ⟨node, scale, x, y⟩
      rcases right with ⟨node', scale', x', y'⟩
      dsimp only at hn hs hx hy
      subst node'
      subst scale'
      subst x'
      subst y'
      rcases li with ⟨time, label, value⟩
      rcases ri with ⟨time', label', value'⟩
      have ht : time = time' := Fin.ext ht
      cases ht
      have hl : label = label' := Fin.ext hl
      cases hl
      have hv : value = value' := Fin.ext hv
      cases hv
      rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalScalarCodeBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Concrete coordinate pairing has constant-factor bit overhead. The
addresses are computed from coordinates, without enumerating a key space. -/

namespace EditApproximation

 theorem natPair_lt_two_pow {a b k : ℕ} (ha : a < 2 ^ k) (hb : b < 2 ^ k) :
    Nat.pair a b < 2 ^ (2 * k) := by
  calc
    _ < (max a b + 1) ^ 2 := Nat.pair_lt_max_add_one_sq a b
    _ ≤ (2 ^ k) ^ 2 := Nat.pow_le_pow_left (by omega) 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

 theorem natPair_lt_two_pow_scaled {a b k d : ℕ} (ha : a < 2 ^ k)
    (hb : b < 2 ^ (d * k)) (hd : 1 ≤ d) : Nat.pair a b < 2 ^ ((2 * d) * k) := by
  have hk : k ≤ d * k := by simpa only [one_mul] using Nat.mul_le_mul_right k hd
  have h := natPair_lt_two_pow (ha.trans_le (Nat.pow_le_pow_right (by decide) hk)) hb
  simpa only [Nat.mul_assoc] using h

 theorem physicalScalarCode_bound {M J N n exponent F Q R B : ℕ} (k : ℕ)
    (hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ k)
    (hentry : ∀ entry : PhysicalEntry M J n, physicalEntryCode entry < 2 ^ k)
    (hscale : (dyadicScales N).length ≤ 2 ^ k)
    (hcell : n * 2 ^ exponent + 1 ≤ 2 ^ k)
    (hrange : B + 1 ≤ 2 ^ k) (htime : R ≤ 2 ^ k) (hM : M ≤ 2 ^ k)
    (hlabels : ∀ scale : Fin (dyadicScales N).length,
      (groupDyadicScales M ((dyadicScales N).get scale) F).length ≤ 2 ^ k)
    (key : PhysicalScalarKey M J N n exponent F Q R B) :
    physicalScalarCode key < 2 ^ (64 * k + 1) := by
  rcases key with ⟨key, index⟩
  cases key with
  | inl online =>
    have h0 := natPair_lt_two_pow (online.2.val.isLt.trans_le hrange) (index.isLt.trans_le htime)
    have h1 := natPair_lt_two_pow_scaled (online.1.2.1.isLt.trans_le hscale) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (hentry (online.1.1.val, online.1.2.2)) h1 (by decide : 1 ≤ 4)
    have h2' : Nat.pair (physicalEntryCode (online.1.1.val, online.1.2.2))
        (Nat.pair online.1.2.1.val (Nat.pair online.2.val.val index.val)) < 2 ^ (64 * k) :=
      h2.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    change 2 * _ < _
    rw [pow_succ]
    omega
  | inr group =>
    have h0 := natPair_lt_two_pow
      (index.2.1.isLt.trans_le (hlabels group.2.1))
      (index.2.2.isLt.trans_le ((min_le_left _ _).trans hM))
    have h1 := natPair_lt_two_pow_scaled (index.1.isLt.trans_le htime) h0 (by decide : 1 ≤ 2)
    have h2 := natPair_lt_two_pow_scaled (group.2.2.2.isLt.trans_le hcell) h1 (by decide : 1 ≤ 4)
    have h3 := natPair_lt_two_pow_scaled (group.2.2.1.isLt.trans_le hcell) h2 (by decide : 1 ≤ 8)
    have h4 := natPair_lt_two_pow_scaled (group.2.1.isLt.trans_le hscale) h3 (by decide : 1 ≤ 16)
    have h5 := natPair_lt_two_pow_scaled (hnode group.1.val) h4 (by decide : 1 ≤ 32)
    norm_num only at h5
    change 2 * _ + 1 < _
    rw [pow_succ]
    omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalFamilyEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

section Encoding

variable {α : Type*} {M J R : ℕ} (target : List α) (N P F exponent H Q passes copies : ℕ)

local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P F exponent H Q passes copies



 theorem physicalFamilyCode_injective (hM : 1 ≤ M) :
    Function.Injective (physicalFamilyCode (M := M) (J := J) (R := R)
      target N P F exponent H Q passes copies) := by
  intro first second h
  obtain ⟨hp, h⟩ := Nat.pair_eq_pair.mp h
  obtain ⟨hc, hs⟩ := Nat.pair_eq_pair.mp h
  exact Prod.ext (Fin.ext hp) (Prod.ext (Fin.ext hc) (physicalScalarCode_injective hM hs))

 theorem physicalFamilyCode_bound (k : ℕ)
    (hpass : passes + 1 ≤ 2 ^ k) (hcopy : copies + 1 ≤ 2 ^ k)
    (hscalar : ∀ key : PhysicalScalarKey M J N target.length exponent F Q R
        (localOnlineMassBound M P H), physicalScalarCode key < 2 ^ (64 * k + 1))
    (key : Key) : physicalFamilyCode target N P F exponent H Q passes copies key <
      2 ^ (256 * k + 4) := by
  have hk : k ≤ 64 * k + 1 := by omega
  have hp := key.1.isLt.trans_le (hpass.trans (Nat.pow_le_pow_right (by decide) hk))
  have hc := key.2.1.isLt.trans_le (hcopy.trans (Nat.pow_le_pow_right (by decide) hk))
  have hi := natPair_lt_two_pow hc (hscalar key.2.2)
  have ho := natPair_lt_two_pow_scaled hp hi (by decide : 1 ≤ 2)
  change Nat.pair _ (Nat.pair _ _) < _
  convert ho using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

end Encoding

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedScalarCodeBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledSeedLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalCoarseSeedLaw_probability _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalLocalProgramDrawLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_physicalScalarCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N ny (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P (inputHeight N))) :
    physicalScalarCode key < 2 ^ (64 * (64 * inputHeight N) + 1) := by
  let H := inputHeight N
  let M := (integerParameters N).M
  let J := intervalTreeDepth M nx
  have hMH : M ≤ H := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  have hMpos : 1 ≤ M := (by omega : 1 ≤ 2).trans (computed_branching_bounds N hN hell).1
  have hH : 64 ≤ H := (by omega : 64 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift (e : ℕ) (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hHpow : H ^ 2 ≤ 2 ^ (2 * H) := by
    calc
      _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
      _ = _ := by rw [← pow_mul]; congr 1; omega
  have hentry : ∀ entry : PhysicalEntry M J ny, physicalEntryCode entry < 2 ^ (64 * H) := by
    intro entry
    exact ((physicalEntryCode_bound hMpos entry).trans_le
      (computed_entryCapacity_bound N nx ny hN hell hnx hny)).trans_le (hlift (5 * H) (by omega))
  have hnode : ∀ node : PhysicalNode M J, physicalNodeCode node < 2 ^ (64 * H) := by
    intro node
    have hb : M ^ J * (J + 1) ≤ 2 ^ (5 * H) := by
      simpa only [PhysicalTableRequest.entryCapacity, zero_add, one_pow, one_mul] using
        computed_entryCapacity_bound N nx 0 hN hell hnx (Nat.zero_le N)
    exact ((physicalNodeCode_bound hMpos node).trans_le hb).trans_le (hlift (5 * H) (by omega))
  have hsmall : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ 2 ^ smallLogExponent N).trans
      (computed_smallLog_le_height N)
  have hcell : ny * 2 ^ (40 * smallLogExponent N) + 1 ≤ 2 ^ (64 * H) := by
    have hn : ny ≤ 2 ^ H := hny.trans ((Nat.le_add_right N 2).trans (inputHeight_covers_length N))
    have he : 2 ^ (40 * smallLogExponent N) ≤ 2 ^ (40 * H) :=
      Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 40 hsmall)
    calc
      _ ≤ 2 ^ H * 2 ^ (40 * H) + 1 := Nat.add_le_add_right (Nat.mul_le_mul hn he) 1
      _ = 2 ^ (41 * H) + 1 := by rw [← pow_add]; congr 2; omega
      _ ≤ 2 ^ (41 * H) + 2 ^ (41 * H) := Nat.add_le_add_left Nat.one_le_two_pow _
      _ = 2 ^ (41 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift _ (by omega)
  apply physicalScalarCode_bound (64 * H) hnode hentry
  · exact (computed_dyadicScales_length N (by omega)).trans (hHpow.trans (hlift _ (by omega)))
  · exact hcell
  · have hb := Nat.lt_size_self (localOnlineMassBound M (integerParameters N).P H)
    exact (Nat.succ_le_of_lt hb).trans
      ((Nat.pow_le_pow_right (by decide) hB).trans (hlift H (by omega)))
  · exact hR.trans (hHpow.trans (hlift _ (by omega)))
  · exact hMH.trans (Nat.lt_two_pow_self.le.trans (hlift H (by omega)))
  · intro scale
    have hs := List.get_mem (dyadicScales N) scale
    obtain ⟨eb, _, heq⟩ := List.mem_map.mp hs
    have hc : (groupDyadicScales M ((dyadicScales N).get scale) (inputSmallLog N)).length ≤
        2 * inputSmallLog N := by
      rw [← heq]
      exact computed_group_scale_count N eb hN (by omega)
    have htwo : 2 * inputSmallLog N ≤ 2 ^ (H + 1) := by
      have hp := Nat.mul_le_mul_left 2 ((computed_smallLog_le_height N).trans Nat.lt_two_pow_self.le)
      simpa only [pow_succ, Nat.mul_comm] using hp
    exact hc.trans (htwo.trans (hlift _ (by omega)))

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyEncoding
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

 theorem computed_physicalFamilyCode_bound (N nx ny R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hnx : nx ≤ N) (hny : ny ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (target : List ℕ) (htarget : target.length = ny)
    (key : PhysicalFamilyScalarKey (M := (integerParameters N).M)
      (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
      target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2)) :
    physicalFamilyCode target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
      (inputHeight N) (inputSmallLog N ^ 80) (computedSeedPassCount N) (inputHeight N ^ 2) key <
      2 ^ (16384 * inputHeight N + 4) := by
  let H := inputHeight N
  have hH : 2 ≤ H := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hlift {e : ℕ} (he : e ≤ 64 * H) : 2 ^ e ≤ 2 ^ (64 * H) :=
    Nat.pow_le_pow_right (by decide) he
  have hp : computedSeedPassCount N + 1 ≤ 2 ^ (64 * H) :=
    ((Nat.add_le_add_right (computedSeedPassCount_le_height N hN hell) 1).trans
      (Nat.lt_two_pow_self : H < 2 ^ H)).trans (hlift (by omega))
  have hc : H ^ 2 + 1 ≤ 2 ^ (64 * H) := by
    have hh : H ^ 2 ≤ 2 ^ (2 * H) := by
      calc
        _ ≤ (2 ^ H) ^ 2 := Nat.pow_le_pow_left Nat.lt_two_pow_self.le 2
        _ = _ := by rw [← pow_mul]; congr 1; omega
    calc
      _ ≤ 2 ^ (2 * H) + 2 ^ (2 * H) := Nat.add_le_add hh Nat.one_le_two_pow
      _ = 2 ^ (2 * H + 1) := by rw [pow_succ]; omega
      _ ≤ _ := hlift (by omega)
  have hscalar (scalar : PhysicalScalarKey (integerParameters N).M
      (intervalTreeDepth (integerParameters N).M nx) N target.length (40 * smallLogExponent N)
      (inputSmallLog N) (inputSmallLog N ^ 80) R
      (localOnlineMassBound (integerParameters N).M (integerParameters N).P H)) :
      physicalScalarCode scalar < 2 ^ (64 * (64 * H) + 1) :=
    computed_physicalScalarCode_bound N nx target.length R hN (by omega) hnx
      (by omega) hR hB scalar
  have h := physicalFamilyCode_bound (M := (integerParameters N).M)
    (J := intervalTreeDepth (integerParameters N).M nx) (R := R)
    target N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N) H
      (inputSmallLog N ^ 80) (computedSeedPassCount N) (H ^ 2) (64 * H) hp hc hscalar key
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  congr 1
  omega

 theorem mixedCode_lt_two_pow {σ κ : Type*} (sourceCode : σ → ℕ) (tableCode : κ → ℕ)
    (b : ℕ) (hs : ∀ source, sourceCode source < 2 ^ b)
    (ht : ∀ table, tableCode table < 2 ^ b) (key : Sum σ κ) :
    SourceRanked.keyCode sourceCode tableCode key < 2 ^ (b + 1) := by
  rw [pow_succ]
  cases key with
  | inl source => have h := hs source; change 2 * _ < _; omega
  | inr table => have h := ht table; change 2 * _ + 1 < _; omega

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedFamilyMemoCode
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyLaw_probability _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation







 theorem computedFamilyMemoCode_injective (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 200 ≤ inputSmallLog N) :
    Function.Injective (computedFamilyMemoCode source target N R) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN hell).1
  exact SourceRanked.keyCode_injective _ _
    (physicalFamilyCode_injective target N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (computedSeedPassCount N) (inputHeight N ^ 2) hM)
    (ChargedPhysicalRequest.code_injective hM)

 theorem computedFamilyMemoCode_fits (source target : List ℕ) (N R : ℕ)
    (hN : 0 < N) (hell : 2 ^ 1000 ≤ inputSmallLog N) (hsize : source.length + target.length ≤ N)
    (hR : R ≤ inputHeight N ^ 2)
    (hB : Nat.size (localOnlineMassBound (integerParameters N).M (integerParameters N).P
      (inputHeight N)) ≤ inputHeight N)
    (key : Sum (ComputedFamilyScalarKey source target N R) (ComputedFamilyTableKey source target N)) :
    computedFamilyMemoCode source target N R key < 2 ^ (16384 * inputHeight N + 5) := by
  have hM : 1 ≤ (integerParameters N).M := (by omega : 1 ≤ 2).trans
    (computed_branching_bounds N hN (by omega)).1
  have hH : 2 ≤ inputHeight N := (by omega : 2 ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have hpass : computedSeedPassCount N + 1 ≤ inputHeight N ^ 2 := by
    have h := computedSeedPassCount_le_height N hN hell
    nlinarith only [h, hH]
  apply mixedCode_lt_two_pow _ _ (16384 * inputHeight N + 4)
  · intro scalar
    exact computed_physicalFamilyCode_bound N source.length target.length R hN hell
      (by omega) (by omega) hR hB target rfl scalar
  · intro table
    have hb := computed_charged_request_bits_le N source.length target.length
      (computedSeedPassCount N + 1) (inputHeight N ^ 2) hN (by omega) (by omega) (by omega)
      hpass le_rfl
    exact (ChargedPhysicalRequest.code_fits hM table).trans_le
      (Nat.pow_le_pow_right (by decide) (hb.trans (by omega)))

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



theorem exactSuffixAnswer_eq_edit {α : Type*} [DecidableEq α] (source target : List α) :
    exactSuffixAnswer source target = edit source target := by
  simpa only [exactSuffixAnswer, List.drop_zero] using exactSuffixDP_spec source target 0 (Nat.zero_le _)

theorem exactSuffixAnswer_approximation {α : Type*} [DecidableEq α] (source target : List α)
    (epsilon : ℝ) (hepsilon : 0 ≤ epsilon) :
    edit source target ≤ exactSuffixAnswer source target ∧
      (exactSuffixAnswer source target : ℝ) ≤ (1 + epsilon) * edit source target := by
  rw [exactSuffixAnswer_eq_edit]
  constructor
  · exact le_rfl
  · nlinarith [show (0 : ℝ) ≤ (edit source target : ℝ) from Nat.cast_nonneg _]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_PhysicalUniformAccuracy
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.absolute_value _root_.OAI.EditApproximation.BinaryFraction.absolute_width _root_.OAI.EditApproximation.BinaryFraction.affineErrorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandFromActionsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandPredicateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bandToleranceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanActionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.bellmanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalAddWithWork_value _root_.OAI.EditApproximation.BinaryFraction.canonicalMulWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellCoordinatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellGridPointsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cellStatesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.centerEligibilityWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coefficientWithWork_value _root_.OAI.EditApproximation.BinaryFraction.connectionTermsWithWork_length _root_.OAI.EditApproximation.BinaryFraction.connectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.coordinateVectorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.cutGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.decrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.distanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.divWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointActionWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.endpointConnectionWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointDistanceWithWork_value _root_.OAI.EditApproximation.BinaryFraction.endpointScoreWithWork_value _root_.OAI.EditApproximation.BinaryFraction.equalWithWork_value _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.groupIndexWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupMemberWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupSampleCountWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScaleWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.groupTermsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.indexedGroupScales_value _root_.OAI.EditApproximation.BinaryFraction.initialCenterGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialConeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.initialScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localContinuationWithWork_value _root_.OAI.EditApproximation.BinaryFraction.localRepresentativesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.medianSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.nat_value _root_.OAI.EditApproximation.BinaryFraction.naturalFloorWithWork_value _root_.OAI.EditApproximation.BinaryFraction.ofNaturalWord_value _root_.OAI.EditApproximation.BinaryFraction.onlineIndexSetupWithWork_value _root_.OAI.EditApproximation.BinaryFraction.onlineMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.prefixMinimumWithWork_value _root_.OAI.EditApproximation.BinaryFraction.prefixWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedRepresentativeWithWork_value _root_.OAI.EditApproximation.BinaryFraction.preparedUnskippedCandidateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryExponentsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementScaleGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementUpdateWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedBandWithWork_value _root_.OAI.EditApproximation.BinaryFraction.roundedSpacingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledCeilingWithWork_value _root_.OAI.EditApproximation.BinaryFraction.scaledSeedWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.signedPowerTwoWithWork_value _root_.OAI.EditApproximation.BinaryFraction.stateGapWithWork_value _root_.OAI.EditApproximation.BinaryFraction.subWithWork_value _root_.OAI.EditApproximation.BinaryFraction.targetCellsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.unskippedGuardWithWork_value _root_.OAI.EditApproximation.BinaryFraction.vector_map_get _root_.OAI.EditApproximation.BinaryFraction.warmupAverageWithWork_value _root_.OAI.EditApproximation.BinaryFraction.wideActionsFromRepresentativesWithWork_decode _root_.OAI.EditApproximation.BinaryFraction.wideMinimumWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.actionEqualWithWork_value _root_.OAI.EditApproximation.actionMemberWithWork_value _root_.OAI.EditApproximation.chargedPhysicalCodeWithWork_value _root_.OAI.EditApproximation.coordinateEqualWithWork_value _root_.OAI.EditApproximation.dyadicScalesWithWork_value _root_.OAI.EditApproximation.gridStateBoxWithWork_value _root_.OAI.EditApproximation.makeStateWithWork_value _root_.OAI.EditApproximation.onlineMassWithWork_value _root_.OAI.EditApproximation.physicalEntryCodeWithWork_value _root_.OAI.EditApproximation.physicalFamilyCodeWithWork_value _root_.OAI.EditApproximation.physicalNodeCodeWithWork_value _root_.OAI.EditApproximation.physicalScalarCodeWithWork_value _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.queryScaleDispatchWithWork_value _root_.OAI.EditApproximation.queryScalePresentWithWork_value _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint _root_.OAI.EditApproximation.rationalParametersWithWork_value _root_.OAI.EditApproximation.roundStateWithWork_value _root_.OAI.EditApproximation.sourceChildWithWork_value _root_.OAI.EditApproximation.treeLayerCodeWithWork_value _root_.OAI.EditApproximation.wideActionGridWithWork_value _root_.OAI.EditApproximation.wideChildGridWithWork_value _root_.OAI.EditApproximation.zeroConnectionWithWork_value
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false


namespace OAI

namespace EditApproximation

open MeasureTheory ProbabilityTheory Filter

section Uniform

variable {α : Type} [DecidableEq α] {M J R : ℕ} [NeZero M] [NeZero R]
  (source target : List α) (N P T S H B : ℕ)
  [NeZero B] [MeasurableSpace (Fin B)] [MeasurableSingletonClass (Fin B)]
  (depth : PhysicalEntry M J target.length → ℕ)

local notation "passes" => computedSeedPassCount N
local notation "ell" => inputSmallLog N
local notation "exponent" => (40 * smallLogExponent N : ℕ)
local notation "Key" => PhysicalFamilyScalarKey (M := M) (J := J) (R := R)
  target N P ell exponent H (ell ^ 80) passes (H ^ 2)
local notation "Table" => ChargedPhysicalRequest M J target.length (passes + 1) (H ^ 2) T S

/-- Uniform correctness of the memo evaluator driven by rejection trials,
under finite Bernstein bounds for coarse and group coordinates. -/
theorem physical_uniform_conditional_accuracy (epsilon : BinaryFraction) (hH : 0 < H) (bits : ℕ)
    (encode : Sum Key Table → ℕ)
    (hcode : physicalLargeInput N epsilon → Function.Injective encode)
    (hfits : physicalLargeInput N epsilon → ∀ key, encode key < 2 ^ bits)
    (hsize : source.length + target.length ≤ N)
    (hMeq : M = (integerParameters N).M) (hJeq : J = intervalTreeDepth M source.length)
    (hPeq : P = (integerParameters N).P) (hTeq : T = (integerParameters N).T)
    (hSeq : S = (integerParameters N).S) (hHeq : H = inputHeight N)
    (hB : B = (integerParameters N).B)
    (hdepth : ∀ state, depth state = computedCoarseDepth N
      (coarseEntryWidth (physicalSource source state.1) (substring target state.2.lo state.2.hi)))
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin B =>
      (PMF.uniformOfFintype (Fin B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin (groupDyadicScales M b ell).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount M (ell ^ 80) b (groupDyadicScaleAt M b ell h)) =>
        (PMF.uniformOfFintype (Fin M)).toMeasure))
    (hepsilon : 0 < epsilon.value) :
    (2 / 3 : ℝ) ≤ (physicalUniformLaw (R := R) source target N P H B depth epsilon).real
      {outcome | EditDistortion.edit source target ≤
        physicalUniformAnswer source target N P T S H hH bits encode outcome ∧
        (physicalUniformAnswer source target N P T S H hH bits encode outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  classical
  by_cases hlarge : physicalLargeInput N epsilon
  · have hN := largeAccuracyInput_pos N epsilon.value hlarge.2.1
    have hreal := largeAccuracyInput_real N epsilon.value hlarge.2.1
    have hepsilonR : (0 : ℝ) < epsilon.value := by exact_mod_cast hepsilon
    have hPpos : 0 < P := by
      rw [hPeq]
      exact Nat.pow_pos (Nat.two_pow_pos _)
    rw [physicalUniformLaw, ite_eq_left hlarge,
      map_measureReal_apply (by fun_prop) (Set.to_countable _).measurableSet]
    change (2 / 3 : ℝ) ≤ (physicalFamilyRuntimeLaw (R := R) target N P H
      (physicalCoarseSeedLaw source target N B depth)).real
      {execution | EditDistortion.edit source target ≤
        physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
          (finalTargetState target.length) execution ∧
        (physicalFamilyRuntimeAnswer source target N P T S H hH bits encode
          (finalTargetState target.length) execution : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}
    have hevent := physicalFamilyRuntimeAnswer_event source target N P T S H hPpos hH bits encode
      (hcode hlarge) (hfits hlarge) (physicalCoarseSeedLaw source target N B depth)
      (finalTargetState target.length)
      {answer | EditDistortion.edit source target ≤ answer ∧
        (answer : ℝ) ≤ (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target}
    simp only [Set.mem_ofPred_eq] at hevent
    rw [hevent]
    exact local_physical_conditional_accuracy source target N P T S H B depth hN hreal.1
      hsize hMeq hJeq hPeq hTeq hSeq hHeq hB hdepth coarseBernstein groupBernstein
      (epsilon.value : ℝ) hepsilonR hreal.2
  · rw [physicalUniformLaw, ite_eq_right hlarge]
    have hgood : (Sum.inl () : PhysicalUniformOutcome (M := M) (J := J) (R := R) target N P H) ∈
        {outcome | EditDistortion.edit source target ≤
          physicalUniformAnswer source target N P T S H hH bits encode outcome ∧
          (physicalUniformAnswer source target N P T S H hH bits encode outcome : ℝ) ≤
            (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} :=
      exactSuffixAnswer_approximation source target epsilon.value (by exact_mod_cast hepsilon.le)
    rw [Measure.real, Measure.dirac_apply_of_mem hgood, ENNReal.toReal_one]
    norm_num

end Uniform

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPhysicalUniform
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
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

 theorem computed_physical_uniform_conditional_accuracy (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N)
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
      (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin
      (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
          (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)) :
    (2 / 3 : ℝ) ≤ (computedPhysicalLaw source target N epsilon).real
      {outcome | EditDistortion.edit source target ≤ computedPhysicalAnswer source target N outcome ∧
        (computedPhysicalAnswer source target N outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  apply physical_uniform_conditional_accuracy source target N (integerParameters N).P
    (integerParameters N).T (integerParameters N).S (inputHeight N) (integerParameters N).B
    (computedPhysicalCoarseDepth source target N) epsilon (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    ?_ ?_ hsize rfl rfl rfl rfl rfl rfl rfl (fun _ => rfl) coarseBernstein groupBernstein hepsilon
  · intro hlarge
    exact computedFamilyMemoCode_injective source target N (inputHeight N ^ 2)
      (largeAccuracyInput_pos N epsilon.value hlarge.2.1) (by
        have h := hlarge.2.1.1
        have hc := two_hundred_le_two_pow_thousand
        omega)
  · intro hlarge key
    exact computedFamilyMemoCode_fits source target N (inputHeight N ^ 2)
      (largeAccuracyInput_pos N epsilon.value hlarge.2.1) hlarge.2.1.1 hsize le_rfl hlarge.2.2 key

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



 theorem computedFullProjection_measurable (source target : List ℕ) (N : ℕ) :
    Measurable (computedFullProjection source target N) := by
  apply measurable_fun_sum
  · exact measurable_const
  · exact measurable_inr.comp (computedExecutionProjection_measurable source target N)

 theorem computedFullProjection_law (source target : List ℕ) (N : ℕ) (epsilon : BinaryFraction) :
    (computedFullLaw source target N epsilon).map (computedFullProjection source target N) =
      computedPhysicalLaw source target N epsilon := by
  unfold computedFullLaw computedPhysicalLaw physicalUniformLaw
  split_ifs with hlarge
  · rw [Measure.map_map (computedFullProjection_measurable source target N) measurable_inr]
    have heq : computedFullProjection source target N ∘ Sum.inr =
        Sum.inr ∘ computedExecutionProjection source target N := rfl
    rw [heq, ← Measure.map_map measurable_inr (computedExecutionProjection_measurable source target N),
      computedExecutionProjection_law]
  · rw [Measure.map_dirac]
    rfl


 theorem computed_full_conditional_accuracy (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N)
    (coarseBernstein : FiniteBernsteinInput (Measure.pi fun _ : Fin (integerParameters N).B =>
      (PMF.uniformOfFintype (Fin (integerParameters N).B)).toMeasure))
    (groupBernstein : ∀ b : ℕ, ∀ h : Fin
      (groupDyadicScales (integerParameters N).M b (inputSmallLog N)).length,
      FiniteBernsteinInput (Measure.pi fun _ : Fin
        (groupSampleCount (integerParameters N).M (inputSmallLog N ^ 80) b
          (groupDyadicScaleAt (integerParameters N).M b (inputSmallLog N) h)) =>
        (PMF.uniformOfFintype (Fin (integerParameters N).M)).toMeasure)) :
    (2 / 3 : ℝ) ≤ (computedFullLaw source target N epsilon).real
      {outcome | EditDistortion.edit source target ≤ computedFullAnswer source target N outcome ∧
        (computedFullAnswer source target N outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  have h := computed_physical_uniform_conditional_accuracy source target N epsilon hepsilon hsize
    coarseBernstein groupBernstein
  rw [← computedFullProjection_law source target N epsilon,
    map_measureReal_apply (computedFullProjection_measurable source target N)
      (Set.to_countable _).measurableSet] at h
  exact h

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





theorem integerInputSymbolBits_fits (source target : List ℤ) (z : ℤ)
    (hz : z ∈ source ++ target) :
    integerSymbolCode z < 2 ^ integerInputSymbolBits source target := by
  exact ((integerSymbolCode_bound z).trans
    (Nat.mul_le_mul_left 2 (integerMagnitude_mem _ z hz))).trans_lt (Nat.lt_size_self _)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
attribute [local instance] queryArityNeZero queryRoundsNeZero

/-- The binary evaluator returns exactly the answer used in the execution-law theorem. -/
theorem computedQueryAnswerWithWork_execution (source target : List ℕ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (occurrence : BinaryMemo PositionCounts) (symbolBits positionBits : ℕ)
    (hs : ∀ z ∈ source, z < 2 ^ symbolBits) (ht : ∀ z ∈ target, z < 2 ^ symbolBits)
    (hp : target.length ≤ 2 ^ positionBits)
    (htable : occurrence = occurrenceBuild symbolBits positionBits target.zipIdx)
    (execution : ComputedExecutionOutcome source target N) :
    bitWordValue (computedQueryAnswerWithWork source target N occurrence symbolBits positionBits
      (computedExecutionAccepted source target N execution)).1 =
      computedFullAnswer source target N (.inr execution) := by
  have hf : 3 ≤ smallLogExponent N := by
    have h := (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hlarge.2.1.1
    omega
  rw [computedQueryAnswerWithWork_value source target N occurrence symbolBits positionBits _
    (largeAccuracyInput_pos N epsilon.value hlarge.2.1) hlarge.2.1.1 hf hsize hlarge.2.2 hs ht hp htable]
  change _ = physicalFamilyMemoAnswer source target N (integerParameters N).P (integerParameters N).T
    (integerParameters N).S (inputHeight N) (Nat.two_pow_pos _)
    (16384 * inputHeight N + 5) (computedFamilyMemoCode source target N (inputHeight N ^ 2))
    (finalTargetState target.length) (computedExecutionAccepted source target N execution)
  simp only [physicalFamilyMemoAnswer, finalTargetState, substring, List.drop_zero, List.take_length,
    computedFamilyResult]

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryOutput
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem integerBinaryOutput_execution (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hlarge : physicalLargeInput N epsilon)
    (hsize : source.length + target.length ≤ N)
    (execution : ComputedExecutionOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    bitWordValue (integerBinaryOutput source target N
      (computedExecutionAccepted _ _ N execution)).1 =
      computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N (.inr execution) := by
  apply computedQueryAnswerWithWork_execution _ _ _ epsilon hlarge
    (by simpa only [List.length_map] using hsize)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_left _ hz)
  · intro a ha
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp ha
    exact integerInputSymbolBits_fits source target z (List.mem_append_right _ hz)
  · simpa only [List.length_map, integerInputPositionBits] using (Nat.lt_size_self target.length).le
  · rfl

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_IntegerBinaryAccuracy
attribute [-simp] _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open MeasureTheory

theorem integerBinaryAnswer_large (source target : List ℤ) (N : ℕ) (epsilon : BinaryFraction)
    (hlarge : physicalLargeInput N epsilon) (hsize : source.length + target.length ≤ N)
    (outcome : ComputedFullOutcome (source.map integerSymbolCode) (target.map integerSymbolCode) N) :
    integerBinaryAnswer source target N epsilon outcome =
      computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N outcome := by
  cases outcome with
  | inl unitValue => simp only [integerBinaryAnswer, hlarge, ite_true, if_true]; rfl
  | inr execution =>
    simp only [integerBinaryAnswer, hlarge, ite_true, if_true]
    exact integerBinaryOutput_execution source target N epsilon hlarge hsize execution

/-- Accuracy of the concrete binary answer under the finite Bernstein
hypothesis for the reference algorithm. -/
theorem integerBinaryAnswer_conditional_accuracy_oai (source target : List ℤ) (N : ℕ)
    (epsilon : BinaryFraction) (hepsilon : 0 < epsilon.value)
    (hsize : source.length + target.length ≤ N) (bernstein : ComputedBernsteinInputs N) :
    (2 / 3 : ℝ) ≤ (computedFullLaw (source.map integerSymbolCode) (target.map integerSymbolCode) N epsilon).real
      {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
        (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} := by
  by_cases hlarge : physicalLargeInput N epsilon
  · have heq : integerBinaryAnswer source target N epsilon =
        computedFullAnswer (source.map integerSymbolCode) (target.map integerSymbolCode) N :=
      funext (integerBinaryAnswer_large source target N epsilon hlarge hsize)
    rw [heq]
    have h := computed_full_conditional_accuracy (source.map integerSymbolCode) (target.map integerSymbolCode)
      N epsilon hepsilon (by simpa only [List.length_map] using hsize) bernstein.1 bernstein.2
    simpa only [integerSymbols_edit] using h
  · have heq (outcome) : integerBinaryAnswer source target N epsilon outcome = EditDistortion.edit source target := by
      simp only [integerBinaryAnswer, hlarge, ite_false, if_false, exactSuffixAnswer_eq_edit, integerSymbols_edit]
    have hupper : (EditDistortion.edit source target : ℝ) ≤
        (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target := by
      have hp : (0 : ℝ) < epsilon.value := by exact_mod_cast hepsilon
      nlinarith only [hp, Nat.cast_nonneg (α := ℝ) (EditDistortion.edit source target)]
    have hevent : {outcome | EditDistortion.edit source target ≤ integerBinaryAnswer source target N epsilon outcome ∧
        (integerBinaryAnswer source target N epsilon outcome : ℝ) ≤
          (1 + (epsilon.value : ℝ)) * EditDistortion.edit source target} = Set.univ := by
      ext outcome
      simp only [Set.mem_ofPred_eq, heq, le_refl, true_and, Set.mem_univ, iff_true]
      exact hupper
    rw [hevent, probReal_univ]
    norm_num

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy_oai := @OAI.EditApproximation.integerBinaryAnswer_conditional_accuracy_oai
