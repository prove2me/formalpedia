-- Prove2me | solution 1 for OAI.EditApproximation.computedTableQueryBudget_cap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T17:42:21.932814+00:00
-- url     : https://prove2.me/submissions/1a50ee84-6a21-4405-a35a-8ac16d1c2d61

import Mathlib
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Definitions.Def_OAIQ361V3Ea002
import Definitions.Def_OAIQ361V3Ea003
import Theorems.Thm_OAI_EditApproximation_computedActiveQueryBudget_cap

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_Parameters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Probability_FiniteBitPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A structural polynomial bound for finite Boolean arithmetic loops.
The expression language includes only operations whose magnitude is bounded
by a fixed power of a common input bound. -/

namespace EditApproximation

namespace FiniteBitPolynomial

theorem eval_le_pow {ι : Type*} (p : FiniteBitPolynomial ι) (env : ι → ℕ)
    (S : ℕ) (hS : 2 ≤ S) (henv : ∀ i, env i ≤ S) :
    p.eval env ≤ S ^ p.degree := by
  induction p with
  | input i => simpa only [eval, degree, pow_one] using henv i
  | constant n =>
    exact (Nat.lt_size_self n).le.trans (Nat.pow_le_pow_left hS _)
  | add a b ha hb =>
    have ha' := ha.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_left a.degree b.degree))
    have hb' := hb.trans (Nat.pow_le_pow_right (by omega : 0 < S) (Nat.le_max_right a.degree b.degree))
    change a.eval env + b.eval env ≤ S ^ (max a.degree b.degree + 1)
    calc
      _ ≤ 2 * S ^ max a.degree b.degree := by omega
      _ ≤ S * S ^ max a.degree b.degree := Nat.mul_le_mul_right _ hS
      _ = _ := (pow_succ' S _).symm
  | mul a b ha hb =>
    exact (Nat.mul_le_mul ha hb).trans_eq (pow_add S a.degree b.degree).symm
  | pow a n ha =>
    exact (Nat.pow_le_pow_left ha n).trans_eq (pow_mul S a.degree n).symm
  | maximum a b ha hb =>
    exact max_le
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
      (hb.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_right a.degree b.degree)))
  | minimum a b ha _ =>
    exact (Nat.min_le_left _ _).trans
      (ha.trans (Nat.pow_le_pow_right (by omega) (Nat.le_max_left a.degree b.degree)))
  | bitLength a ha =>
    exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans ha

end FiniteBitPolynomial
end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedEarlierInputBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedNumericalParameters
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedShellPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed-degree envelopes for the literal representative, online outer,
and continuation loops. Large action counts are explicit numeric inputs. -/

namespace EditApproximation

attribute [local irreducible] preparedBandBitDegree sampledOnlineBitDegree

theorem localRepresentativesBitBudget_fixedPower (P F B X : ℕ) (hX : 2 ≤ X)
    (hP : P ≤ X) (hF : F ≤ X) (hB : B ≤ X) :
    BinaryFraction.localRepresentativesBitBudget P F B ≤ X ^ representativeShellDegree := by
  let env : Fin 8 → ℕ := ![P, F, B, 0, 0, 0, 0, 0]
  have heval : representativeShell.eval env = BinaryFraction.localRepresentativesBitBudget P F B := by
    simp only [representativeShell, spQuery, spGuard, spBox, spGrid, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact representativeShell.eval_le_pow env X hX henv

theorem physicalContinuationBitBudget_fixedPower (M P nr ng no B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hr : nr ≤ X) (hg : ng ≤ X) (ho : no ≤ X) (hB : B ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.physicalContinuationBitBudget M P nr ng no B ≤ X ^ physicalShellDegree := by
  let env : Fin 8 → ℕ := ![M, P, nr, ng, no, B, (40 * P + 2) ^ (2 * M), ((40 * P + 2) ^ 2 + 1) ^ (M + 1)]
  have heval : physicalShell.eval env = BinaryFraction.physicalContinuationBitBudget M P nr ng no B := by
    simp only [physicalShell, spConnectionWord, spSumStorage, spBox, spGrid, spConnectionWork,
      spSumWork, spSumWord, spContinuation, spBellman, spActionWork, spActionWord, spUpdate,
      FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact physicalShell.eval_le_pow env X hX henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedCachedKernelWork
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The complete refinement return includes literal power-denominator
construction, multiplication, division and trimming before cache insertion. -/

namespace EditApproximation

attribute [local irreducible] preparedCacheReturnBitDegree

theorem preparedCacheReturnBitBudget_fixedPower (M B n D X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hB : B ≤ X) (hn : n ≤ X) (hD : D ≤ X) :
    BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D ≤
      X ^ preparedCacheReturnBitDegree := by
  have heval : cacheReturnPolynomial.eval (cacheEnvironment M B n D) =
      BinaryFraction.powerDenominatorBitBudget n (BinaryFraction.preparedKernelWordBudget M B) D := rfl
  have henv : ∀ i, cacheEnvironment M B n D i ≤ X := by
    intro i
    fin_cases i <;> simp only [cacheEnvironment] <;> assumption
  rw [← heval]
  simpa only [preparedCacheReturnBitDegree] using cacheReturnPolynomial.eval_le_pow _ X hX henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedInitialPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Fixed degrees for the literal initial grid/minimum, trimmed seed
median, and child warmup average. Grid side length is an explicit input. -/

namespace EditApproximation

theorem cachedInitialProgramBitBudget_fixedPower (P Amax B X : ℕ) (hX : 2 ≤ X)
    (hB : B ≤ X) (hL : 64 * Amax ^ 2 * P + 2 ≤ X) :
    BinaryFraction.cachedInitialProgramBitBudget P Amax B ≤ X ^ preparedCachedInitialBitDegree := by
  let env : Fin 2 → ℕ := ![B, 64 * Amax ^ 2 * P + 2]
  have heval : cachedInitialShellPolynomial.eval env = BinaryFraction.cachedInitialProgramBitBudget P Amax B := by
    simp only [cachedInitialShellPolynomial, initialShellPolynomial, ipScale, ipGridScale, ipBox, ipGrid,
      ipCenter, ipMinimum, ipMinimumWord, ipConeInput, ipCone, ipSeed, ipGap, ipDistance,
      FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact cachedInitialShellPolynomial.eval_le_pow env X hX henv

theorem seedMedianBitBudget_fixedPower (n B X : ℕ) (hX : 2 ≤ X) (hn : n ≤ X) (hB : B ≤ X) :
    BinaryFraction.seedMedianBitBudget n B ≤ X ^ preparedMedianBitDegree := by
  let env : Fin 2 → ℕ := ![n, B]
  have heval : medianShellPolynomial.eval env = BinaryFraction.seedMedianBitBudget n B := by
    simp only [medianShellPolynomial, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> assumption
  rw [← heval]
  exact medianShellPolynomial.eval_le_pow env X hX henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedWarmupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! The initial warmup Bellman scan and its cache return are covered by
the same fixed polynomial envelope as the full continuation. -/

namespace EditApproximation

attribute [local irreducible] representativeShellDegree physicalShellDegree
  preparedCacheReturnBitDegree

private theorem warmup_le_continuation (M P F B : ℕ) :
    BinaryFraction.localWarmupBitBudget M P F B ≤
      BinaryFraction.localRepresentativesBitBudget P F B +
        BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
          0 0 (B + 4) + 3 := by
  unfold BinaryFraction.localWarmupBitBudget BinaryFraction.physicalContinuationBitBudget
    BinaryFraction.localContinuationBitBudget
  dsimp only
  simp only [Nat.zero_mul, Nat.add_assoc, Nat.reduceAdd]
  omega

private theorem warmup_width_le_continuation (M B : ℕ) :
    BinaryFraction.localWarmupWordBudget M B ≤ BinaryFraction.preparedKernelWordBudget M B := by
  unfold BinaryFraction.localWarmupWordBudget BinaryFraction.preparedKernelWordBudget
    BinaryFraction.localContinuationWordBudget BinaryFraction.localContinuationInputBudget
    BinaryFraction.refinementUpdateWordBudget
  dsimp only
  omega

theorem cachedWarmupBitBudget_fixedPower (M P F B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hB : B + 4 ≤ X)
    (hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.localWarmupBitBudget M P F B +
        BinaryFraction.powerDenominatorBitBudget 0 (BinaryFraction.localWarmupWordBudget M B) 1 + 1 ≤
      X ^ preparedWarmupBitDegree := by
  let D := max representativeShellDegree (max physicalShellDegree preparedCacheReturnBitDegree)
  have hpos : 0 < X := by omega
  have hr := (localRepresentativesBitBudget_fixedPower P F B X hX hP hF (by omega)).trans
    (Nat.pow_le_pow_right hpos (show representativeShellDegree ≤ D from Nat.le_max_left _ _))
  have hc := (physicalContinuationBitBudget_fixedPower M P _ 0 0 (B + 4) X hX hM hP hrep
    (Nat.zero_le _) (Nat.zero_le _) hB hV hCartesian).trans
      (Nat.pow_le_pow_right hpos (show physicalShellDegree ≤ D from
        (Nat.le_max_left _ _).trans (Nat.le_max_right _ _)))
  have hret := (preparedCacheReturnBitBudget_fixedPower M B 0 1 X hX hM (by omega)
    (Nat.zero_le _) (by omega)).trans
      (Nat.pow_le_pow_right hpos (show preparedCacheReturnBitDegree ≤ D from
        (Nat.le_max_right _ _).trans (Nat.le_max_right _ _)))
  have hreturn : BinaryFraction.powerDenominatorBitBudget 0 (BinaryFraction.localWarmupWordBudget M B) 1 ≤
      X ^ D := by
    apply le_trans _ hret
    unfold BinaryFraction.powerDenominatorBitBudget
    gcongr
    exact warmup_width_le_continuation M B
  have hw := warmup_le_continuation M P F B
  have hone : 1 ≤ X ^ D := Nat.succ_le_of_lt (pow_pos hpos D)
  have he : 8 ≤ X ^ 3 := (show 8 = (2 : ℕ) ^ 3 by decide).trans_le (Nat.pow_le_pow_left hX 3)
  calc
    _ ≤ 3 * X ^ D + 4 := by omega
    _ ≤ 8 * X ^ D := by omega
    _ ≤ X ^ 3 * X ^ D := Nat.mul_le_mul_right _ he
    _ = X ^ preparedWarmupBitDegree := by
      rw [← pow_add]
      change X ^ (3 + D) = X ^ (D + 3)
      rw [Nat.add_comm 3 D]

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedSourceAddressBits
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
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

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryInitialWarmupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Polynomial certificate for the complete initial and warmup dispatch,
including actual gathers, buffer scans, and the previous-pass median. -/

namespace EditApproximation

private theorem initialWarmupPolynomial_eval (M P F Amax copies J symbolBits positionBits B C : ℕ) :
    initialWarmupPolynomial.eval (initialWarmupEnvironment M P F Amax copies J symbolBits positionBits B C) =
      queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C := by
  rfl

theorem queryChargedWarmupBitBudget_fixedPower (M P F Amax copies J symbolBits positionBits B C X : ℕ)
    (hX : 2 ≤ X)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hA : Amax ≤ X) (hc : copies ≤ X)
    (hJ : J ≤ X) (hs : symbolBits ≤ X) (hp : positionBits ≤ X) (hB : B ≤ X) (hC : C ≤ X)
    (hi : BinaryFraction.cachedInitialProgramBitBudget P Amax (B + 2) ≤ X)
    (hm : BinaryFraction.seedMedianBitBudget copies B ≤ X)
    (hw : BinaryFraction.localWarmupBitBudget M P F B ≤ X) :
    queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C ≤
      X ^ queryInitialWarmupBitDegree := by
  rw [← initialWarmupPolynomial_eval]
  apply initialWarmupPolynomial.eval_le_pow _ X hX
  intro i
  fin_cases i
  · exact hM
  · exact hP
  · exact hF
  · exact hA
  · exact hc
  · exact hJ
  · exact hs
  · exact hp
  · exact hB
  · exact hC
  · exact hi
  · exact hm
  · exact hw

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryWarmupUniformCost
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedCachedInitialBitDegree preparedMedianBitDegree
  preparedWarmupBitDegree queryInitialWarmupBitDegree

theorem queryChargedWarmupBitBudget_uniform_cap (M P F Amax copies J symbolBits positionBits B C X : ℕ)
    (hX : 64 ≤ X) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (hA : Amax ≤ X)
    (hc : copies ≤ X) (hJ : J ≤ X) (hs : symbolBits ≤ X) (hp : positionBits ≤ X)
    (hB : B ≤ X) (hC : C ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    queryChargedWarmupBitBudget M P F Amax copies J symbolBits positionBits B C ≤
      X ^ queryInitialWarmupDegree := by
  have hpos : 0 < X := by omega
  have hXX : X ≤ X ^ 16 := Nat.le_pow (by decide)
  have hB4 : B + 4 ≤ X ^ 16 := by
    have : B + 4 ≤ X ^ 2 := by nlinarith only [hB, hX]
    exact this.trans (Nat.pow_le_pow_right hpos (by decide))
  have hside : 64 * Amax ^ 2 * P + 2 ≤ X ^ 16 := by
    have hprod := Nat.mul_le_mul (Nat.pow_le_pow_left hA 2) hP
    have hcoef : 66 ≤ X ^ 2 := by nlinarith only [hX]
    calc
      _ ≤ 66 * (X ^ 2 * X) := by nlinarith only [hprod, hX]
      _ ≤ X ^ 2 * (X ^ 2 * X) := Nat.mul_le_mul_right _ hcoef
      _ = X ^ 5 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hpos (by decide)
  have hrepSide : 64 * F * P + 2 ≤ X ^ 4 := by
    have hprod := Nat.mul_le_mul hF hP
    have hcoef : 66 ≤ X ^ 2 := by nlinarith only [hX]
    calc
      _ ≤ 66 * X ^ 2 := by nlinarith only [hprod, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by ring
  have hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X ^ 16 := by
    calc
      _ ≤ X ^ 2 * (X ^ 4) ^ 2 := Nat.mul_le_mul (by nlinarith only [hB, hX])
        (Nat.pow_le_pow_left hrepSide 2)
      _ = X ^ 10 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hpos (by decide)
  have h16 : 2 ≤ X ^ 16 := (by omega : 2 ≤ X).trans hXX
  have hi := cachedInitialProgramBitBudget_fixedPower P Amax (B + 2) (X ^ 16) h16 (by omega) hside
  have hm := seedMedianBitBudget_fixedPower copies B (X ^ 16) h16 (hc.trans hXX) (hB.trans hXX)
  have hw := cachedWarmupBitBudget_fixedPower M P F B (X ^ 16) h16 (hM.trans hXX)
    (hP.trans hXX) (hF.trans hXX) hB4 hrep (hV.trans hXX) (hCart.trans hXX)
  have hid : preparedCachedInitialBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hmd : preparedMedianBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hwd : preparedWarmupBitDegree ≤ queryInitialWarmupPrimitiveDegree := by
    unfold queryInitialWarmupPrimitiveDegree; omega
  have hbase : X ≤ (X ^ 16) ^ queryInitialWarmupPrimitiveDegree :=
    hXX.trans (Nat.le_pow (Nat.le_max_left _ _))
  have hY : 2 ≤ (X ^ 16) ^ queryInitialWarmupPrimitiveDegree := (by omega : 2 ≤ X).trans hbase
  have hw0 : BinaryFraction.localWarmupBitBudget M P F B ≤ (X ^ 16) ^ preparedWarmupBitDegree := by
    omega
  have hwp : BinaryFraction.localWarmupBitBudget M P F B ≤
      (X ^ 16) ^ queryInitialWarmupPrimitiveDegree :=
    hw0.trans (Nat.pow_le_pow_right (pow_pos hpos 16) hwd)
  have h := queryChargedWarmupBitBudget_fixedPower M P F Amax copies J symbolBits positionBits B C
    ((X ^ 16) ^ queryInitialWarmupPrimitiveDegree) hY
    (hM.trans hbase) (hP.trans hbase) (hF.trans hbase) (hA.trans hbase) (hc.trans hbase)
    (hJ.trans hbase) (hs.trans hbase) (hp.trans hbase) (hB.trans hbase) (hC.trans hbase)
    (hi.trans (Nat.pow_le_pow_right (by positivity) hid))
    (hm.trans (Nat.pow_le_pow_right (by positivity) hmd)) hwp
  simpa only [← pow_mul, queryInitialWarmupDegree] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

/-- A single logarithmic word accommodates every power exponent needed
by the global integer and online-mass constructors. -/
 theorem computedParameterPower_word :
    ∀ᶠ N in atTop, ∀ k : ℕ,
      k ≤ 8000 * (coarseExponent (inputSmallLog N) + 1) →
      Nat.size (inputHeight N ^ k) ≤ inputHeight N := by
  filter_upwards [computed_sourceAddressBits_le_height 8000] with N hN
  intro k hk
  exact (natural_power_bit_length _ _).trans
    ((Nat.add_le_add_right (Nat.mul_le_mul_right _ hk) 1).trans hN)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedPreparedInputBounds
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

private theorem precision_power_bound (p : ℕ) : p + 20 ≤ 8000 * (p + 1) := by omega

private theorem prepared_loop_caps (H M P p : ℕ) (hH : 64 ≤ H)
    (hM : M ≤ H) (hP : 1 ≤ P) (hPcap : P ≤ H ^ (p + 20)) :
    (40 * P + 2) ^ (2 * M) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ H ^ ((100 * M + 100000) * (p + 1)) ∧
    (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((100 * M + 100000) * (p + 1)) := by
  have hHp : 0 < H := by omega
  have hbox : 40 * P + 2 ≤ H ^ (p + 22) := by
    calc
      _ ≤ 42 * P := by omega
      _ ≤ H ^ 2 * H ^ (p + 20) := Nat.mul_le_mul (by nlinarith only [hH]) hPcap
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hbase : (40 * P + 2) ^ 2 + 1 ≤ H ^ (2 * (p + 22) + 1) := by
    have hs := Nat.pow_le_pow_left hbox 2
    have hunit : 1 ≤ (H ^ (p + 22)) ^ 2 := one_le_pow₀ (one_le_pow₀ (by omega))
    calc
      _ ≤ 2 * (H ^ (p + 22)) ^ 2 := by omega
      _ ≤ H * (H ^ (p + 22)) ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by rw [← pow_mul, ← pow_succ']; congr 1; omega
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ (H ^ (p + 22)) ^ (2 * M) := Nat.pow_le_pow_left hbox _
      _ = H ^ ((p + 22) * (2 * M)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · calc
      _ ≤ (H ^ (2 * (p + 22) + 1)) ^ (M + 1) := Nat.pow_le_pow_left hbase _
      _ = H ^ ((2 * (p + 22) + 1) * (M + 1)) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])
  · have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    calc
      _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
      _ = H ^ ((2 * p + 46) * 80) := (pow_mul H _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right hHp (by nlinarith only [Nat.zero_le (M * p), Nat.zero_le p, Nat.zero_le M])

/-- Every numeric premise of the prepared kernel follows from the computed
parameters. Width assumptions here concern only the five actual parameter
words; cached data are added by `physicalPreparedStep_inputBounds`. -/
theorem computedPreparedNumericBounds :
    ∀ᶠ N : ℕ in atTop, ∀ nx ny : ℕ, nx + ny ≤ N → ∀ t : ℕ, t ≤ inputHeight N ^ 2 →
      ∀ tau a eta kappa delta : BinaryFraction,
      tau.width ≤ inputHeight N ^ 8 → a.width ≤ inputHeight N ^ 8 →
      eta.width ≤ inputHeight N ^ 8 → kappa.width ≤ inputHeight N ^ 8 →
      delta.width ≤ inputHeight N ^ 8 → |eta.value| ≤ ((inputHeight N ^ 5 : ℕ) : ℚ) →
      (0 ≤ kappa.value ∧ kappa.value ≤ 1) →
      ∀ integer : ℕ → TargetInterval ny → ℕ,
      (∀ b r, Nat.size (integer b r) ≤ inputHeight N) →
      BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := (integerParameters N).M)
        N (integerParameters N).P (inputSmallLog N) (40 * smallLogExponent N)
        (inputHeight N) (inputSmallLog N ^ 80) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8) (inputHeight N ^ 5)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t tau a eta kappa delta integer := by
  filter_upwards [computedParameterPower_word,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hpower hell
  intro nx ny hsize t ht tau a eta kappa delta htau ha heta hk hd hrate hkRange integer hint
  let H := inputHeight N
  let p := coarseExponent (inputSmallLog N)
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let L := (100 * M + 100000) * (p + 1)
  have hpowers : ∀ k : ℕ, k ≤ 8000 * (p + 1) → Nat.size (H ^ k) ≤ H := hpower
  change BinaryFraction.PreparedKernelNumericBounds (nx := nx) (M := M)
    N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (H ^ 8) (H ^ 5) (H ^ L) t
    tau a eta kappa delta integer
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hHp : 0 < H := by omega
  have hM : M ≤ H := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.div_le_self _ _)
  have hP : 1 ≤ P := one_le_pow₀ (by omega)
  have hPcap : P ≤ H ^ (p + 20) := le_rfl
  have hH8 : H ^ 2 ≤ H ^ 8 := Nat.pow_le_pow_right hHp (by decide)
  have hsmall : H + 2 ≤ H ^ 8 := (by nlinarith only [hH] : H + 2 ≤ H ^ 2).trans hH8
  have hHle : H ≤ H ^ 8 := by omega
  have hL : p + 20 ≤ L := by dsimp only [L]; nlinarith only [Nat.zero_le (M * p), Nat.zero_le M, Nat.zero_le p]
  have hL20 : 20 ≤ L := (Nat.le_add_left 20 p).trans hL
  have hHL : H ≤ H ^ L := Nat.le_pow (by omega)
  have hsizeN : Nat.size N ≤ H := computed_input_size_le_height N
  have hMF : Nat.size M ≤ H := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hM
  have hF : Nat.size (inputSmallLog N) ≤ H :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (computed_smallLog_le_height N)
  have hPs : Nat.size P ≤ H := by
    change Nat.size (H ^ (p + 20)) ≤ H
    exact hpowers (p + 20) (precision_power_bound p)
  have hQs : Nat.size (inputSmallLog N ^ 80) ≤ H :=
    (Nat.size_le_size (Nat.pow_le_pow_left (computed_smallLog_le_height N) 80)).trans
      (hpowers 80 (by omega))
  have he : smallLogExponent N ≤ H :=
    (Nat.lt_two_pow_self.le : smallLogExponent N ≤ inputSmallLog N).trans (computed_smallLog_le_height N)
  have htheta : 40 * smallLogExponent N + 1 ≤ H ^ 8 :=
    (by nlinarith only [he, hH] : 40 * smallLogExponent N + 1 ≤ H ^ 2).trans hH8
  have hscale : heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 8 := by
    have heM : heightExponent N / 20 ≤ H :=
      (Nat.div_le_self _ _).trans Nat.lt_two_pow_self.le
    exact (by nlinarith only [heM, he, hH] :
      heightExponent N / 20 + smallLogExponent N + 7 ≤ H ^ 2).trans hH8
  have hcoord : Nat.size (M * (40 * P + 2) ^ 2) ≤ H :=
    (Nat.size_le_size (wide_coordinate_budget_le H M P p hH hM hP hPcap)).trans
      (hpowers (2 * p + 45) (by omega))
  have hiter : Nat.size ((H + M * (40 * P + 2) ^ 2 + 2) ^ 80) ≤ H := by
    have hg := optimizer_parameter_budget_le H M P p hH hM hP hPcap
    have hi : (H + M * (40 * P + 2) ^ 2 + 2) ^ 80 ≤ H ^ ((2 * p + 46) * 80) := by
      calc
        _ ≤ (H ^ (2 * p + 46)) ^ 80 := Nat.pow_le_pow_left (by omega) 80
        _ = _ := (pow_mul H _ _).symm
    exact (Nat.size_le_size hi).trans (hpowers ((2 * p + 46) * 80) (by omega))
  have hcaps := prepared_loop_caps H M P p hH hM hP hPcap
  have hword : 3 * (H ^ 8 + 4) + 4 ≤ H ^ L := by
    have hunit : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    calc
      _ ≤ 19 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ (by nlinarith only [hH])
      _ = H ^ 10 := by rw [← pow_add]
      _ ≤ _ := Nat.pow_le_pow_right hHp (by omega)
  refine {
    largeBits := (by nlinarith only [hH] : 10 ≤ H ^ 2).trans hH8
    inputSize := hsizeN.trans hHle
    sourceSize := (Nat.add_le_add_right (Nat.size_le_size (show nx ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    targetSize := (Nat.add_le_add_right (Nat.size_le_size (show ny ≤ N by omega) |>.trans hsizeN) 2).trans hsmall
    aritySize := (Nat.add_le_add_right hMF 2).trans hsmall
    precisionSize := hPs.trans hHle
    factorSize := (Nat.add_le_add_right hF 2).trans hsmall
    sampleSize := (Nat.add_le_add_right hQs 2).trans hsmall
    thetaSize := htheta
    scaleSizes := hscale
    heightSize := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hHle
    coordinateSize := hcoord.trans hHle
    iterationSize := hiter.trans hHle
    drawSize := fun b r => (hint b r).trans hHle
    tauSize := htau
    factorWidth := ha
    rateSize := heta
    optimismSize := hk
    decrementSize := hd
    rateMagnitude := hrate
    optimismRange := hkRange
    scalePositive := ?_
    arityCap := hM.trans ?_
    precisionCap := hPcap.trans (Nat.pow_le_pow_right hHp hL)
    rateCap := Nat.pow_le_pow_right hHp (by omega)
    timeCap := ht.trans (Nat.pow_le_pow_right hHp (by omega))
    wordCap := hword
    actionCap := hcaps.1
    cartesianCap := hcaps.2.1
    iterationCap := hcaps.2.2 }
  · exact (by omega : 2 ≤ H).trans hHL
  · exact hHL

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryBudgetAlgebra
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

/-- Enlarge the exponent of the common computed kernel scale. -/
theorem computedLocalKernelBudget_mono (N D E : ℕ) (h : D ≤ E) :
    computedLocalKernelBudget D N ≤ computedLocalKernelBudget E N := by
  unfold computedLocalKernelBudget localKernelPowerExponent
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  exact Nat.mul_le_mul_left _ h

theorem computedLocalKernelBudget_three (N D x y z : ℕ) (hH : 3 ≤ inputHeight N)
    (hx : x ≤ computedLocalKernelBudget D N) (hy : y ≤ computedLocalKernelBudget D N)
    (hz : z ≤ computedLocalKernelBudget D N) :
    x + y + z ≤ computedLocalKernelBudget (D + 1) N := by
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := inputHeight N ^ L
  have hL : 1 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : inputHeight N ≤ S := Nat.le_pow hL
  have hx' : x ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hx
  have hy' : y ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hy
  have hz' : z ≤ S ^ D := by simpa only [S, L, computedLocalKernelBudget, localKernelPowerExponent, ← pow_mul] using hz
  have hsum : x + y + z ≤ 3 * S ^ D := by omega
  have h3S : 3 ≤ S := hH.trans hHS
  calc
    _ ≤ 3 * S ^ D := hsum
    _ ≤ S * S ^ D := Nat.mul_le_mul_right _ h3S
    _ = S ^ (D + 1) := (pow_succ' S D).symm
    _ = _ := by simp only [S, ← pow_mul]; rfl

/-- The fixed guard overhead at the eight-power word bound. -/
theorem computed_kernel_guard_cost (N : ℕ) (hH : 64 ≤ inputHeight N) :
    50 * inputHeight N ^ 8 + 100 ≤ computedLocalKernelBudget 1 N := by
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  have hL : 10 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hpow : 50 * H ^ 8 + 100 ≤ H ^ 10 := by
    have hone : 1 ≤ H ^ 8 := one_le_pow₀ (by omega)
    have hcoef : 150 ≤ H ^ 2 := by nlinarith only [hH]
    calc
      _ ≤ 150 * H ^ 8 := by omega
      _ ≤ H ^ 2 * H ^ 8 := Nat.mul_le_mul_right _ hcoef
      _ = _ := by rw [← pow_add]
  apply hpow.trans
  change H ^ 10 ≤ H ^ (L * 1)
  simpa only [Nat.mul_one] using Nat.pow_le_pow_right (by omega : 0 < H) hL

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryNumericZero
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.decrementReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.gainReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.optimisticTermReadWithWork_eq _root_.OAI.EditApproximation.BinaryFraction.queryGroupKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryOnlineKeysWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryRawHistoryInputsWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryScaleAt_value _root_.OAI.EditApproximation.BinaryFraction.queryScalesWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryChildCodeWithWork_value _root_.OAI.EditApproximation.queryGapStatesWithWork_value _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryHistoryCodeWithWork_value _root_.OAI.EditApproximation.queryHistoryEqualWithWork_value _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryIntervalEqualWithWork_value _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineKeyEqualWithWork_value _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryNumeric_zero :
    ∀ᶠ N : ℕ in atTop, BinaryFraction.PreparedKernelNumericBounds (nx := 0) (ny := 0)
      (M := (integerParameters N).M) N (integerParameters N).P (inputSmallLog N)
      (40 * smallLogExponent N) (inputHeight N) (inputSmallLog N ^ 80)
      (heightExponent N / 20) (smallLogExponent N) (inputHeight N ^ 8) (inputHeight N ^ 5)
      (inputHeight N ^ ((100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)))
      0 BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero
      (fun _ _ => 0) := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hz : BinaryFraction.zero.width ≤ inputHeight N ^ 8 := by
    change 1 ≤ inputHeight N ^ 8
    exact one_le_pow₀ (by omega)
  have hzv : BinaryFraction.zero.value = 0 := by
    norm_num [BinaryFraction.value, BinaryFraction.zero, SignedBinary.value, signedMagnitude, bitWordValue]
  exact hn 0 0 (by omega) 0 (by omega) _ _ _ _ _ hz hz hz hz hz
    (by rw [hzv]; simp) (by rw [hzv]; norm_num) (fun _ _ => 0) (by intro b r; simp)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryWarmupBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryInitialWarmupDegree queryInitialWarmupPrimitiveDegree queryInitialWarmupBitDegree queryChargedWarmupBitBudget

theorem computedQueryWarmupBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ Amax copies J symbolBits positionBits C : ℕ,
      Amax ≤ computedLocalKernelBudget 1 N → copies ≤ inputHeight N ^ 2 →
      J ≤ inputHeight N → symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 →
      C ≤ computedLocalKernelBudget K N →
      queryChargedWarmupBitBudget (integerParameters N).M (integerParameters N).P (inputSmallLog N)
        Amax copies J symbolBits positionBits (inputHeight N ^ 8) C ≤
        computedLocalKernelBudget (computedQueryWarmupDegree K) N := by
  filter_upwards [computedQueryNumeric_zero,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hnum hell
  intro Amax copies J symbolBits positionBits C hA hc hJ hs hp hC
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let L := (100 * M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hpos : 0 < H := lt_of_lt_of_le (by decide : 0 < 64) hH
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hHS : H ≤ S := Nat.le_pow ((by decide : 1 ≤ 8).trans hL)
  have hSX : S ≤ X := Nat.le_pow (Nat.succ_le_succ (Nat.zero_le K))
  have h8S : H ^ 8 ≤ S := Nat.pow_le_pow_right hpos hL
  have h2S : H ^ 2 ≤ S := Nat.pow_le_pow_right hpos ((by decide : 2 ≤ 8).trans hL)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hpos ((by decide : 3 ≤ 8).trans hL)
  have hCX : C ≤ X := by
    apply hC.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul_left L (Nat.le_succ K))
  have hAS : Amax ≤ S := by
    simpa only [S, H, L, M, computedLocalKernelBudget, localKernelPowerExponent, Nat.mul_one] using hA
  have hAX : Amax ≤ X := hAS.trans hSX
  have h := queryChargedWarmupBitBudget_uniform_cap M P (inputSmallLog N) Amax copies J
    symbolBits positionBits (H ^ 8) C X (hH.trans (hHS.trans hSX))
    (hnum.arityCap.trans hSX) (hnum.precisionCap.trans hSX)
    ((computed_smallLog_le_height N).trans (hHS.trans hSX)) hAX
    (hc.trans (h2S.trans hSX)) (hJ.trans (hHS.trans hSX))
    (hs.trans (h3S.trans hSX)) (hp.trans (h3S.trans hSX)) (h8S.trans hSX) hCX
    (hnum.actionCap.trans hSX) (hnum.cartesianCap.trans hSX)
  simpa only [X, S, H, L, computedLocalKernelBudget, localKernelPowerExponent,
    computedQueryWarmupDegree, ← pow_mul, Nat.mul_assoc] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryTableBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter
attribute [local irreducible] queryLocalProgramBitDegree queryCallbackShellDegree queryInitialWarmupDegree

theorem computedTableQueryBudget_cap_oai :
    ∀ᶠ N : ℕ in atTop, ∀ Amax J symbolBits positionBits t : ℕ,
      Amax ≤ computedLocalKernelBudget 1 N → J ≤ inputHeight N →
      symbolBits ≤ inputHeight N ^ 3 → positionBits ≤ inputHeight N ^ 3 → t ≤ inputHeight N ^ 2 →
      computedTableQueryBudget N Amax J symbolBits positionBits t ≤
        computedLocalKernelBudget computedTableQueryDegree N := by
  filter_upwards [computedActiveQueryBudget_cap, computedQueryWarmupBudget_cap 1,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hactive hwarm hell
  intro Amax J symbolBits positionBits t hA hJ hs hp ht
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hg := computed_kernel_guard_cost N hH
  have hw := hwarm Amax (inputHeight N ^ 2) J symbolBits positionBits 2 hA le_rfl hJ hs hp (by omega)
  have ha := hactive J t hJ ht
  let D := max 2 (max (computedQueryWarmupDegree 1) computedActiveQueryDegree)
  have hover : 80 * (inputHeight N ^ 8 + 1) ≤ computedLocalKernelBudget 2 N := by
    have hS : 2 ≤ computedLocalKernelBudget 1 N := by omega
    have hsq : computedLocalKernelBudget 2 N = (computedLocalKernelBudget 1 N) ^ 2 := by
      unfold computedLocalKernelBudget localKernelPowerExponent
      simp only [Nat.mul_one, pow_mul]
    rw [hsq]
    nlinarith only [hg, hS]
  have hbound := computedLocalKernelBudget_three N D _ _ _ (by omega)
    (hover.trans (computedLocalKernelBudget_mono N 2 D (Nat.le_max_left _ _)))
    (hw.trans (computedLocalKernelBudget_mono N (computedQueryWarmupDegree 1) D
      ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))))
    (ha.trans (computedLocalKernelBudget_mono N computedActiveQueryDegree D
      ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))))
  exact hbound

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedTableQueryBudget_cap_oai := @OAI.EditApproximation.computedTableQueryBudget_cap_oai
