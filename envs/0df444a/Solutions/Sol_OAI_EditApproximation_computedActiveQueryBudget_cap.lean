-- Prove2me | solution 1 for OAI.EditApproximation.computedActiveQueryBudget_cap
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-17T16:33:35.219394+00:00
-- url     : https://prove2.me/submissions/e0653cd9-fa79-4642-ba3d-90479a6b408f

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
import Definitions.Def_OAIQ361V3Ea004

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Binary_BinarySampledGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed polynomial bounds the actual sampled-member bit counter. The
scale is supplied through its bit length, so a large distance scale does
not introduce a spurious linear dependence on that scale. -/

namespace EditApproximation

private theorem sampledGroupPolynomial_eval (M T exponent b vertices B : ℕ) :
    sampledGroupPolynomial.eval (sampledGroupEnvironment M T exponent b vertices B) =
      BinaryFraction.sampledMemberWordBudget M T b B +
        BinaryFraction.sampledMemberBitBudget M T exponent b vertices B := rfl

theorem sampledMemberBitBudget_fixedPower (M T exponent b vertices B S : ℕ)
    (hS : 2 ≤ S) (hM : M ≤ S) (hT : T ≤ S) (he : exponent ≤ S)
    (hb : Nat.size b ≤ S) (hv : vertices ≤ S) (hB : B ≤ S) :
    BinaryFraction.sampledMemberWordBudget M T b B ≤ S ^ sampledGroupBitDegree ∧
      BinaryFraction.sampledMemberBitBudget M T exponent b vertices B ≤ S ^ sampledGroupBitDegree := by
  have henv : ∀ i, sampledGroupEnvironment M T exponent b vertices B i ≤ S := by
    intro i
    fin_cases i <;> simp only [sampledGroupEnvironment] <;> assumption
  have h := sampledGroupPolynomial.eval_le_pow (sampledGroupEnvironment M T exponent b vertices B) S hS henv
  rw [sampledGroupPolynomial_eval] at h
  exact ⟨(Nat.le_add_right _ _).trans h, (Nat.le_add_left _ _).trans h⟩

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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedBandPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree bound for the complete band constructor. The sole
non-polynomial quantity is the actual Cartesian-product list bound, an
explicit input subsequently bounded by the computed grid parameters. -/

namespace EditApproximation

private theorem preparedBandPolynomial_eval (e b M P v w B : ℕ) :
    preparedBandPolynomial.eval (preparedBandEnvironment e b M P v w B) =
      BinaryFraction.preparedUnskippedBitBudget e b M P v w B := rfl

theorem preparedUnskippedBitBudget_fixedPower (e b M P v w B S : ℕ)
    (hS : 2 ≤ S) (he : e ≤ S) (hb : Nat.size b ≤ S) (hM : M ≤ S) (hP : P ≤ S)
    (hv : v ≤ S) (hw : w ≤ S) (hB : B ≤ S)
    (hC : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ S) :
    BinaryFraction.preparedUnskippedBitBudget e b M P v w B ≤ S ^ preparedBandBitDegree := by
  have henv : ∀ i, preparedBandEnvironment e b M P v w B i ≤ S := by
    intro i
    fin_cases i <;> simp only [preparedBandEnvironment] <;> assumption
  simpa only [preparedBandPolynomial_eval, preparedBandBitDegree] using
    preparedBandPolynomial.eval_le_pow _ S hS henv

theorem representativeCompleteBitBudget_fixedPower (M vertices B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hV : vertices ≤ X) (hB : B ≤ X) :
    BinaryFraction.representativeCompleteBitBudget M vertices B ≤ X ^ representativeCompleteBitDegree := by
  let env : Fin 8 → ℕ := ![M, vertices, B, 0, 0, 0, 0, 0]
  have heval : (bpRepresentative (.input 0) (.input 1) (.input 2)).eval env =
      BinaryFraction.representativeCompleteBitBudget M vertices B := by rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact FiniteBitPolynomial.eval_le_pow _ env X hX henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap for the complete cell selector, including all band
construction and exact finite-count sampled scores. -/

namespace EditApproximation

private theorem cellGroupPolynomial_eval (M P B X : ℕ) :
    cellGroupPolynomial.eval (cellGroupEnvironment M P B X) =
      BinaryFraction.cellCentersBitBudget P P B + (P + 1) ^ 2 * (X ^ preparedBandBitDegree + 3) +
        (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
        1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 + 2 := rfl

theorem preparedCellGroupBitBudget_fixedPower (M T e b P B X : ℕ)
    (hX : 2 ≤ X) (hM : M ≤ X) (hT : T ≤ X) (he : e ≤ X) (hb : Nat.size b ≤ X)
    (hP : P ≤ X) (hB : B ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.preparedCellGroupBitBudget M T e b P B ≤ X ^ preparedCellGroupBitDegree := by
  let V := (40 * P + 2) ^ (2 * M)
  have hband := preparedUnskippedBitBudget_fixedPower e b M P V V B X hX he hb hM hP hV hV hB hCartesian
  have hmember := sampledMemberBitBudget_fixedPower M T e b V B X hX hM hT he hb hV hB
  have hr : BinaryFraction.roundedBandBitBudget e b M V B ≤ X ^ sampledGroupBitDegree := by
    apply le_trans _ hmember.2
    unfold BinaryFraction.sampledMemberBitBudget
    omega
  have hc : BinaryFraction.connectionBitBudget M B ≤ X ^ sampledGroupBitDegree := by
    apply le_trans _ hmember.2
    unfold BinaryFraction.sampledMemberBitBudget
    omega
  have hs : BinaryFraction.selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B ≤
      (P + 1) ^ 2 * (X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3) +
        1 + 2 * X ^ sampledGroupBitDegree + 2 * B + 2 * M + 6 := by
    unfold BinaryFraction.selectedGroupBitBudget
    have hw := Nat.pow_le_pow_left (Nat.add_le_add_right hmember.1 1) 2
    have hm := Nat.mul_le_mul_left ((P + 1) ^ 2)
      (show BinaryFraction.sampledMemberBitBudget M T e b V B +
        1000 * (BinaryFraction.sampledMemberWordBudget M T b B + 1) ^ 2 + 3 ≤
          X ^ sampledGroupBitDegree + 1000 * (X ^ sampledGroupBitDegree + 1) ^ 2 + 3 by
        exact Nat.add_le_add_right (Nat.add_le_add hmember.2 (Nat.mul_le_mul_left 1000 hw)) 3)
    omega
  have hmajor : BinaryFraction.preparedCellGroupBitBudget M T e b P B ≤
      cellGroupPolynomial.eval (cellGroupEnvironment M P B X) := by
    rw [cellGroupPolynomial_eval]
    unfold BinaryFraction.preparedCellGroupBitBudget
    have hp := Nat.mul_le_mul_left ((P + 1) ^ 2) (Nat.add_le_add_right hband 3)
    change BinaryFraction.cellCentersBitBudget P P B +
      (P + 1) ^ 2 * (BinaryFraction.preparedUnskippedBitBudget e b M P V V B + 3) +
      BinaryFraction.selectedGroupBitBudget M T e b ((P + 1) ^ 2) V B + 2 ≤ _
    omega
  have henv : ∀ i, cellGroupEnvironment M P B X i ≤ X := by
    intro i
    fin_cases i <;> simp only [cellGroupEnvironment] <;> omega
  exact hmajor.trans (cellGroupPolynomial.eval_le_pow _ X hX henv)

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Geometry_PreparedLocalGroupPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A fixed-degree cap on all whole-cell loops at a query. Distance scales
enter through their bit length; their numeric size is never charged. -/

namespace EditApproximation

private theorem localGroupPolynomial_eval (F thetaPow B eM eF X : ℕ) :
    localGroupPolynomial.eval (localGroupEnvironment F thetaPow B eM eF X) =
      localGroupMajorant F thetaPow B eM eF X := rfl

theorem preparedLocalGroupsBitBudget_fixedPower (N M P F exponent eM eF B X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (htheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCartesian : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤
      X ^ preparedLocalGroupBitDegree := by
  let count := max 1 N.bits.length
  let K := (32 * F + 2) * 2 ^ exponent + 2
  let scale := 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
    BinaryFraction.targetCellsBitBudget K K (4 * B + 40) +
    K ^ 2 * (BinaryFraction.groupScalesBitBudget eM B eF + X ^ preparedCellGroupBitDegree + 4) + B + 4
  let cost := BinaryFraction.localEligibilityBitBudget (B + 3) + scale + B + 4 + K ^ 2 + 3
  have hcount : count ≤ B + 1 := by dsimp only [count]; rw [Nat.size_eq_bits_len]; omega
  have hscale (eb : ℕ) (heb : eb ∈ List.range count) :
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B ≤ scale := by
    have heB : eb ≤ B := by have := List.mem_range.mp heb; omega
    have hbb : Nat.size (2 ^ eb) ≤ X := by rw [Nat.size_pow]; omega
    have hc := preparedCellGroupBitBudget_fixedPower M (7 + eM + eF) exponent (2 ^ eb) P (16 * B + 200) X
      hX hM hscales he hbb hP hword hV hCartesian
    have hs : BinaryFraction.groupScalesBitBudget eM eb eF ≤
        BinaryFraction.groupScalesBitBudget eM B eF := by
      unfold BinaryFraction.groupScalesBitBudget
      gcongr
      exact Nat.size_le_size heB
    unfold BinaryFraction.preparedLocalGroupScaleBitBudget
    change 2000 * (B + 4) ^ 2 + 500 * (B + 1) ^ 2 +
      BinaryFraction.targetCellsBitBudget K K (4 * B + 40) + K ^ 2 *
        (BinaryFraction.groupScalesBitBudget eM eb eF +
          BinaryFraction.preparedCellGroupBitBudget M (7 + eM + eF) exponent (2 ^ eb) P (16 * B + 200) + 4) + eb + 4 ≤ _
    dsimp only [scale]
    gcongr
  have hsum : ((List.range count).map fun eb => BinaryFraction.localEligibilityBitBudget (B + 3) +
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3).sum ≤
        count * cost := by
    have hh := List.sum_le_sum (l := List.range count)
      (f := fun eb : ℕ => BinaryFraction.localEligibilityBitBudget (B + 3) +
        BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3)
      (g := fun _ => cost) (by
      intro eb heb
      have heB : eb ≤ B := by have := List.mem_range.mp heb; omega
      have hs := hscale eb heb
      dsimp only [cost]
      omega)
    simpa [List.map_const', List.length_range, List.sum_replicate, nsmul_eq_mul] using hh
  have hmajor : BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤
      localGroupMajorant F (2 ^ exponent) B eM eF X := by
    have hh := hsum.trans (Nat.mul_le_mul_right cost hcount)
    unfold BinaryFraction.preparedLocalGroupsBitBudget
    change ((List.range count).map fun eb : ℕ => BinaryFraction.localEligibilityBitBudget (B + 3) +
      BinaryFraction.preparedLocalGroupScaleBitBudget M P F exponent eM eF eb B + eb + 4 + K ^ 2 + 3).sum +
      count + N.bits.length + 2 ≤ _
    unfold localGroupMajorant
    change _ ≤ (B + 1) * cost + (B + 1) + B + 2
    have hNbits : N.bits.length ≤ B := by simpa only [Nat.size_eq_bits_len] using hN
    omega
  have henv : ∀ i, localGroupEnvironment F (2 ^ exponent) B eM eF X i ≤ X := by
    intro i
    fin_cases i <;> simp [localGroupEnvironment] <;> omega
  exact hmajor.trans (by
    rw [← localGroupPolynomial_eval]
    exact localGroupPolynomial.eval_le_pow _ X hX henv)

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

theorem preparedLocalOnlineBitBudget_fixedPower (M P B X : ℕ) (hX : 2 ≤ X)
    (hM : M ≤ X) (hB : B ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X) :
    BinaryFraction.preparedLocalOnlineBitBudget M P B X ≤ X ^ onlineShellDegree := by
  let env : Fin 8 → ℕ := ![M, (40 * P + 2) ^ (2 * M), B, X, 0, 0, 0, 0]
  have heval : onlineShell.eval env = BinaryFraction.preparedLocalOnlineBitBudget M P B X := by
    simp only [onlineShell, spQuery, spGuard, spOnline, spCoordinates, spPower, FiniteBitPolynomial.eval]
    simp only [env, Matrix.cons_val_zero]
    rfl
  have henv : ∀ i, env i ≤ X := by intro i; fin_cases i <;> simp [env] <;> omega
  rw [← heval]
  exact onlineShell.eval_le_pow env X hX henv

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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryCallbackPolynomial
attribute [-instance] _root_.OAI.EditApproximation.localCommonTraceFintype _root_.OAI.EditApproximation.localScheduledSeedDrawFintype _root_.OAI.EditApproximation.scheduledSeedDrawFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

theorem queryCallbackShell_fixedPower (T J B V C W X : ℕ) (hX : 2 ≤ X)
    (hT : T ≤ X) (hJ : J ≤ X) (hB : B ≤ X) (hV : V ≤ X) (hC : C ≤ X) (hW : W ≤ X) :
    BinaryFraction.queryPhysicalDataBudget T J B V C (BinaryFraction.queryFamilySourceReadBudget J B W) ≤
      X ^ queryCallbackShellDegree := by
  have h := callbackPolynomial.eval_le_pow ![T, J, B, V, C, W] X hX (by
    intro i
    fin_cases i
    · exact hT
    · exact hJ
    · exact hB
    · exact hV
    · exact hC
    · exact hW)
  exact h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryGatherPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! A finite polynomial certificate for the complete adaptive gather cost.
The four kernel bounds and the two Cartesian counts
are explicit inputs. Every remaining operation is addition, multiplication,
fixed natural power, or bit length. -/

namespace EditApproximation

private theorem queryGatherPolynomial_eval (M N P F exponent eM eF B S t W : ℕ) :
    queryGatherPolynomial.eval (queryGatherEnvironment M N P F exponent eM eF B S t W) =
      BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W := by
  rfl

theorem queryLocalProgramBitBudget_fixedPower (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 2 ≤ X) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (he : exponent ≤ X)
    (heM : eM ≤ X) (heF : eF ≤ X) (hB : B ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hTheta : 2 ^ exponent ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hGroups : BinaryFraction.preparedLocalGroupsBitBudget N M P F exponent eM eF B ≤ X)
    (hOnline : BinaryFraction.preparedLocalOnlineBitBudget M P B S ≤ X)
    (hFinish : BinaryFraction.physicalContinuationBitBudget M P ((B + 1) * (64 * F * P + 2) ^ 2)
      ((B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2) (B + 1) (B + 4) ≤ X)
    (hRange : BinaryFraction.representativeCompleteBitBudget M ((40 * P + 2) ^ (2 * M))
      (4 * (B + 1) + 20) ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤ X ^ queryGatherBitDegree := by
  have henv : ∀ i, queryGatherEnvironment M N P F exponent eM eF B S t W i ≤ X := by
    intro i
    fin_cases i
    · exact hM
    · exact hP
    · exact hF
    · exact he
    · exact heM
    · exact heF
    · exact hB
    · exact ht
    · exact hW
    · exact hTheta
    · exact hV
    · exact hCart
    · exact hGroups
    · exact hOnline
    · exact hFinish
    · exact hRange
  simpa only [queryGatherPolynomial_eval, queryGatherBitDegree] using
    queryGatherPolynomial.eval_le_pow (queryGatherEnvironment M N P F exponent eM eF B S t W) X hX henv

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Queries_QueryProgramPolynomial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation

attribute [local irreducible] preparedLocalGroupBitDegree onlineShellDegree physicalShellDegree
  representativeCompleteBitDegree queryGatherBitDegree

theorem queryLocalProgramBitBudget_shell_cap (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 2 ≤ X) (hN : Nat.size N ≤ B) (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X)
    (he : exponent ≤ X) (hTheta : 2 ^ exponent ≤ X) (hword : 16 * B + 200 ≤ X)
    (hscales : 7 + eM + eF ≤ X) (hS : S ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X)
    (hrep : (B + 1) * (64 * F * P + 2) ^ 2 ≤ X)
    (hgroup : (B + 1) * ((32 * F + 2) * 2 ^ exponent + 2) ^ 2 ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤
      X ^ queryLocalProgramBitDegree := by
  have hp : 0 < X := by omega
  have hD : 1 ≤ queryPrimitiveBitDegree := Nat.le_max_left _ _
  have hbase : X ≤ X ^ queryPrimitiveBitDegree := Nat.le_pow hD
  have hY : 2 ≤ X ^ queryPrimitiveBitDegree := hX.trans hbase
  have hB : B ≤ X := by omega
  have hg := preparedLocalGroupsBitBudget_fixedPower N M P F exponent eM eF B X
    hX hN hM hP hF he hTheta hword hscales hV hCart
  have ho := preparedLocalOnlineBitBudget_fixedPower M P B X hX hM hB hV
  have hos : BinaryFraction.preparedLocalOnlineBitBudget M P B S ≤
      BinaryFraction.preparedLocalOnlineBitBudget M P B X := by
    unfold BinaryFraction.preparedLocalOnlineBitBudget BinaryFraction.preparedLocalOnlineScaleBitBudget
      BinaryFraction.preparedOnlineBitBudget
    dsimp only
    gcongr
  have hf := physicalContinuationBitBudget_fixedPower M P _ _ (B + 1) (B + 4) X
    hX hM hP hrep hgroup (by omega) (by omega) hV hCart
  have hr := representativeCompleteBitBudget_fixedPower M ((40 * P + 2) ^ (2 * M))
    (4 * (B + 1) + 20) X hX hM hV (by omega)
  have hgd : preparedLocalGroupBitDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hod : onlineShellDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hfd : physicalShellDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have hrd : representativeCompleteBitDegree ≤ queryPrimitiveBitDegree := by
    unfold queryPrimitiveBitDegree; omega
  have h := queryLocalProgramBitBudget_fixedPower M N P F exponent eM eF B S t W
    (X ^ queryPrimitiveBitDegree) hY (hM.trans hbase) (hP.trans hbase) (hF.trans hbase)
    (he.trans hbase) ((by omega : eM ≤ X).trans hbase) ((by omega : eF ≤ X).trans hbase)
    (hB.trans hbase) (ht.trans hbase) (hW.trans hbase) (hTheta.trans hbase)
    (hV.trans hbase) (hCart.trans hbase)
    (hg.trans (Nat.pow_le_pow_right hp hgd))
    (hos.trans (ho.trans (Nat.pow_le_pow_right hp hod)))
    (hf.trans (Nat.pow_le_pow_right hp hfd))
    (hr.trans (Nat.pow_le_pow_right hp hrd))
  simpa only [← pow_mul, queryLocalProgramBitDegree] using h

/-- A uniform cap absorbs the finite counts before applying the cost polynomial. -/
theorem queryLocalProgramBitBudget_uniform_cap (M N P F exponent eM eF B S t W X : ℕ)
    (hX : 64 ≤ X) (hN : Nat.size N ≤ B)
    (hM : M ≤ X) (hP : P ≤ X) (hF : F ≤ X) (he : exponent ≤ X)
    (heM : eM ≤ X) (heF : eF ≤ X) (hB : B ≤ X) (hS : S ≤ X) (ht : t ≤ X) (hW : W ≤ X)
    (hTheta : 2 ^ exponent ≤ X) (hV : (40 * P + 2) ^ (2 * M) ≤ X)
    (hCart : ((40 * P + 2) ^ 2 + 1) ^ (M + 1) ≤ X) :
    BinaryFraction.queryLocalProgramBitBudget M N P F exponent eM eF B S t W ≤
      X ^ (16 * queryLocalProgramBitDegree) := by
  have hp : 0 < X := by omega
  have hunit : 1 ≤ X := by omega
  have hXX : X ≤ X ^ 16 := Nat.le_pow (by decide)
  have hx2 : X + 1 ≤ X ^ 2 := by nlinarith only [hX]
  have hword : 16 * B + 200 ≤ X ^ 16 := by
    calc
      _ ≤ 216 * X := by omega
      _ ≤ X ^ 2 * X := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = X ^ 3 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have hscales : 7 + eM + eF ≤ X ^ 16 := by
    calc
      _ ≤ 9 * X := by omega
      _ ≤ X ^ 2 := by nlinarith only [hX]
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have hrepSide : 64 * F * P + 2 ≤ X ^ 4 := by
    have hfp := Nat.mul_le_mul hF hP
    calc
      _ ≤ 66 * X ^ 2 := by nlinarith only [hfp, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = _ := by ring
  have hgroupSide : (32 * F + 2) * 2 ^ exponent + 2 ≤ X ^ 4 := by
    have hft := Nat.mul_le_mul (show 32 * F + 2 ≤ 34 * X by omega) hTheta
    calc
      _ ≤ 36 * X ^ 2 := by nlinarith only [hft, hX]
      _ ≤ X ^ 2 * X ^ 2 := Nat.mul_le_mul_right _ (by nlinarith only [hX])
      _ = _ := by ring
  have hcounts (side : ℕ) (hs : side ≤ X ^ 4) : (B + 1) * side ^ 2 ≤ X ^ 16 := by
    calc
      _ ≤ X ^ 2 * (X ^ 4) ^ 2 := Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hs 2)
      _ = X ^ 10 := by ring
      _ ≤ _ := Nat.pow_le_pow_right hp (by decide)
  have h := queryLocalProgramBitBudget_shell_cap M N P F exponent eM eF B S t W (X ^ 16)
    ((by omega : 2 ≤ X).trans hXX) hN (hM.trans hXX) (hP.trans hXX) (hF.trans hXX)
    (he.trans hXX) (hTheta.trans hXX) hword hscales (hS.trans hXX) (ht.trans hXX) (hW.trans hXX)
    (hV.trans hXX) (hCart.trans hXX) (hcounts _ hrepSide) (hcounts _ hgroupSide)
  simpa only [← pow_mul] using h

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedParameterRegisters
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability _root_.OAI.EditApproximation.finalProgramDrawLaw_probability _root_.OAI.EditApproximation.localCommonDrawLaw_probability _root_.OAI.EditApproximation.localCommonFinalLaw_probability _root_.OAI.EditApproximation.localCommonTerminalLaw_probability _root_.OAI.EditApproximation.localCommonTraceLaw_probability _root_.OAI.EditApproximation.localCommonTraceSingleton _root_.OAI.EditApproximation.localFinalProgramDrawLaw_probability _root_.OAI.EditApproximation.localFinalProgramLaw_probability _root_.OAI.EditApproximation.localScheduledSeedDrawLaw_probability _root_.OAI.EditApproximation.localScheduledTrace_measurableSingleton _root_.OAI.EditApproximation.physicalFamilyRuntimeLaw_probability _root_.OAI.EditApproximation.physicalUniformLaw_probability _root_.OAI.EditApproximation.physicalUniformOutcome_measurableSingleton _root_.OAI.EditApproximation.scheduledSeedDrawLaw_probability
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
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryProgramWork
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
attribute [-simp] _root_.OAI.EditApproximation.BinaryFraction.queryInitialConeCentersWithWork_value _root_.OAI.EditApproximation.BinaryFraction.queryMeanWithWork_value _root_.OAI.EditApproximation.BinaryFraction.querySeedMedianWithWork_value _root_.OAI.EditApproximation.BinaryFraction.refinementDecrementWithWork_value _root_.OAI.EditApproximation.BinaryFraction.seedMedianWithWork_value _root_.OAI.EditApproximation.BitQuery.Heap.footprint_collect _root_.OAI.EditApproximation.BitQuery.Heap.footprint_normalize _root_.OAI.EditApproximation.BitQuery.Heap.footprint_read _root_.OAI.EditApproximation.BitQuery.Heap.footprint_runCells _root_.OAI.EditApproximation.queryBandGatherHeap_footprint _root_.OAI.EditApproximation.queryChargedReadHeap_footprint _root_.OAI.EditApproximation.queryGroupSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryInitialConeProgramAtHeap_footprint _root_.OAI.EditApproximation.queryInitialGatherHeap_footprint _root_.OAI.EditApproximation.queryLocalBandHeap_footprint _root_.OAI.EditApproximation.queryLocalProgramHeap_footprint _root_.OAI.EditApproximation.queryLocalRandomSourcesHeap_footprint _root_.OAI.EditApproximation.queryLocalRefinementHeap_footprint _root_.OAI.EditApproximation.queryMeanReadHeap_footprint _root_.OAI.EditApproximation.queryOnlineSourceGatherHeap_footprint _root_.OAI.EditApproximation.queryPhysicalScalarReadHeap_footprint _root_.OAI.EditApproximation.queryPhysicalTableReadHeap_footprint _root_.OAI.EditApproximation.queryRestrictedPhysicalOracle_source _root_.OAI.EditApproximation.querySliceHeadWithWork_value _root_.OAI.EditApproximation.queryWarmupProgramHeap_footprint
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryProgramBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ t W : ℕ, t ≤ inputHeight N ^ 2 →
      W ≤ computedLocalKernelBudget K N →
      BinaryFraction.queryLocalProgramBitBudget (integerParameters N).M N (integerParameters N).P
        (inputSmallLog N) (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N)
        (inputHeight N ^ 8)
        (inputHeight N ^ ((100 * (integerParameters N).M + 100000) *
          (coarseExponent (inputSmallLog N) + 1))) t W ≤
        computedLocalKernelBudget (computedQueryProgramDegree K) N := by
  filter_upwards [computedPreparedNumericBounds,
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hn hell
  intro t W ht hW
  let H := inputHeight N
  let M := (integerParameters N).M
  let P := (integerParameters N).P
  let p := coarseExponent (inputSmallLog N)
  let L := (100 * M + 100000) * (p + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 40 ≤ L := by
    dsimp only [L]
    nlinarith only [Nat.zero_le M, Nat.zero_le p, Nat.zero_le (M * p)]
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have hX : 64 ≤ X := hH.trans (hHS.trans hSX)
  have hz : BinaryFraction.zero.width ≤ H ^ 8 := by
    change 1 ≤ H ^ 8
    exact one_le_pow₀ (by omega)
  have hzv : BinaryFraction.zero.value = 0 := by
    norm_num [BinaryFraction.value, BinaryFraction.zero, SignedBinary.value, signedMagnitude, bitWordValue]
  have hnum := hn 0 0 (by omega) t ht BinaryFraction.zero BinaryFraction.zero
    BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero hz hz hz hz hz
    (by rw [hzv]; simp)
    (by rw [hzv]; norm_num)
    (fun _ _ => 0) (by intro b r; simp)
  change BinaryFraction.PreparedKernelNumericBounds (nx := 0) (ny := 0) (M := M)
    N P (inputSmallLog N) (40 * smallLogExponent N) H (inputSmallLog N ^ 80)
    (heightExponent N / 20) (smallLogExponent N) (H ^ 8) (H ^ 5) S t
    BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero BinaryFraction.zero
    (fun _ _ => 0) at hnum
  have hB : H ^ 8 ≤ S := by have := hnum.wordCap; omega
  have he : 40 * smallLogExponent N ≤ S := by
    have := hnum.thetaSize
    omega
  have heM : heightExponent N / 20 ≤ S := by have := hnum.scaleSizes; omega
  have heF : smallLogExponent N ≤ S := by have := hnum.scaleSizes; omega
  have hTheta : 2 ^ (40 * smallLogExponent N) ≤ S := by
    calc
      _ = inputSmallLog N ^ 40 := by unfold inputSmallLog; rw [← pow_mul]; congr 1; omega
      _ ≤ H ^ 40 := Nat.pow_le_pow_left (computed_smallLog_le_height N) 40
      _ ≤ S := Nat.pow_le_pow_right hp hL
  have hWX : W ≤ X := by
    apply hW.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryLocalProgramBitBudget_uniform_cap M N P (inputSmallLog N)
    (40 * smallLogExponent N) (heightExponent N / 20) (smallLogExponent N) (H ^ 8) S t W X
    hX hnum.inputSize (hnum.arityCap.trans hSX) (hnum.precisionCap.trans hSX)
    ((computed_smallLog_le_height N).trans (hHS.trans hSX)) (he.trans hSX) (heM.trans hSX)
    (heF.trans hSX) (hB.trans hSX) hSX (hnum.timeCap.trans hSX) hWX
    (hTheta.trans hSX) (hnum.actionCap.trans hSX) (hnum.cartesianCap.trans hSX)
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ (16 * queryLocalProgramBitDegree) =
    H ^ (L * computedQueryProgramDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

end EditApproximation

end OAI
end

section
-- module Solutions.OAIQ361V3_EA.EditApproximation_Refinement_ComputedQueryReadBudget
attribute [-instance] _root_.OAI.EditApproximation.computedExecutionLaw_probability _root_.OAI.EditApproximation.computedFullLaw_probability _root_.OAI.EditApproximation.computedFullOutcome_measurableSingleton _root_.OAI.EditApproximation.computedPhysicalCoarseLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace EditApproximation
open Filter

theorem computedQueryReadBudget_cap (K : ℕ) :
    ∀ᶠ N : ℕ in atTop, ∀ T J B V C W : ℕ,
      T ≤ inputHeight N ^ 2 → J ≤ inputHeight N → B ≤ inputHeight N ^ 8 →
      V ≤ inputHeight N ^ 3 → C ≤ computedLocalKernelBudget K N → W ≤ computedLocalKernelBudget K N →
      BinaryFraction.queryPhysicalDataBudget T J B V C (BinaryFraction.queryFamilySourceReadBudget J B W) ≤
        computedLocalKernelBudget (computedQueryReadDegree K) N := by
  filter_upwards [inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hell
  intro T J B V C W hT hJ hB hV hC hW
  let H := inputHeight N
  let L := (100 * (integerParameters N).M + 100000) * (coarseExponent (inputSmallLog N) + 1)
  let S := H ^ L
  let X := S ^ (K + 1)
  have hH : 64 ≤ H := hell.trans (computed_smallLog_le_height N)
  have hp : 0 < H := by omega
  have hL : 8 ≤ L := by
    have h := Nat.le_mul_of_pos_right (100 * (integerParameters N).M + 100000)
      (by omega : 0 < coarseExponent (inputSmallLog N) + 1)
    dsimp only [L]
    omega
  have hSX : S ≤ X := Nat.le_pow (by omega)
  have hHS : H ≤ S := Nat.le_pow (by omega)
  have h8S : H ^ 8 ≤ S := Nat.pow_le_pow_right hp hL
  have h2S : H ^ 2 ≤ S := Nat.pow_le_pow_right hp (by omega)
  have h3S : H ^ 3 ≤ S := Nat.pow_le_pow_right hp (by omega)
  have hcX : C ≤ X := by
    apply hC.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have hwX : W ≤ X := by
    apply hW.trans
    change H ^ (L * K) ≤ (H ^ L) ^ (K + 1)
    rw [← pow_mul]
    exact Nat.pow_le_pow_right hp (Nat.mul_le_mul_left L (Nat.le_succ K))
  have h := queryCallbackShell_fixedPower T J B V C W X
    ((by omega : 2 ≤ H).trans (hHS.trans hSX))
    (hT.trans (h2S.trans hSX)) (hJ.trans (hHS.trans hSX)) (hB.trans (h8S.trans hSX))
    (hV.trans (h3S.trans hSX)) hcX hwX
  apply h.trans_eq
  change ((H ^ L) ^ (K + 1)) ^ queryCallbackShellDegree = H ^ (L * computedQueryReadDegree K)
  rw [← pow_mul, ← pow_mul]
  congr 1

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

theorem computedActiveQueryBudget_cap_oai :
    ∀ᶠ N : ℕ in atTop, ∀ J t : ℕ, J ≤ inputHeight N → t ≤ inputHeight N ^ 2 →
      computedActiveQueryBudget N J t ≤ computedLocalKernelBudget computedActiveQueryDegree N := by
  filter_upwards [computedQueryReadBudget_cap 1, computedQueryProgramBudget_cap (computedQueryReadDegree 1),
    inputSmallLog_tendsto.eventually (eventually_ge_atTop 64)] with N hread hprogram hell
  intro J t hJ ht
  have hH : 64 ≤ inputHeight N := hell.trans (computed_smallLog_le_height N)
  have hg := computed_kernel_guard_cost N hH
  have hT : (integerParameters N).T ≤ inputHeight N ^ 2 := by
    have h := computed_history_budget_le_height_sq N (by omega)
    omega
  have hd := hread (integerParameters N).T J (inputHeight N ^ 8) (inputHeight N ^ 3)
    (50 * inputHeight N ^ 8 + 24) (50 * inputHeight N ^ 8 + 25) hT hJ le_rfl le_rfl
    (by omega) (by omega)
  exact hprogram t _ ht hd

end EditApproximation

end OAI
end

theorem solution : type_of% @OAI.EditApproximation.computedActiveQueryBudget_cap_oai := @OAI.EditApproximation.computedActiveQueryBudget_cap_oai
