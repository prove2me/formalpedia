-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:25:52.85559+00:00
-- url     : https://prove2.me/submissions/b60b03b2-185e-41dc-b3ea-5bd5594922ec

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S085
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S099

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ChunkPartition
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.labelFintype _root_.OAI.Algorithms.SubexponentialSAT.FixedParameters.variableFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# An explicit ceiling-based partition into Boolean chunks

For positive `ell`, the number of chunks is `(n + ell - 1) / ell`.
The `i`th chunk contains the consecutive indices starting at `i * ell` and
has size `min ell (n - i * ell)`. Quotient and remainder give an actual
equivalence between the original indices and chunk/offset pairs.
-/

namespace SubexponentialSAT.ChunkPartition

open scoped BigOperators

theorem count_le_iff {n ell d : ℕ} (hell : 0 < ell) :
    count n ell ≤ d ↔ n ≤ d * ell := by
  unfold count
  rw [Nat.div_le_iff_le_mul hell]
  omega

theorem lt_count_iff {n ell i : ℕ} (hell : 0 < ell) :
    i < count n ell ↔ i * ell < n := by
  have h := count_le_iff (n := n) (ell := ell) (d := i) hell
  omega

theorem le_count_mul {n ell : ℕ} (hell : 0 < ell) :
    n ≤ count n ell * ell :=
  (count_le_iff hell).mp le_rfl

@[simp] theorem count_zero {ell : ℕ} (hell : 0 < ell) : count 0 ell = 0 := by
  apply Nat.eq_zero_of_le_zero
  exact (count_le_iff hell).mpr (by simp)

@[simp] theorem count_eq_zero_iff {n ell : ℕ} (hell : 0 < ell) :
    count n ell = 0 ↔ n = 0 := by
  constructor
  · intro h
    have hn := le_count_mul (n := n) hell
    simp [h] at hn
    exact hn
  · rintro rfl
    exact count_zero hell

theorem count_le_div_add_one {n ell : ℕ} (hell : 0 < ell) :
    count n ell ≤ n / ell + 1 := by
  apply (count_le_iff hell).mpr
  have hr := Nat.mod_lt n hell
  have heq := Nat.div_add_mod' n ell
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem count_eq_div_add_ite {n ell : ℕ} (hell : 0 < ell) :
    count n ell = n / ell + if n % ell = 0 then 0 else 1 := by
  have hdiv := Nat.div_add_mod' n ell
  by_cases hr : n % ell = 0
  · simp only [hr, ite_true, if_true, Nat.add_zero]
    apply Nat.le_antisymm
    · apply (count_le_iff hell).mpr
      omega
    · have h := Nat.div_le_div_right (c := ell) (le_count_mul (n := n) hell)
      simpa only [Nat.mul_div_cancel _ hell] using h
  · simp only [hr, ite_false]
    apply Nat.le_antisymm (count_le_div_add_one hell)
    have hlt : n / ell < count n ell := (lt_count_iff hell).mpr (by omega)
    omega

end SubexponentialSAT.ChunkPartition

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CeilingDivisionPrograms
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Ceiling division by fixed finite bit programs

The rounding suffix tests the actual remainder word and increments the actual
quotient word precisely when that remainder is nonzero. Natural division is
used only in the semantic statement of the full routine.
-/

namespace SubexponentialSAT.CeilingDivisionPrograms

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.CounterPrograms

theorem round_eval (d : Data) (hs : d.stacks 1 = []) :
    ∃ n e, StructuredCalls.Eval roundCmd n d e ∧ RoundOutput d e ∧ n ≤ roundBound d := by
  let z := CounterForPrograms.zeroResult remainderPorts d
  have hz : StructuredCalls.Eval (CounterForPrograms.zeroCmd remainderPorts)
      (8 * (d.stacks 0).length + 6) d z := CounterForPrograms.zero_eval remainderPorts d hs
  have hzstacks : z.stacks = d.stacks :=
    CounterForPrograms.install_stacks_self remainderPorts d _ _ _ hs
  have hzscratch : z.stacks 1 = [] := by rw [hzstacks]; exact hs
  have hzflag : z.regs 2 = isZero (d.stacks 0) :=
    CounterForPrograms.install_register remainderPorts d _ _ _ _ _ 2
  by_cases hv : value (d.stacks 0) = 0
  · have hf : z.regs 2 = true := hzflag.trans ((isZero_eq_true_iff _).mpr hv)
    refine ⟨(8 * (d.stacks 0).length + 6) + (0 + 1), z,
      .seq hz (.ite_true hf (.base (.skip z))), ?_, ?_⟩
    · constructor
      · simp only [hv, ite_eq_left, hzstacks]
      · intro j _; exact congrFun hzstacks j
    · dsimp [roundBound]; omega
  · have hf : z.regs 2 = false :=
      hzflag.trans ((isZero_eq_false_iff _).mpr (by omega))
    refine ⟨(8 * (d.stacks 0).length + 6) +
        ((rippleCost true (z.stacks 7) + 1) + 1), incrementResult quotientPorts z,
      .seq hz (.ite_false hf (increment_eval quotientPorts z hzscratch)), ?_, ?_⟩
    · constructor
      · simpa only [quotientPorts, hv, ite_false, hzstacks] using
          increment_counter quotientPorts z
      · intro j hj
        exact (increment_other quotientPorts z hzscratch j hj).trans (congrFun hzstacks j)
    · have hb := rippleCost_le true (z.stacks 7)
      rw [hzstacks] at hb ⊢
      dsimp [roundBound]
      omega

theorem round_value (d e : Data) (h : RoundOutput d e) :
    value (e.stacks 7) = value (d.stacks 7) + if value (d.stacks 0) = 0 then 0 else 1 := by
  rw [h.1]
  by_cases hz : value (d.stacks 0) = 0 <;> simp [hz, value_increment]

theorem round_length (d e : Data) (h : RoundOutput d e) :
    (e.stacks 7).length ≤ (d.stacks 7).length + 1 := by
  rw [h.1]
  split_ifs
  · omega
  · exact ripple_length_le true _

end SubexponentialSAT.CeilingDivisionPrograms

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCeilingProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# The actual binary program for the packed dimension

Binary long division yields quotient and remainder. A finite zero test and
conditional increment then produce the ceiling. The input-dependent values are
stack words throughout; the control table is fixed.
-/

namespace SubexponentialSAT.SubexpCeilingProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredProgram SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.ModularQuotientArithmetic

theorem runtimeBound_le (modulus input : List Bool) {L : ℕ}
    (hm : modulus.length ≤ L) (hx : input.length ≤ L) :
    runtimeBound modulus input ≤ 500 * (L + 1) ^ 2 := by
  have hs : modulus.length + input.length + 1 ≤ 2 * L + 1 := by omega
  have hp := Nat.pow_le_pow_left hs 2
  dsimp [runtimeBound]
  nlinarith

theorem command_eval (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ n d, StructuredCalls.Eval command n (inputState regs modulus input) d ∧
      Output modulus input d ∧ n + 1 ≤ runtimeBound modulus input := by
  obtain ⟨rf, n₁, hn₁, ht⟩ := ModularQuotientPrograms.quotient_correct regs modulus input
  let mid := state rf (divide modulus input).2 modulus [] (divide modulus input).1
  have hfirst : StructuredCalls.Eval (.call ModularQuotientPrograms.quotientProgram) n₁
      (inputState regs modulus input) mid := .call _ ht
  obtain ⟨n₂, d, hround, hout, hn₂⟩ := CeilingDivisionPrograms.round_eval mid rfl
  have hl₀ : (mid.stacks 0).length = modulus.length + input.length :=
    divide_remainder_length modulus input
  have hl₇ : (mid.stacks 7).length = input.length :=
    divide_quotient_length modulus input
  refine ⟨n₁ + n₂, d, .seq hfirst hround, ?_, ?_⟩
  · refine ⟨?_, ?_, hout.2⟩
    · have hv : BinaryArithmetic.toNat (d.stacks 7) = BinaryArithmetic.toNat (divide modulus input).1 +
          if BinaryArithmetic.toNat (divide modulus input).2 = 0 then 0 else 1 := by
        simpa [mid, state, CounterPrograms.value_eq_toNat] using
          CeilingDivisionPrograms.round_value mid d hout
      rw [divide_quotient_correct modulus input hm,
        divide_remainder_correct modulus input hm] at hv
      rw [ChunkPartition.count_eq_div_add_ite hm]
      exact hv
    · simpa only [hl₇] using CeilingDivisionPrograms.round_length mid d hout
  · have hb : n₂ ≤ 8 * ((modulus.length + input.length) + input.length) + 15 := by
      simpa only [CeilingDivisionPrograms.roundBound, hl₀, hl₇] using hn₂
    dsimp [runtimeBound]
    omega

theorem run_output (regs : Regs) (modulus input : List Bool)
    (hm : 0 < BinaryArithmetic.toNat modulus) :
    ∃ d, Output modulus input d ∧
      BitProgram.RunsIn program (runtimeBound modulus input)
        ((inputState regs modulus input).withPC (some program.entry)) (d.withPC none) := by
  obtain ⟨n, d, he, hout, hn⟩ := command_eval regs modulus input hm
  exact ⟨d, hout, n + 1, hn, StructuredCalls.compiled_halt_trace he 6 7⟩

theorem output_modulus (modulus input : List Bool) (d : Data) (h : Output modulus input d) :
    d.stacks 5 = modulus := h.2.2 5 (by decide)

end SubexponentialSAT.SubexpCeilingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramCutoff
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual runtime multiplication and ceiling division for the high-incidence
integer threshold. Inputs are binary S,t,n; the output is binary ceil(S*t/n).
Counting S from scope records and converting the result to unary are separate
physical frontend obligations, not operations hidden in this specification. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem ceilingPorts_injective : Function.Injective ceilingPorts := by decide

theorem command_eval (regs : Fin 8 → Bool) (mass scale dimension : List Bool)
    (hn : 0 < BinaryArithmetic.toNat dimension) :
    ∃ time b, Eval command time (state regs mass scale dimension) b ∧
      time + 1 ≤ bound mass scale dimension ∧
      BinaryArithmetic.toNat (b.stacks 5) = (BinaryArithmetic.toNat mass * BinaryArithmetic.toNat scale) ⌈/⌉ BinaryArithmetic.toNat dimension ∧
      (b.stacks 5).length ≤ mass.length + scale.length + 2 ∧
      b.stacks 0 = mass ∧ b.stacks 1 = scale ∧ b.stacks 2 = dimension := by
  let a := state regs mass scale dimension
  have ha : ArithmeticCalls.Valid ports a := by
    constructor
    · rfl
    · intro i; fin_cases i <;> rfl
  obtain ⟨tm, rm, product, hm, hp, hl, ht⟩ := ArithmeticCalls.multiplyAt_eval ports a ha
  let mid : Data := ⟨rm, Function.update a.stacks 3 product⟩
  have hp' : BinaryArithmetic.toNat product = BinaryArithmetic.toNat mass * BinaryArithmetic.toNat scale := hp
  have hl' : product.length ≤ mass.length + scale.length + 1 := hl
  have ht' : tm ≤ 100 * (mass.length + scale.length + 1)^2 := ht
  have hproject : projectState id ceilingPorts mid =
      SubexpCeilingProgram.inputState rm dimension product := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨localResult, hout, tc, htc, hc⟩ := SubexpCeilingProgram.run_output rm dimension product hn
  rw [← hproject] at hc
  let b := embedState id ceilingPorts mid localResult
  have he := eval_call_from_state SubexpCeilingProgram.program id ceilingPorts mid
    Function.injective_id ceilingPorts_injective hc
  have hs (i : Fin 8) : b.stacks (ceilingPorts i) = localResult.stacks i :=
    embedState_stack _ _ _ _ ceilingPorts_injective i
  refine ⟨tm + tc, b, hm.seq he, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hcBound := SubexpCeilingProgram.runtimeBound_le dimension product
      (L := mass.length + scale.length + dimension.length + 1) (by omega) (by omega)
    have hcBound' : SubexpCeilingProgram.runtimeBound dimension product ≤
        500 * (mass.length + scale.length + dimension.length + 2)^2 := by
      simpa [Nat.add_assoc] using hcBound
    dsimp [bound]
    omega
  · rw [show b.stacks 5 = localResult.stacks 7 from hs 7, hout.1, hp']
    rfl
  · rw [show b.stacks 5 = localResult.stacks 7 from hs 7]
    exact hout.2.1.trans (by omega)
  · change (embedState id ceilingPorts mid localResult).stacks 0 = mass
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    rfl
  · change (embedState id ceilingPorts mid localResult).stacks 1 = scale
    rw [embedState_stack_frame _ _ _ _ _ (by decide)]
    rfl
  · exact (hs 5).trans (SubexpCeilingProgram.output_modulus dimension product localResult hout)

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Cutoff

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramPrepareOps
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed ports for the physical high-incidence prefix. Each operation below
is a genuine call to an already verified finite program. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem reg8_inj : Function.Injective reg8 := Fin.castAdd_injective _ _
theorem cutoffPorts_inj : Function.Injective cutoffPorts := by decide

theorem cutoff_eval_oai (d : Data) (hn : 0 < BinaryArithmetic.toNat (d.stacks 16))
    (hwork : ∀ i : Fin 12, i ≠ 0 → i ≠ 1 → i ≠ 2 → d.stacks (cutoffPorts i) = []) :
    ∃ time b, Eval cutoffCall time d b ∧
      time ≤ Cutoff.bound (d.stacks 19) (d.stacks 17) (d.stacks 16) ∧
      BinaryArithmetic.toNat (b.stacks 20) = (BinaryArithmetic.toNat (d.stacks 19) * BinaryArithmetic.toNat (d.stacks 17)) ⌈/⌉ BinaryArithmetic.toNat (d.stacks 16) ∧
      (b.stacks 20).length ≤ (d.stacks 19).length + (d.stacks 17).length + 2 ∧
      (∀ i : Fin 32, i.val < 16 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨
        i = 21 ∨ i = 22 ∨ i = 23 → b.stacks i = d.stacks i) := by
  let a := projectState reg8 cutoffPorts d
  have ha : a = Cutoff.state a.regs (d.stacks 19) (d.stacks 17) (d.stacks 16) := by
    apply congrArg (StructuredProgram.State.mk a.regs)
    funext i
    fin_cases i <;> first | rfl | exact hwork _ (by decide) (by decide) (by decide)
  obtain ⟨time, out, he, ht, hv, hl, h0, h1, h2⟩ :=
    Cutoff.command_eval a.regs (d.stacks 19) (d.stacks 17) (d.stacks 16) hn
  rw [← ha] at he
  let b := embedState reg8 cutoffPorts d out
  have hb := eval_liftCommand_from_state Cutoff.command 0 5 reg8 cutoffPorts d
    reg8_inj cutoffPorts_inj he
  have hs (i : Fin 12) : b.stacks (cutoffPorts i) = out.stacks i :=
    embedState_stack _ _ _ _ cutoffPorts_inj i
  refine ⟨time + 1, b, hb, ht, (congrArg BinaryArithmetic.toNat (hs 5)).trans hv, ?_, ?_⟩
  · change (b.stacks (cutoffPorts 5)).length ≤
      (d.stacks 19).length + (d.stacks 17).length + 2
    rw [hs 5]
    exact hl
  · intro i hi
    by_cases h16 : i = 16
    · subst i; exact (hs 2).trans h2
    by_cases h17 : i = 17
    · subst i; exact (hs 1).trans h1
    by_cases h19 : i = 19
    · subst i; exact (hs 0).trans h0
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    have h16' : i.val ≠ 16 := fun h => h16 (Fin.ext h)
    have h17' : i.val ≠ 17 := fun h => h17 (Fin.ext h)
    have h19' : i.val ≠ 19 := fun h => h19 (Fin.ext h)
    have hi' : i.val < 16 ∨ i.val = 16 ∨ i.val = 17 ∨ i.val = 18 ∨ i.val = 19 ∨
        i.val = 21 ∨ i.val = 22 ∨ i.val = 23 := by simpa [Fin.ext_iff] using hi
    fin_cases j <;> norm_num [cutoffPorts] at hjv <;> omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Prepare.cutoff_eval_oai
