-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:20:44.673446+00:00
-- url     : https://prove2.me/submissions/5b44f33e-e8f3-43de-a9c8-7ce5a35e6915

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S084
import Definitions.Def_OAIQ081S089

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native unary-to-binary conversion for each statistics output. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem command_eval (r : Fin 3 → Bool) (input : List Bool) :
    ∃ n output, n ≤ input.length*(8*input.length+10)+4 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      Eval command n (state r input []) (state (fun _ => false) [] output) := by
  obtain ⟨output,hv,hl,n,hn,ht⟩ := CounterPrograms.length_correct_from (r 0) (r 1) input
  have hregs : Function.update r 2 false = CounterPrograms.counterRegs (r 0) (r 1) false := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  have hreset : Eval (.base (.atom (.set (2 : Fin 3) false))) 1 (state r input [])
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input []) := by
    have h := Eval.base (StructuredProgram.Eval.atom (.set (2 : Fin 3) false) (state r input []))
    simpa [state,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hregs] using h
  have hc : Eval (.call CounterPrograms.lengthProgram) n
      (state (CounterPrograms.counterRegs (r 0) (r 1) false) input [])
      (state (fun _ => false) [] output) := by
    apply Eval.call
    convert ht using 1
    · simp [state,CounterPrograms.lengthCfg,
        StructuredProgram.State.withPC]
    · simp [state,SubexponentialSAT.BitProgram.terminal
        ]
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
  refine ⟨1+n,output,by omega,(CounterPrograms.value_eq_toNat output).symm.trans hv,hl,hreset.seq hc⟩

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countRegisters_injective : Function.Injective countRegisters := Fin.castAdd_injective _ _
theorem countStacks_injective : Function.Injective countStacks := by decide

theorem count_eval (d : ArithData) (h3 : d.stacks 3 = [])
    (h12 : d.stacks 12 = []) (h13 : d.stacks 13 = []) :
    ∃ t ≤ (d.stacks 2).length * (8 * (d.stacks 2).length + 10) +
      7 * (d.stacks 2).length + 10, ∃ rf word,
      Eval count t d ⟨rf, Function.update d.stacks 3 word⟩ ∧
      BinaryArithmetic.toNat word = (d.stacks 2).length ∧
      word.length ≤ (d.stacks 2).length := by
  let a := ArithmeticCalls.afterCopy 2 13 d
  have ha := ArithmeticCalls.copyAt_eval 2 13 12 d
    (by decide) (by decide) (by decide) h13 h12
  obtain ⟨n, word, hn, hv, hl, he⟩ := LeafStatisticsProgram.Binary.command_eval
    (fun i => a.regs (countRegisters i)) (d.stacks 2)
  have hp : projectState countRegisters countStacks a =
      LeafStatisticsProgram.Binary.state (fun i => a.regs (countRegisters i)) (d.stacks 2) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;>
        simp [ countStacks, a, ArithmeticCalls.afterCopy, CounterPrograms.lengthStacks, h3, h12]
  rw [← hp] at he
  let b := LeafStatisticsProgram.Binary.state (fun _ => false) [] word
  let e := embedState countRegisters countStacks a b
  have hb : e = (⟨e.regs, Function.update d.stacks 3 word⟩ : ArithData) := by
    apply embedState_eq_of_ports countRegisters countStacks a _ b
      countRegisters_injective countStacks_injective
    · intro i; exact embedState_register countRegisters countStacks a b countRegisters_injective i
    · intro i hi; exact embedState_register_frame countRegisters countStacks a b i hi
    · intro i; fin_cases i <;>
        simp [b, countStacks, LeafStatisticsProgram.Binary.state,
          CounterPrograms.lengthStacks, h12, h13]
    · intro i hi
      have hi3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
      have hi13 : i ≠ 13 := fun h => hi ⟨0, h.symm⟩
      simp [a, ArithmeticCalls.afterCopy, hi3, hi13]
  have hrun := eval_liftCommand_from_state LeafStatisticsProgram.Binary.command 0 1
    countRegisters countStacks a countRegisters_injective countStacks_injective he
  change Eval _ (n+1) a e at hrun
  rw [hb] at hrun
  exact ⟨(7 * (d.stacks 2).length + 5) + (n+1), by omega,
    e.regs, word, ha.seq hrun, hv, hl⟩

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

theorem arithmetic_eval (d : ArithData) (hd : ready d) :
    ∃ t ≤ 600 * (2 * inputLength d + 4)^2, ∃ e : ArithData,
      Eval arithmetic t d e ∧
      BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
      (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * inputLength d + 4) ∧
      (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j) := by
  have hwork (i : Fin 5) : 3 ≤ (work i).val := by
    change 3 ≤ i.val + 8
    omega
  obtain ⟨tc, htc, rc, wc, hec, hvc, hlc⟩ := count_eval d
    (hd 3 (by decide)) (hd 12 (by decide)) (hd 13 (by decide))
  let a : ArithData := ⟨rc, Function.update d.stacks 3 wc⟩
  have hv0 : Valid (ports 0) a := by
    constructor
    · simpa [a, ports] using hd 4 (by decide)
    · intro i
      have hi : work i ≠ 3 := by
        intro h
        have hval : i.val + 8 = 3 := congrArg Fin.val h
        omega
      simpa [a, ports, hi] using hd (work i) (hwork i)
  obtain ⟨t0, r0, w0, he0, hv0', hl0, ht0⟩ := multiplyAt_eval (ports 0) a hv0
  let b : ArithData := ⟨r0, Function.update a.stacks 4 w0⟩
  have hv1 : Valid (ports 1) b := by
    constructor
    · simpa [b, a, ports] using hd 5 (by decide)
    · intro i
      have hi : work i ≠ 4 := (ports 0).work_ne_out i
      simpa [b, ports, hi] using hv0.2 i
  obtain ⟨t1, r1, w1, he1, hv1', hl1, ht1⟩ := multiplyAt_eval (ports 1) b hv1
  let c : ArithData := ⟨r1, Function.update b.stacks 5 w1⟩
  let c' := Subexp.TupleProgram.pushedState 5 0 false c
  have heS := Subexp.TupleProgram.pushConst_eval 5 0 false c
  have hv2 : Valid (ports 2) c' := by
    constructor
    · simpa [c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hd 6 (by decide)
    · intro i
      have hi : work i ≠ 5 := (ports 1).work_ne_out i
      simpa [c', Subexp.TupleProgram.pushedState, c, ports, hi] using hv1.2 i
  obtain ⟨t2, r2, w2, he2, hv2', hl2, ht2⟩ := addAt_eval (ports 2) c' hv2
  let f : ArithData := ⟨r2, Function.update c'.stacks 6 w2⟩
  have hv3 : Valid (ports 3) f := by
    constructor
    · simpa [f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hd 7 (by decide)
    · intro i
      have hi : work i ≠ 6 := (ports 2).work_ne_out i
      simpa [f, ports, hi] using hv2.2 i
  obtain ⟨t3, r3, w3, he3, hv3', hl3, ht3⟩ := addAt_eval (ports 3) f hv3
  let e : ArithData := ⟨r3, Function.update f.stacks 7 w3⟩
  have hl0' : w0.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := by
    simpa [a, ports] using hl0
  have hl1' : w1.length ≤ (d.stacks 0).length + wc.length + 1 := by
    simpa [b, a, ports] using hl1
  have hl2' : w2.length ≤ (d.stacks 1).length + w1.length + 2 := by
    simpa [c', Subexp.TupleProgram.pushedState, c, b, a, ports, Nat.add_assoc] using hl2
  have hl3' : w3.length ≤ w0.length + (d.stacks 1).length + 1 := by
    simpa [f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hl3
  have hlen : (d.stacks 2).length ≤ inputLength d := by unfold inputLength; omega
  have htc' : tc ≤ 100 * (2 * inputLength d + 4)^2 := by
    have hm := Nat.mul_le_mul hlen
      (show 8 * (d.stacks 2).length + 10 ≤ 8 * inputLength d + 10 by omega)
    have hs := Nat.mul_le_mul_left 7 hlen
    nlinarith only [htc, hm, hs]
  have ht0' : t0 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht0.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [a, ports, inputLength]; omega
  have ht1' : t1 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht1.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [b, a, ports, inputLength]; omega
  have ht2' : t2 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht2.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [c', c, b, a, ports, inputLength]; omega
  have ht3' : t3 ≤ 100 * (2 * inputLength d + 4)^2 := by
    apply ht3.trans; apply Nat.mul_le_mul_left; apply Nat.pow_le_pow_left
    simp [f, c', c, b, a, ports, inputLength]; omega
  refine ⟨tc + (t0 + (t1 + (2 + (t2+t3)))), ?_, e,
    hec.seq (he0.seq (he1.seq (heS.seq (he2.seq he3)))), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hp : 16 ≤ (2 * inputLength d + 4)^2 :=
      Nat.pow_le_pow_left (show 4 ≤ 2 * inputLength d + 4 by omega) 2
    omega
  · simpa [e, f, c', Subexp.TupleProgram.pushedState, c, b, a] using hvc
  · simpa [e, f, c', Subexp.TupleProgram.pushedState, c, b, a, ports] using hv0'
  · simp [e, f, c', c]
    simp [b, a, ports, hvc] at hv1'
    rw [hv1']; ring
  · simp [e, f]
    simp [c', c, b, a, ports] at hv2'
    simp [b, a, ports, hvc] at hv1'
    rw [hv2', hv1']; ring
  · simp [e]
    simp [f, c', c, b, a, ports] at hv3'
    simp [a, ports] at hv0'
    rw [hv3', hv0']
  · intro j hjlo hjhi
    have hj : j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases hj with rfl | rfl | rfl | rfl | rfl <;>
      simp [e, f, c', c, b, a, inputLength] <;> omega
  · intro j hj
    have h3 : j ≠ 3 := by intro h; have hv : j.val = 3 := congrArg Fin.val h; omega
    have h4 : j ≠ 4 := by intro h; have hv : j.val = 4 := congrArg Fin.val h; omega
    have h5 : j ≠ 5 := by intro h; have hv : j.val = 5 := congrArg Fin.val h; omega
    have h6 : j ≠ 6 := by intro h; have hv : j.val = 6 := congrArg Fin.val h; omega
    have h7 : j ≠ 7 := by intro h; have hv : j.val = 7 := congrArg Fin.val h; omega
    simp [e, f, c', c, b, a, h3, h4, h5, h6, h7]

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeSearchWalshProgramChecks
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeSearchWalshProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lowRegisters_injective : Function.Injective lowRegisters := Fin.castAdd_injective _ _

theorem prepare_eval_oai (d : Data) (hd : ∀ j : Fin 14, 3 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 600 * (2 * size d + 4)^2 + 1, ∃ e : Data,
      Eval prepare t d e ∧
      BinaryArithmetic.toNat (e.stacks 3) = (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 4) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) ∧
      BinaryArithmetic.toNat (e.stacks 5) = 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 6) = BinaryArithmetic.toNat (d.stacks 1) + 2 * BinaryArithmetic.toNat (d.stacks 0) * (d.stacks 2).length ∧
      BinaryArithmetic.toNat (e.stacks 7) = BinaryArithmetic.toNat (d.stacks 0) * BinaryArithmetic.toNat (d.stacks 1) + BinaryArithmetic.toNat (d.stacks 1) ∧
      (∀ j : Fin 14, 3 ≤ j.val → j.val ≤ 7 → (e.stacks j).length ≤ 2 * size d + 4) ∧
      (∀ j : Fin 14, (j.val < 3 ∨ 7 < j.val) → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, b, he, hv3, hv4, hv5, hv6, hv7, hl, hf⟩ :=
    arithmetic_eval (projectState lowRegisters id d) hd
  let e := embedState lowRegisters id d b
  have hs (j : Fin 14) : e.stacks j = b.stacks j :=
    embedState_stack lowRegisters id d b Function.injective_id j
  refine ⟨t+1, Nat.add_le_add_right ht 1, e,
    eval_liftCommand_from_state arithmetic 0 3 lowRegisters id d
      lowRegisters_injective Function.injective_id he, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs]; exact hv3
  · rw [hs]; exact hv4
  · rw [hs]; exact hv5
  · rw [hs]; exact hv6
  · rw [hs]; exact hv7
  · intro j hlo hhi; rw [hs]; exact hl j hlo hhi
  · intro j hj; rw [hs]; exact hf j hj

end SubexponentialSAT.SqrtLog.CodeSearchWalshProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeSearchWalshProgram.prepare_eval_oai
