-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:55:55.302036+00:00
-- url     : https://prove2.me/submissions/cf53c135-892a-4b46-aa0d-26cbd2dc381d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S093
import Definitions.Def_OAIQ081S096
import Definitions.Def_OAIQ081S099
import Definitions.Def_OAIQ081S100
import Definitions.Def_OAIQ081S108

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafStatisticsProgramBinaryFrame
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Relocation and frame contract for converting a computed unary statistic
into a binary output without disturbing the enclosing machine's data. -/
namespace SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem lifted_eval {r s : ℕ} (rr : Fin 3 → Fin r) (ss : Fin 3 → Fin s)
    (hr : Function.Injective rr) (hs : Function.Injective ss)
    (d : State r s) (input : List Bool)
    (hp : projectState rr ss d = state (d.regs ∘ rr) input []) :
    ∃ n output, ∃ b : State r s,
      n ≤ input.length*(8*input.length+10)+5 ∧
      BinaryArithmetic.toNat output = input.length ∧ output.length ≤ input.length ∧
      b.stacks (ss 0) = [] ∧ b.stacks (ss 1) = output ∧ b.stacks (ss 2) = [] ∧
      (∀ i, i ∉ Set.range rr → b.regs i = d.regs i) ∧
      (∀ i, i ∉ Set.range ss → b.stacks i = d.stacks i) ∧
      Eval (.call (ProgramLinking.liftProgram program rr ss)) n d b := by
  obtain ⟨n,output,hn,hv,hl,he⟩ := command_eval (d.regs ∘ rr) input
  let small := state (fun _ => false) [] output
  let b := embedState rr ss d small
  have ht := compiled_halt_trace he 0 1
  rw [←hp] at ht
  have hc := eval_call_from_state program rr ss d hr hs (b := small) ht
  refine ⟨n+1,output,b,by omega,hv,hl,?_,?_,?_,?_,?_,hc⟩
  · exact embedState_stack rr ss d small hs 0
  · exact embedState_stack rr ss d small hs 1
  · exact embedState_stack rr ss d small hs 2
  · exact fun i hi => embedState_register_frame rr ss d small i hi
  · exact fun i hi => embedState_stack_frame rr ss d small i hi

end SubexponentialSAT.SqrtLog.LeafStatisticsProgram.Binary

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpScopeCountSetup
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual preserving scope-record count and assignment-fuel setup.
The scope and base remain on stacks 1 and 0. The program returns unary arity,
binary exponent, and binary base^arity on stacks 2, 3, and 4. -/

namespace SubexponentialSAT.SubexpScopeCountSetup

open BitProgram StructuredCalls

theorem counterReg_injective : Function.Injective counterReg := by
  intro i j h
  exact Fin.ext (congrArg (fun i : Fin 8 => i.val) h)

theorem counterStack_injective : Function.Injective counterStack := by decide

theorem countCall_eval (records : List (List Bool)) (d : Data)
    (hi : d.stacks 14 = Encoding.encodeList id records) (ho : d.stacks 2 = []) :
    ∃ e : Data, Eval countCall (SubexpSunflowerProgram.CountRecords.loopSteps records) d e ∧
      e.stacks = Function.update (Function.update d.stacks 14 []) 2 (List.replicate records.length true) := by
  let a := counterState (d.regs 0) (d.regs 1) (Encoding.encodeList id records) []
  let b := counterState false false [] (List.replicate records.length true)
  have ha : a = projectState counterReg counterStack d := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [ counterStack, ParserProgram.pair, hi, ho]
  have ht := counter_trace records (d.regs 0) (d.regs 1)
  change Trace counterProgram _ (a.withPC _) (b.withPC _) at ht
  rw [ha] at ht
  have he := eval_call_from_state counterProgram counterReg counterStack d
    counterReg_injective counterStack_injective ht
  let e := embedState counterReg counterStack d b
  have hs (i : Fin 2) : e.stacks (counterStack i) = b.stacks i :=
    embedState_stack _ _ _ _ counterStack_injective i
  refine ⟨e, he, ?_⟩
  funext i
  by_cases h14 : i = 14
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 0
  by_cases h2 : i = 2
  · subst i
    simpa [b, counterState, counterStack, ParserProgram.pair] using hs 1
  · rw [embedState_stack_frame counterReg counterStack d b i (by
      rintro ⟨j, hj⟩
      fin_cases j <;> simp [counterStack] at hj <;> simp_all)]
    simp [h14, h2]

theorem count_eval (records : List (List Bool)) (d : Data)
    (hs : d.stacks 1 = Encoding.encodeList id records)
    (h2 : d.stacks 2 = []) (h5 : d.stacks 5 = []) (h14 : d.stacks 14 = []) :
    ∃ rf : Fin 8 → Bool,
      Eval countCommand (countBudget records) d
        ⟨rf, Function.update d.stacks 2 (List.replicate records.length true)⟩ := by
  let a := ArithmeticCalls.afterCopy 1 14 d
  have ha14 : a.stacks 14 = Encoding.encodeList id records := by
    simp [a, ArithmeticCalls.afterCopy, hs]
  have ha2 : a.stacks 2 = [] := by simpa [a, ArithmeticCalls.afterCopy] using h2
  obtain ⟨e, he, hstacks⟩ := countCall_eval records a ha14 ha2
  have heq : e.stacks = Function.update d.stacks 2 (List.replicate records.length true) := by
    rw [hstacks]
    funext i
    by_cases hi2 : i = 2
    · subst i; simp
    by_cases hi14 : i = 14
    · subst i; simp [h14]
    · simp [a, ArithmeticCalls.afterCopy, hi2, hi14]
  have heq' : e = (⟨e.regs, Function.update d.stacks 2 (List.replicate records.length true)⟩ : Data) :=
    congrArg (fun stk => (⟨e.regs, stk⟩ : Data)) heq
  have hcopy := ArithmeticCalls.copyAt_eval (1 : Fin 15) 14 5 d
    (by decide) (by decide) (by decide) h14 h5
  have hrun := hcopy.seq he
  rw [heq'] at hrun
  refine ⟨e.regs, ?_⟩
  simpa only [countCommand, countBudget, hs] using hrun

end SubexponentialSAT.SubexpScopeCountSetup

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramClauseCount
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Count the clauses in the actual emitted leaf. Both the preserving record
scan and unary-to-binary conversion are fixed native programs. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

open SubexponentialSAT BitProgram StructuredCalls

private theorem data_updates (regs oldRegs : Fin 8 → Bool) (formula oldU oldB u b : List Bool) :
    (data regs formula u b).stacks =
      Function.update (Function.update (data oldRegs formula oldU oldB).stacks 2 u) 15 b := by
  funext i; fin_cases i <;> simp [data]

theorem embedded (frameRegs regs : Fin 8 → Bool) (formula unary : List Bool) :
    embedState id (Fin.castAdd 1) (data frameRegs formula [] []) (small regs formula unary) =
      data regs formula unary [] := by
  apply embedState_eq_of_ports id (Fin.castAdd 1) _ _ _ Function.injective_id (Fin.castAdd_injective 15 1)
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i,rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have hlast : i.val = 15 := by
      by_contra h
      have hlt : i.val < 15 := by omega
      exact hi ⟨⟨i.val,hlt⟩,Fin.ext rfl⟩
    have he : i = (15 : Fin 16) := Fin.ext hlast
    subst i
    rfl

theorem count_eval (regs : Fin 8 → Bool) (records : List (List Bool)) :
    ∃ rr, Eval count (SubexpScopeCountSetup.countBudget records+1)
      (data regs (Encoding.encodeList id records) [] [])
      (data rr (Encoding.encodeList id records) (List.replicate records.length true) []) := by
  obtain ⟨rr,he⟩ := SubexpScopeCountSetup.count_eval records
    (small regs (Encoding.encodeList id records) []) rfl rfl rfl rfl
  have hh : (⟨rr,Function.update (small regs (Encoding.encodeList id records) []).stacks
      2 (List.replicate records.length true)⟩ : State 8 15) =
      small rr (Encoding.encodeList id records) (List.replicate records.length true) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hh] at he
  have ht := eval_call_lifted (compiled SubexpScopeCountSetup.countCommand 1 2)
    id (Fin.castAdd 1) (data regs (Encoding.encodeList id records) [] [])
    Function.injective_id (Fin.castAdd_injective 15 1) (compiled_halt_trace he 1 2)
  rw [embedded,embedded] at ht
  exact ⟨rr,ht⟩

theorem command_eval (regs : Fin 8 → Bool) (records : List (List Bool)) :
    ∃ k word rr, k ≤ budget records ∧ BinaryArithmetic.toNat word = records.length ∧
      word.length ≤ records.length ∧
      Eval command k (data regs (Encoding.encodeList id records) [] [])
        (data rr (Encoding.encodeList id records) [] word) := by
  obtain ⟨r1,h1⟩ := count_eval regs records
  let mid := data r1 (Encoding.encodeList id records) (List.replicate records.length true) []
  have hp : projectState binaryRegisters binaryStacks mid =
      LeafStatisticsProgram.Binary.state (mid.regs ∘ binaryRegisters)
        (List.replicate records.length true) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨k,word,b,hk,hv,hl,h0,h15,h14,hr,hf,he⟩ := LeafStatisticsProgram.Binary.lifted_eval
    binaryRegisters binaryStacks (Fin.castAdd_injective 3 5) (by decide) mid
    (List.replicate records.length true) hp
  have hb : b = data b.regs (Encoding.encodeList id records) [] word := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      change b.stacks i = (data b.regs (Encoding.encodeList id records) [] word).stacks i
      rw [data_updates b.regs r1 (Encoding.encodeList id records)
        (List.replicate records.length true) [] [] word]
      by_cases h2 : i=2
      · subst i
        change b.stacks (binaryStacks 0) = []
        exact h0
      by_cases hOut : i=15
      · subst i
        change b.stacks (binaryStacks 1) = word
        exact h15
      by_cases hTemp : i=14
      · subst i
        change b.stacks (binaryStacks 2) = []
        exact h14
      · rw [Function.update_of_ne hOut,Function.update_of_ne h2]
        apply hf
        rintro ⟨j,hj⟩
        fin_cases j <;> simp_all [binaryStacks]
  rw [hb] at he
  refine ⟨SubexpScopeCountSetup.countBudget records+1+k,word,b.regs,?_,?_,?_,h1.seq he⟩
  · simp only [List.length_replicate] at hk
    unfold budget
    omega
  · simpa only [List.length_replicate] using hv
  · simpa only [List.length_replicate] using hl

end SubexponentialSAT.SqrtLog.LeafProgram.ClauseCount

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafOuterProgramBoundary
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact physical boundaries for the clause counter, trivial dispatch, and
the final Boolean decision. None of these steps invokes an evaluator oracle. -/
namespace SubexponentialSAT.SqrtLog.LeafOuterProgram

open SubexponentialSAT BitProgram StructuredCalls

theorem clauseCount_eval_oai (a : Data) (records : List (List Bool))
    (hformula : a.stacks 784 = Encoding.encodeList id records)
    (hempty : ∀ i : Fin 896, i.val < 14 → a.stacks i = [])
    (h782 : a.stacks 782 = []) :
    ∃ n b, Eval LeafProgram.ClauseCount.caller n a b ∧
      n ≤ LeafProgram.ClauseCount.budget records+1 ∧
      BinaryArithmetic.toNat (b.stacks 782) = records.length ∧
      (b.stacks 782).length ≤ records.length ∧
      (∀ i : Fin 896, i ≠ 782 → b.stacks i = a.stacks i) := by
  let reg := LeafProgram.ClauseCount.callerRegisters
  let stk := LeafProgram.ClauseCount.callerStacks
  have hr : Function.Injective reg := Fin.castAdd_injective 8 32
  have hs : Function.Injective stk := by decide
  have hp : projectState reg stk a = LeafProgram.ClauseCount.data (a.regs ∘ reg)
      (Encoding.encodeList id records) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;>
        simp [stk,LeafProgram.ClauseCount.callerStacks,
hformula,h782,hempty]
  obtain ⟨n,word,rr,hn,hv,hl,he⟩ := LeafProgram.ClauseCount.command_eval (a.regs ∘ reg) records
  have ht := compiled_halt_trace he 1 15
  rw [← hp] at ht
  let out := LeafProgram.ClauseCount.data rr (Encoding.encodeList id records) [] word
  let b := embedState reg stk a out
  have hb782 : b.stacks 782 = word := embedState_stack reg stk a out hs 15
  refine ⟨n+1,b,eval_call_from_state _ reg stk a hr hs ht,by omega,
    by simpa only [hb782] using hv,by simpa only [hb782] using hl,?_⟩
  intro i hi
  by_cases hport : ∃ j, stk j = i
  · obtain ⟨j,rfl⟩ := hport
    have hj15 : j ≠ 15 := by intro h; subst j; exact hi rfl
    rw [embedState_stack reg stk a out hs]
    have hproj := congrArg (fun d : State 8 16 => d.stacks j) hp
    change a.stacks (stk j) = _ at hproj
    rw [hproj]
    fin_cases j <;> simp_all [out,LeafProgram.ClauseCount.data]
  · exact embedState_stack_frame reg stk a out i hport

end SubexponentialSAT.SqrtLog.LeafOuterProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafOuterProgram.clauseCount_eval_oai
