-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:03:52.070561+00:00
-- url     : https://prove2.me/submissions/cf0b3b86-932b-4965-bb17-8265b9327a7d

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S071
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S075
import Definitions.Def_OAIQ081S080
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_RowSelectionProgram_multiplyReuseCommand_eval_total
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_RowSelectionProgram_streamPorts_injective

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Stack-size accounting and fixed cleanup loops for signed minor arithmetic. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem instr_stack_length {r s l : ℕ} (i : Instr r s l)
    (a : Cfg r s l) (j : Fin s) :
    ((execInstr i a).stacks j).length ≤ (a.stacks j).length + 1 := by
  cases i <;> simp only [execInstr]
  all_goals try omega
  case push stack src next =>
    by_cases h : j = stack
    · subst j; simp
    · simp [h]
  case pop stack value present next =>
    by_cases h : j = stack
    · subst j; simp; omega
    · simp [h]

theorem trace_stack_length {r s l : ℕ} (p : Program r s l) {t : ℕ}
    {a b : Cfg r s l} (h : Trace p t a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + t := by
  induction h with
  | refl => omega
  | @cons t a b c hs ht ih =>
    have hb : (b.stacks j).length ≤ (a.stacks j).length + 1 := by
      cases hp : a.pc with
      | none => simp [step, hp] at hs
      | some q =>
        have he : execInstr (p.code q) a = b := by simpa [step, hp] using hs
        rw [← he]
        exact instr_stack_length _ _ _
    omega

theorem eval_stack_length {r s : ℕ} {c : Cmd r s} {t : ℕ}
    {a b : State r s} (h : Eval c t a b) (j : Fin s) :
    (b.stacks j).length ≤ (a.stacks j).length + t := by
  exact trace_stack_length _ (compiled_trace h j j) j

theorem clearAt_eval (j : Fin 15) (d : Data) :
    Eval (clearAt j) (2*(d.stacks j).length+3) d (clearedAt j d) := by
  simpa only [clearAt, clearedAt, StackRoutines.clearStacks] using
    Subexp.TupleProgram.clear_eval j 0 1 d

theorem clearList_eval (js : List (Fin 15)) (d : Data) :
    ∃ t ≤ (js.map fun j => 2*(d.stacks j).length+3).sum,
      Eval (clearList js) t d (clearedList js d) := by
  induction js generalizing d with
  | nil => exact ⟨0, by simp, .base (.skip _)⟩
  | cons j js ih =>
    obtain ⟨t, ht, he⟩ := ih (clearedAt j d)
    refine ⟨2*(d.stacks j).length+3+t, ?_, (clearAt_eval j d).seq he⟩
    simp only [List.map_cons, List.sum_cons]
    have hm : (js.map fun i => 2*((clearedAt j d).stacks i).length+3).sum ≤
        (js.map fun i => 2*(d.stacks i).length+3).sum := by
      apply List.sum_le_sum
      intro i hi
      by_cases hij : i = j <;> simp [clearedAt, hij]
    omega

/-- Cleanup bound expressed by a uniform bound on the input stack lengths. -/
theorem clearList_eval_bounded (js : List (Fin 15)) (d : Data) (B : ℕ)
    (hb : ∀ j ∈ js, (d.stacks j).length ≤ B) :
    ∃ t ≤ js.length*(2*B+3), Eval (clearList js) t d (clearedList js d) := by
  obtain ⟨t, ht, he⟩ := clearList_eval js d
  refine ⟨t, ht.trans ?_, he⟩
  calc
    (js.map fun j => 2*(d.stacks j).length+3).sum ≤
        (js.map fun _ => 2*B+3).sum := by
      apply List.sum_le_sum
      intro j hj
      have := hb j hj
      omega
    _ = js.length*(2*B+3) := by simp

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramReuse
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed cleanup adapter makes signed arithmetic reusable inside loops. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem finishCommand_eval (d : Data) (B : ℕ)
    (hb : ∀ j : Fin 15, (d.stacks j).length ≤ B)
    (hf : ∀ j : Fin 15, 10 ≤ j.val → d.stacks j = []) :
    ∃ t ≤ 34*B+40, ∃ regs,
      Eval finishCommand t d (pairState regs (d.stacks 6) (d.stacks 9)) := by
  let a := clearedList [0,1,2,3,4,5,7,8] d
  obtain ⟨tc, htc, hec⟩ := clearList_eval_bounded [0,1,2,3,4,5,7,8] d B
    (fun j _ => hb j)
  have ha0 : a.stacks 0 = [] := by simp [a]
  have ha1 : a.stacks 1 = [] := by simp [a]
  have ha6 : a.stacks 6 = d.stacks 6 := by simp [a]
  have ha9 : a.stacks 9 = d.stacks 9 := by simp [a]
  have ha10 : a.stacks 10 = [] := by simpa [a] using hf 10 (by decide)
  let b := ArithmeticCalls.afterCopy 6 0 a
  have he0 := ArithmeticCalls.copyAt_eval 6 0 10 a (by decide) (by decide)
    (by decide) ha0 ha10
  have hb1 : b.stacks 1 = [] := by simpa [b, ArithmeticCalls.afterCopy] using ha1
  have hb10 : b.stacks 10 = [] := by simpa [b, ArithmeticCalls.afterCopy] using ha10
  let c := ArithmeticCalls.afterCopy 9 1 b
  have he1 := ArithmeticCalls.copyAt_eval 9 1 10 b (by decide) (by decide)
    (by decide) hb1 hb10
  have hc6 : c.stacks 6 = d.stacks 6 := by simpa [c, b, ArithmeticCalls.afterCopy] using ha6
  have hc9 : c.stacks 9 = d.stacks 9 := by simpa [c, b, ArithmeticCalls.afterCopy] using ha9
  obtain ⟨td, htd, hed⟩ := clearList_eval_bounded [6,9] c B (by
    intro j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl
    · simpa only [hc6] using hb 6
    · simpa only [hc9] using hb 9)
  let out := clearedList [6,9] c
  have hout : out = pairState out.regs (d.stacks 6) (d.stacks 9) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      have hf10 := hf 10 (by decide)
      have hf11 := hf 11 (by decide)
      have hf12 := hf 12 (by decide)
      have hf13 := hf 13 (by decide)
      have hf14 := hf 14 (by decide)
      fin_cases j <;>
        simp [ c, b, a, clearedList, clearedAt, ArithmeticCalls.afterCopy,
          hf10, hf11, hf12, hf13, hf14]
  refine ⟨tc + ((7*(a.stacks 6).length+5) + ((7*(b.stacks 9).length+5)+td)),
    ?_, out.regs, ?_⟩
  · have hb6 := hb 6
    have hb9 := hb 9
    simp only [List.length_cons, List.length_nil] at htc htd
    have hb9' : b.stacks 9 = d.stacks 9 := by
      simpa [b, ArithmeticCalls.afterCopy] using ha9
    rw [ha6, hb9']
    omega
  · rw [← hout]
    exact hec.seq (he0.seq (he1.seq hed))

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalar
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete arithmetic adapters for the cached layout scalar loop.
The working signed pair occupies 0/1, the next operand 2/3, the record queue
15, and the saved sum 16/17. All arithmetic is an actual compiled bit program.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem workPorts_injective : Function.Injective workPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 18 => k.val) h

theorem workCall_eval {c : Cmd 8 16} {t : ℕ}
    {regs regs' : Fin 8 → Bool} {work next work' next' : WordPair}
    {queue queue' : List Bool}
    (he : Eval c t (streamData regs work next queue)
      (streamData regs' work' next' queue')) (acc : WordPair) :
    Eval (workCall c) (t+1) (state regs acc work next queue)
      (state regs' acc work' next' queue') := by
  have emb (r : Fin 8 → Bool) (w n : WordPair) (q : List Bool) :
      embedState id workPorts (state regs acc work next queue)
        (streamData r w n q) = state r acc w n q := by
    apply embedState_eq_of_ports id workPorts _ _ _
      Function.injective_id workPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [state, streamData, workPorts]
    · intro i hi
      have hv : 16 ≤ i.val := by
        by_contra h
        have hlt : i.val < 16 := by omega
        exact hi ⟨⟨i.val,hlt⟩, Fin.ext rfl⟩
      fin_cases i <;> simp_all [state]
  have h := eval_call_lifted (compiled c 0 1) id workPorts
    (state regs acc work next queue) Function.injective_id workPorts_injective
    (compiled_halt_trace he 0 1)
  simpa only [workCall, emb] using h

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTotal
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact nonnegative component-mass contracts for the actual signed arithmetic
programs. These bounds control both components even when cancellation occurs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic SubexponentialSAT.ArithmeticCalls

theorem addCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 200 * (inputLength d + 1)^2, ∃ e : Data,
      Eval addCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal (e.stacks 6) (e.stacks 9) =
        pairTotal (d.stacks 0) (d.stacks 1) + pairTotal (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length + (e.stacks 9).length ≤ inputLength d + 2 ∧
      (∀ j : Fin 15, j ≠ 6 → j ≠ 9 → e.stacks j = d.stacks j) := by
  have hp : Valid addPositivePorts d := by
    constructor
    · exact hd 6 (by decide)
    · intro i
      exact hd (addWork i) (by
        change 4 ≤ i.val + 10
        omega)
  obtain ⟨tp, rp, wp, hep, hvp, hlp, htp⟩ := addAt_eval addPositivePorts d hp
  let middle : Data := ⟨rp, Function.update d.stacks 6 wp⟩
  have hn : Valid addNegativePorts middle := by
    constructor
    · simpa [middle, addNegativePorts] using hd 9 (by decide)
    · intro i
      have hi : addWork i ≠ 6 := by fin_cases i <;> decide
      simpa [middle, addNegativePorts, hi] using hd (addWork i) (by
        change 4 ≤ i.val + 10
        omega)
  obtain ⟨tn, rn, wn, hen, hvn, hln, htn⟩ := addAt_eval addNegativePorts middle hn
  let out : Data := ⟨rn, Function.update middle.stacks 9 wn⟩
  have hpbound : (d.stacks addPositivePorts.left).length +
      (d.stacks addPositivePorts.right).length + 1 ≤ inputLength d + 1 := by
    dsimp [addPositivePorts, inputLength]; omega
  have hnbound : (middle.stacks addNegativePorts.left).length +
      (middle.stacks addNegativePorts.right).length + 1 ≤ inputLength d + 1 := by
    simp [middle, addNegativePorts, inputLength]; omega
  have htp' := htp.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hpbound 2))
  have htn' := htn.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hnbound 2))
  refine ⟨tp+tn, by omega, out, hep.seq hen, ?_, ?_, ?_, ?_⟩
  · simp [addPositivePorts] at hvp
    simp [middle, addNegativePorts] at hvn
    simp [out, middle, signedValue, hvp, hvn]
    ring
  · simp [addPositivePorts] at hvp
    simp [middle, addNegativePorts] at hvn
    simp [out,middle,pairTotal,hvp,hvn]
    omega
  · simp [addPositivePorts] at hlp
    simp [middle, addNegativePorts] at hln
    simp [out, middle, inputLength]
    omega
  · intro j h6 h9
    simp [out, middle, h6, h9]

private theorem total_initial_stack_bound (d : Data) (hd : Ready d) (j : Fin 15) :
    (d.stacks j).length ≤ inputLength d := by
  by_cases hj : j.val < 4
  · fin_cases j <;> simp_all [inputLength] <;> omega
  · rw [hd j (by omega)]
    simp

theorem addReuseCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval addReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) + signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal positive negative =
        pairTotal (d.stacks 0) (d.stacks 1) + pairTotal (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ inputLength d+2 := by
  obtain ⟨tm, htm, m, hem, hv, htotal, hl, hf⟩ := addCommand_eval_total d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (total_initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    have hj6 : j ≠ 6 := by intro h; have : j.val = 6 := congrArg Fin.val h; omega
    have hj9 : j ≠ 9 := by intro h; have : j.val = 9 := congrArg Fin.val h; omega
    rw [hf j hj6 hj9, hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, htotal, hl⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]


end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramTotalStream
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem localOperation_eval_total (multiply : Bool) (regs : Fin 8 → Bool)
    (acc next : WordPair) :
    ∃ t ≤ 25000*(pairLength acc+pairLength next+3)^2, ∃ regs' result,
      Eval (localOperation multiply) t (localInput regs acc next)
        (pairState regs' result.1 result.2) ∧
      pairValue result = combine multiply (pairValue acc) (pairValue next) ∧
      pairTotal result.1 result.2 = (if multiply then
        pairTotal acc.1 acc.2 * pairTotal next.1 next.2 else
        pairTotal acc.1 acc.2 + pairTotal next.1 next.2) ∧
      pairLength result ≤ wordGrowth multiply (pairLength acc) (pairLength next) := by
  have hd : Ready (localInput regs acc next) := by
    intro j hj
    fin_cases j <;> simp_all [localInput]
  have hl : inputLength (localInput regs acc next) = pairLength acc+pairLength next := by
    simp [inputLength, localInput, pairLength, Nat.add_assoc]
  cases multiply with
  | false =>
    obtain ⟨t, ht, r, p, n, he, hv, htotal, hb⟩ := addReuseCommand_eval_total _ hd
    refine ⟨t, by simpa only [hl] using ht, r, (p,n), he, ?_, ?_, ?_⟩
    · simpa [pairValue, localInput, combine] using hv
    · simpa [localInput] using htotal
    · simpa only [hl, pairLength, wordGrowth, Bool.false_eq_true, ↓reduceIte] using hb
  | true =>
    obtain ⟨t, ht, r, p, n, he, hv, htotal, hb⟩ := multiplyReuseCommand_eval_total _ hd
    refine ⟨t, by simpa only [hl] using ht, r, (p,n), he, ?_, ?_, ?_⟩
    · simpa [pairValue, localInput, combine] using hv
    · simpa [localInput] using htotal
    · simpa only [hl, pairLength, wordGrowth, ↓reduceIte] using hb

private theorem outside_streamPorts_total (j : Fin 16)
    (hj : ¬ ∃ i, streamPorts i = j) : j = 15 := by
  have hv : ¬ j.val < 15 := by
    intro h
    exact hj ⟨⟨j.val,h⟩, Fin.ext rfl⟩
  apply Fin.ext
  change j.val = 15
  omega

theorem streamOperation_eval_total (multiply : Bool) (regs : Fin 8 → Bool)
    (acc next : WordPair) (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength acc+pairLength next+3)^2+1, ∃ regs' result,
      Eval (streamOperation multiply) t (streamData regs acc next queue)
        (streamData regs' result ([],[]) queue) ∧
      pairValue result = combine multiply (pairValue acc) (pairValue next) ∧
      pairTotal result.1 result.2 = (if multiply then
        pairTotal acc.1 acc.2 * pairTotal next.1 next.2 else
        pairTotal acc.1 acc.2 + pairTotal next.1 next.2) ∧
      pairLength result ≤ wordGrowth multiply (pairLength acc) (pairLength next) := by
  obtain ⟨t, ht, r, result, he, hv, htotal, hb⟩ := localOperation_eval_total multiply regs acc next
  have hs : embedState id streamPorts (streamData regs acc next queue)
      (localInput regs acc next) = streamData regs acc next queue := by
    apply embedState_eq_of_ports id streamPorts _ _ _ Function.injective_id streamPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [streamData, localInput, streamPorts]
    · intro i hi; rfl
  have hf : embedState id streamPorts (streamData regs acc next queue)
      (pairState r result.1 result.2) = streamData r result ([],[]) queue := by
    apply embedState_eq_of_ports id streamPorts _ _ _ Function.injective_id streamPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [streamData, pairState, streamPorts]
    · intro i hi
      rw [outside_streamPorts_total i hi]
      rfl
  have hcall := eval_call_lifted (localOperationProgram multiply) id streamPorts
    (streamData regs acc next queue) Function.injective_id streamPorts_injective
    (compiled_halt_trace he 0 1)
  rw [hs, hf] at hcall
  exact ⟨t+1, by omega, r, result, hcall, hv, htotal, hb⟩

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarStep
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A single cached scalar term: three parsed operands, three real signed
multiplications, and one real signed addition. -/

/-! Polynomial source-step bounds for the concrete cached scalar arithmetic.
The stream has three actual binary signed operands per summand, not a stream
of precomputed products or an assumed arithmetic callback. -/

/-! Exact unsigned component totals for the same concrete scalar program.
The extra invariant controls cancellation without changing any instruction. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem multiply_eval_total_oai (regs : Fin 8 → Bool) (acc work next : WordPair)
    (queue : List Bool) :
    ∃ t ≤ 25000*(pairLength work+pairLength next+3)^2+2,
    ∃ r result, Eval multiply t (state regs acc work next queue)
      (state r acc result ([],[]) queue) ∧
      pairValue result = pairValue work * pairValue next ∧
      wordTotal result = wordTotal work * wordTotal next ∧
      pairLength result ≤ 2*(pairLength work+pairLength next)+6 := by
  obtain ⟨t,ht,r,result,he,hv,hm,hl⟩ := streamOperation_eval_total true regs work next queue
  exact ⟨t+1,by omega,r,result,workCall_eval he acc,
    by simpa only [combine,↓reduceIte] using hv,
    by simpa [wordTotal] using hm,
    by simpa only [wordGrowth,↓reduceIte] using hl⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.multiply_eval_total_oai
