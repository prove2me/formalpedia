-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:08:51.166813+00:00
-- url     : https://prove2.me/submissions/d9e44fc1-3c52-4155-90b2-f5e725ad80c3

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S055
import Definitions.Def_OAIQ081S070
import Definitions.Def_OAIQ081S080

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_PackingProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! One fixed binary machine combines the two collision counts. Its instruction
count and every output length are charged in terms of actual input bit lengths. -/
namespace SubexponentialSAT.SqrtLog.PackingProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls

/-- Intermediate product ports 4 and 5 and output port 6 are written; source
ports and five scratch ports are preserved. The bound is quadratic in bits. -/
theorem weightedScoreCommand_eval (d : ArithmeticData) (hd : arithmeticReady d) :
    ∃ t ≤ 300 * (arithmeticInputLength d + 3)^2, ∃ e : ArithmeticData,
      Eval weightedScoreCommand t d e ∧
      SubexponentialSAT.BinaryArithmetic.toNat (e.stacks 6) = weightedScoreValue d ∧
      (e.stacks 6).length ≤ arithmeticInputLength d + 3 ∧
      (∀ j : Fin 12, j ≠ 4 → j ≠ 5 → j ≠ 6 → e.stacks j = d.stacks j) := by
  have hv1 : Valid firstProductPorts d := by
    constructor
    · exact hd 4 (by decide)
    · intro i; exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₁, r₁, p₁, hrun₁, hvalue₁, hlen₁, ht₁⟩ := multiplyAt_eval firstProductPorts d hv1
  let d₁ : ArithmeticData := ⟨r₁, Function.update d.stacks 4 p₁⟩
  have hv2 : Valid secondProductPorts d₁ := by
    constructor
    · simpa [d₁, secondProductPorts] using hd 5 (by decide)
    · intro i
      have hi : arithmeticWork i ≠ 4 := by fin_cases i <;> decide
      simp only [d₁, secondProductPorts ]
      exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₂, r₂, p₂, hrun₂, hvalue₂, hlen₂, ht₂⟩ := multiplyAt_eval secondProductPorts d₁ hv2
  let d₂ : ArithmeticData := ⟨r₂, Function.update d₁.stacks 5 p₂⟩
  have hv3 : Valid productSumPorts d₂ := by
    constructor
    · simpa [d₂, d₁, productSumPorts] using hd 6 (by decide)
    · intro i
      have hi4 : arithmeticWork i ≠ 4 := by fin_cases i <;> decide
      have hi5 : arithmeticWork i ≠ 5 := by fin_cases i <;> decide
      simp only [d₂, d₁, productSumPorts  ]
      exact hd (arithmeticWork i) (by fin_cases i <;> decide)
  obtain ⟨t₃, r₃, out, hrun₃, hvalue₃, hlen₃, ht₃⟩ := addAt_eval productSumPorts d₂ hv3
  let e : ArithmeticData := ⟨r₃, Function.update d₂.stacks 6 out⟩
  have hvals : SubexponentialSAT.BinaryArithmetic.toNat out = weightedScoreValue d := by
    simp only [firstProductPorts] at hvalue₁
    simp [d₁, secondProductPorts] at hvalue₂
    simp [d₂, d₁, productSumPorts] at hvalue₃
    simpa [weightedScoreValue, hvalue₁, hvalue₂] using hvalue₃
  have hl1 : p₁.length ≤ (d.stacks 0).length + (d.stacks 1).length + 1 := hlen₁
  have hl2 : p₂.length ≤ (d.stacks 2).length + (d.stacks 3).length + 1 := by
    simpa [d₁, secondProductPorts] using hlen₂
  have hl3 : out.length ≤ p₁.length + p₂.length + 1 := by
    simpa [d₂, d₁, productSumPorts] using hlen₃
  have hb1 : (d.stacks firstProductPorts.left).length +
      (d.stacks firstProductPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    dsimp [firstProductPorts, arithmeticInputLength]
    omega
  have hb2 : (d₁.stacks secondProductPorts.left).length +
      (d₁.stacks secondProductPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    simp [d₁, secondProductPorts, arithmeticInputLength]
    omega
  have hb3 : (d₂.stacks productSumPorts.left).length +
      (d₂.stacks productSumPorts.right).length + 1 ≤ arithmeticInputLength d + 3 := by
    change p₁.length + p₂.length + 1 ≤ arithmeticInputLength d + 3
    dsimp [arithmeticInputLength]
    omega
  have ht1 : t₁ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₁.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb1 _))
  have ht2 : t₂ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₂.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb2 _))
  have ht3 : t₃ ≤ 100 * (arithmeticInputLength d + 3)^2 :=
    ht₃.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hb3 _))
  refine ⟨t₁+(t₂+t₃), by omega, e, ?_, ?_, ?_, ?_⟩
  · exact hrun₁.seq (hrun₂.seq hrun₃)
  · simpa [e] using hvals
  · simpa [e, arithmeticInputLength] using (show out.length ≤ arithmeticInputLength d + 3 by
      dsimp [arithmeticInputLength]; omega)
  · intro j hj4 hj5 hj6
    simp [e, d₂, d₁, hj4, hj5, hj6]

end SubexponentialSAT.SqrtLog.PackingProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Exact signed arithmetic for minor enumeration. Integers are represented as
pairs of natural binary words. No modular arithmetic, integer oracle, or
parameter-dependent instruction table is used. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic

theorem positivePorts_injective : Function.Injective positivePorts := by decide
theorem negativePorts_injective : Function.Injective negativePorts := by decide

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

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

private theorem total_scoreCall_eval (ports : Fin 12 → Fin 15)
    (hp : Function.Injective ports) (d : Data)
    (hd : PackingProgram.arithmeticReady (readScore ports d)) :
    ∃ t ≤ 300 * (PackingProgram.arithmeticInputLength (readScore ports d) + 3)^2 + 1,
    ∃ e : Data, Eval (scoreCall ports) t d e ∧
      BinaryArithmetic.toNat (e.stacks (ports 6)) = PackingProgram.weightedScoreValue (readScore ports d) ∧
      (e.stacks (ports 6)).length ≤
        PackingProgram.arithmeticInputLength (readScore ports d) + 3 ∧
      (∀ j, j ≠ ports 4 → j ≠ ports 5 → j ≠ ports 6 → e.stacks j = d.stacks j) := by
  obtain ⟨t, ht, out, he, hv, hl, hf⟩ :=
    PackingProgram.weightedScoreCommand_eval (readScore ports d) hd
  have hs : embedState id ports d (readScore ports d) = d := by
    apply embedState_eq_of_ports id ports d d _ Function.injective_id hp
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; rfl
    · intro i hi; rfl
  refine ⟨t+1, by omega, embedState id ports d out, ?_, ?_, ?_, ?_⟩
  · have h := eval_call_lifted PackingProgram.weightedScoreProgram id ports d
      Function.injective_id hp (compiled_halt_trace he 0 6)
    simpa only [hs, scoreCall] using h
  · simpa only [embedState_stack id ports d out hp] using hv
  · simpa only [embedState_stack id ports d out hp] using hl
  · intro j h4 h5 h6
    classical
    by_cases hj : ∃ i, ports i = j
    · obtain ⟨i, rfl⟩ := hj
      rw [embedState_stack id ports d out hp]
      exact hf i (fun hi => h4 (congrArg ports hi))
        (fun hi => h5 (congrArg ports hi)) (fun hi => h6 (congrArg ports hi))
    · exact embedState_stack_frame id ports d out j hj

theorem multiplyCommand_eval_total (d : Data) (hd : Ready d) :
    ∃ t ≤ 600 * (inputLength d + 3)^2 + 2, ∃ e : Data,
      Eval multiplyCommand t d e ∧
      signedValue (e.stacks 6) (e.stacks 9) =
        signedValue (d.stacks 0) (d.stacks 1) *
          signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal (e.stacks 6) (e.stacks 9) =
        pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
      (e.stacks 6).length ≤ inputLength d + 3 ∧
      (e.stacks 9).length ≤ inputLength d + 3 ∧
      (∀ j : Fin 15, j.val < 4 ∨ 10 ≤ j.val → e.stacks j = d.stacks j) := by
  have hp : PackingProgram.arithmeticReady (readScore positivePorts d) := by
    intro j hj
    have hj' : 4 ≤ (positivePorts j).val := by
      fin_cases j <;> norm_num [positivePorts] at *
    exact hd _ hj'
  obtain ⟨tp, htp, middle, he1, hv1, hl1, hf1⟩ :=
    total_scoreCall_eval positivePorts positivePorts_injective d hp
  have hm (j : Fin 15) (hj : j ≠ 4 ∧ j ≠ 5 ∧ j ≠ 6) :
      middle.stacks j = d.stacks j := hf1 j hj.1 hj.2.1 hj.2.2
  have hn : PackingProgram.arithmeticReady (readScore negativePorts middle) := by
    intro j hj
    change middle.stacks (negativePorts j) = []
    have hj' : 4 ≤ (negativePorts j).val := by
      fin_cases j <;> norm_num [negativePorts] at *
    have hn4 : negativePorts j ≠ 4 := by fin_cases j <;> decide
    have hn5 : negativePorts j ≠ 5 := by fin_cases j <;> decide
    have hn6 : negativePorts j ≠ 6 := by fin_cases j <;> decide
    rw [hm _ ⟨hn4, hn5, hn6⟩]
    exact hd _ hj'
  obtain ⟨tn, htn, out, he2, hv2, hl2, hf2⟩ :=
    total_scoreCall_eval negativePorts negativePorts_injective middle hn
  have hlen1 : PackingProgram.arithmeticInputLength (readScore positivePorts d) =
      inputLength d := by
    simp [PackingProgram.arithmeticInputLength, readScore, positivePorts, inputLength]
    omega
  have hlen2 : PackingProgram.arithmeticInputLength (readScore negativePorts middle) =
      inputLength d := by
    simp [PackingProgram.arithmeticInputLength, readScore, negativePorts, inputLength,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)]
    omega
  have hpout : out.stacks 6 = middle.stacks 6 := hf2 6 (by decide) (by decide) (by decide)
  refine ⟨tp+tn, by rw [hlen1] at htp; rw [hlen2] at htn; omega,
    out, he1.seq he2, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [signedValue, hpout]
    simp [PackingProgram.weightedScoreValue, readScore, positivePorts] at hv1
    simp [PackingProgram.weightedScoreValue, readScore, negativePorts,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at hv2
    rw [hv1, hv2]
    push_cast
    ring
  · simp only [pairTotal, hpout]
    simp [PackingProgram.weightedScoreValue, readScore, positivePorts] at hv1
    simp [PackingProgram.weightedScoreValue, readScore, negativePorts,
      hm 0 (by decide), hm 1 (by decide), hm 2 (by decide), hm 3 (by decide)] at hv2
    rw [hv1,hv2]
    ring
  · change (middle.stacks 6).length ≤ _ at hl1
    rw [hlen1] at hl1
    simpa only [hpout] using hl1
  · change (out.stacks 9).length ≤ _ at hl2
    rwa [hlen2] at hl2
  · intro j hj
    have h4 : j ≠ 4 := by
      intro h
      have hh : j.val = 4 := congrArg Fin.val h
      omega
    have h5 : j ≠ 5 := by
      intro h
      have hh : j.val = 5 := congrArg Fin.val h
      omega
    have h6 : j ≠ 6 := by
      intro h
      have hh : j.val = 6 := congrArg Fin.val h
      omega
    have h7 : j ≠ 7 := by
      intro h
      have hh : j.val = 7 := congrArg Fin.val h
      omega
    have h8 : j ≠ 8 := by
      intro h
      have hh : j.val = 8 := congrArg Fin.val h
      omega
    have h9 : j ≠ 9 := by
      intro h
      have hh : j.val = 9 := congrArg Fin.val h
      omega
    exact (hf2 j h7 h8 h9).trans (hf1 j h4 h5 h6)

private theorem total_initial_stack_bound (d : Data) (hd : Ready d) (j : Fin 15) :
    (d.stacks j).length ≤ inputLength d := by
  by_cases hj : j.val < 4
  · fin_cases j <;> simp_all [inputLength] <;> omega
  · rw [hd j (by omega)]
    simp

theorem multiplyReuseCommand_eval_total_oai (d : Data) (hd : Ready d) :
    ∃ t ≤ 25000*(inputLength d+3)^2, ∃ regs positive negative,
      Eval multiplyReuseCommand t d (pairState regs positive negative) ∧
      signedValue positive negative =
        signedValue (d.stacks 0) (d.stacks 1) * signedValue (d.stacks 2) (d.stacks 3) ∧
      pairTotal positive negative =
        pairTotal (d.stacks 0) (d.stacks 1) * pairTotal (d.stacks 2) (d.stacks 3) ∧
      positive.length + negative.length ≤ 2*inputLength d+6 := by
  obtain ⟨tm, htm, m, hem, hv, htotal, hp, hn, hf⟩ := multiplyCommand_eval_total d hd
  have hm (j : Fin 15) : (m.stacks j).length ≤ inputLength d+tm := by
    exact (eval_stack_length hem j).trans (Nat.add_le_add_right (total_initial_stack_bound d hd j) tm)
  have hf' (j : Fin 15) (hj : 10 ≤ j.val) : m.stacks j = [] := by
    rw [hf j (Or.inr hj), hd j (by omega)]
  obtain ⟨tf, htf, regs, hef⟩ := finishCommand_eval m (inputLength d+tm) hm hf'
  refine ⟨tm+tf, ?_, regs, m.stacks 6, m.stacks 9, hem.seq hef, hv, htotal, by omega⟩
  nlinarith [sq_nonneg (inputLength d : ℤ)]


end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.multiplyReuseCommand_eval_total_oai
