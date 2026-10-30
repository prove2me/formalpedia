-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:32:12.22693+00:00
-- url     : https://prove2.me/submissions/9e14790b-09d4-466e-a5af-088e55ad56f1

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_padding_call_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramStorage
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines

theorem copy_eval (src dst : Fin 64) (d : Data)
    (hsd : src≠dst) (hst : src≠24) (htd : (24 : Fin 64)≠dst)
    (htmp : d.stacks 24=[]) :
    Eval (copy src dst) (7*(d.stacks src).length+5) d (copied src dst d) :=
  Subexp.TupleProgram.copy_eval src dst 24 0 1 hsd hst htd (by decide) d htmp

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared src d) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem push_eval (dst : Fin 64) (b : Bool) (d : Data) :
    Eval (push dst b) 2 d (pushed dst b d) :=
  Subexp.TupleProgram.pushConst_eval dst 0 b d

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

theorem cleared_register (src : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (cleared src d).regs i=d.regs i := by
  exact copied_register src src d i hi

theorem pushed_register (dst : Fin 64) (b : Bool) (d : Data) (i : Fin 16)
    (hi : 1 ≤ i.val) : (pushed dst b d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  simp [pushed,h0]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramOffset
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem offsetWord_length (d : Data) :
    (offsetWord d).length ≤ (d.stacks 4).length+1 := by
  cases h9 : d.regs 9 <;> cases h8 : d.regs 8 <;> simp [offsetWord,h9,h8]

theorem coefficientOffset_eval (d : Data) (he : d.stacks 22=[])
    (ht : d.stacks 24=[]) :
    ∃ n rf, Eval coefficientOffset n d
      ⟨rf,Function.update d.stacks 22 (offsetWord d)⟩ ∧
      n ≤ 7*(d.stacks 4).length+9 ∧
      (∀ i : Fin 16, 2 ≤ i.val → rf i=d.regs i) := by
  cases h9 : d.regs 9 with
  | false =>
    cases h8 : d.regs 8 with
    | false =>
      have hs : (⟨d.regs,Function.update d.stacks 22 (offsetWord d)⟩ : Data)=d := by
        cases d with
        | mk regs stk =>
          simp_all [offsetWord]
      refine ⟨2,d.regs,?_,by omega,by intros; rfl⟩
      rw [hs]
      exact Eval.ite_false h9 (Eval.ite_false h8 (.base (.skip d)))
    | true =>
      have hc := copy_eval 4 22 d (by decide) (by decide) (by decide) ht
      have hs : copied 4 22 d=
          ⟨(copied 4 22 d).regs,Function.update d.stacks 22 (offsetWord d)⟩ := by
        simp [copied,StackRoutines.copyStacks,offsetWord,h8,h9,he]
      refine ⟨7*(d.stacks 4).length+7,(copied 4 22 d).regs,?_,by omega,?_⟩
      · rw [←hs]
        exact Eval.ite_false h9 (Eval.ite_true h8 hc)
      · exact copied_register 4 22 d
  | true =>
    have hc := copy_eval 4 22 d (by decide) (by decide) (by decide) ht
    have hp := push_eval 22 false (copied 4 22 d)
    let e := pushed 22 false (copied 4 22 d)
    have hs : e=⟨e.regs,Function.update d.stacks 22 (offsetWord d)⟩ := by
      simp [e,pushed,copied,StackRoutines.copyStacks,offsetWord,h9,he]
    refine ⟨7*(d.stacks 4).length+8,e.regs,?_,by omega,?_⟩
    · rw [←hs]
      exact Eval.ite_true h9 (hc.seq hp)
    · intro i hi
      exact (pushed_register 22 false (copied 4 22 d) i (by omega)).trans
        (copied_register 4 22 d i hi)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramArithmetic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ArithmeticCalls SubexponentialSAT.BinaryArithmetic

theorem low8_injective : Function.Injective low8 := Fin.castAdd_injective _ _

theorem slotArithmetic_eval (d : Data) (h23 : d.stacks 23=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf word, Eval (liftArithmetic (addAt (arithmeticPorts 2))) n d
      ⟨rf,Function.update d.stacks 23 word⟩ ∧
      BinaryArithmetic.toNat word=BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (d.stacks 22) ∧
      word.length ≤ (d.stacks 21).length+(d.stacks 22).length+1 ∧
      n ≤ 100*((d.stacks 21).length+(d.stacks 22).length+1)^2+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  let a := projectState low8 id d
  have hv : Valid (arithmeticPorts 2) a := ⟨h23,hw⟩
  obtain ⟨n,rr,word,he,hval,hlen,hcost⟩ := addAt_eval (arithmeticPorts 2) a hv
  let small : State 8 64 := ⟨rr,Function.update d.stacks 23 word⟩
  let out := embedState low8 id d small
  have he' := eval_liftCommand_from_state (addAt (arithmeticPorts 2)) 0 0 low8 id d
    low8_injective Function.injective_id he
  have hout : out=⟨out.regs,Function.update d.stacks 23 word⟩ := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    exact Function.injective_id.extend_apply _ _ i
  change Eval (liftArithmetic (addAt (arithmeticPorts 2))) (n+1) d out at he'
  rw [hout] at he'
  refine ⟨n+1,out.regs,word,he',?_,?_,?_,?_⟩
  · simpa [a,arithmeticPorts,projectState] using hval
  · simpa [a,arithmeticPorts,projectState] using hlen
  · have hh : n ≤ 100*((d.stacks 21).length+(d.stacks 22).length+1)^2 := by
      simpa [a,arithmeticPorts,projectState] using hcost
    omega
  · intro i hi
    apply embedState_register_frame low8 id d small i
    rintro ⟨j,hj⟩
    have hh := congrArg Fin.val hj
    have hjlt := j.isLt
    dsimp [low8] at hh
    omega

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramAppend
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem appendSlot_eval_oai (d : Data)
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[])
    (hv : BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
    ∃ n rf, Eval appendSlot n d
      ⟨rf,Function.update d.stacks 13
        ((SubexpLiftRing.fixedBits (d.stacks 5).length
          (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ ∧
      n ≤ appendCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨n0,r0,e0,b0,f0⟩ := coefficientOffset_eval d h22 h24
  let d0 : Data := ⟨r0,Function.update d.stacks 22 (offsetWord d)⟩
  have h23' : d0.stacks 23=[] := by simp [d0,h23]
  have hw' : ∀ i, d0.stacks (arithmeticWork i)=[] := by
    intro i
    have hi : arithmeticWork i≠22 := (arithmeticPorts 2).work_ne_right i
    simpa [d0,hi] using hw i
  obtain ⟨n1,r1,word,e1,v1,l1,b1,f1⟩ := slotArithmetic_eval d0 h23' hw'
  let d1 : Data := ⟨r1,Function.update d0.stacks 23 word⟩
  have h24' : d1.stacks 24=[] := by simp [d1,d0,h24]
  have ec := copy_eval 5 25 d1 (by decide) (by decide) (by decide) h24'
  let d2 := copied 5 25 d1
  have vw : BinaryArithmetic.toNat word=BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) := by
    simpa [d0] using v1
  have hv' : BinaryArithmetic.toNat (d2.stacks 23) < 2^(d2.stacks 25).length := by
    simpa [d2,copied,StackRoutines.copyStacks,d1,d0,h25,vw] using hv
  obtain ⟨r2,ep,fp⟩ := padding_call_eval d2 hv'
  let d3 : Data := ⟨r2,paddedStacks d2⟩
  have ez := clear_eval 23 d3
  let d4 := cleared 23 d3
  have eo := clear_eval 22 d4
  let result := cleared 22 d4
  have hout : result=⟨result.regs,Function.update d.stacks 13
      ((SubexpLiftRing.fixedBits (d.stacks 5).length
        (BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d))).reverse++d.stacks 13)⟩ := by
    apply congrArg (StructuredProgram.State.mk result.regs)
    funext i
    by_cases h13i : i=13
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h25,vw]
    by_cases h22i : i=22
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h22]
    by_cases h23i : i=23
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h23]
    by_cases h25i : i=25
    · subst i
      simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,h25]
    simp [d4,cleared,d3,paddedStacks,d2,copied,StackRoutines.copyStacks,d1,d0,
      h13i,h22i,h23i,h25i]
  let cost := n0+(n1+(7*(d1.stacks 5).length+5+
    (4*(d2.stacks 25).length+3+(2*(d3.stacks 23).length+3+
      (2*(d4.stacks 22).length+3)))))
  have he : Eval appendSlot cost d result :=
    e0.seq (e1.seq (ec.seq (ep.seq (ez.seq eo))))
  refine ⟨cost,result.regs,by rw [←hout]; exact he,?_,?_⟩
  · have lo := offsetWord_length d
    have lw : word.length ≤ (d.stacks 21).length+(d.stacks 4).length+2 := by
      simp only [d0,Function.update_noteq (by decide : (21 : Fin 64)≠22),
        Function.update_same] at l1
      omega
    have ba : n1 ≤ 100*((d.stacks 21).length+(d.stacks 4).length+2)^2+1 := by
      apply b1.trans
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_left
      simp only [d0,Function.update_noteq (by decide : (21 : Fin 64)≠22),
        Function.update_same]
      omega
    have ldrop : (word.drop (d.stacks 5).length).length ≤ word.length := by
      simp only [List.length_drop]
      omega
    dsimp [cost]
    simp only [d1,d0,d2,copied,StackRoutines.copyStacks,d3,paddedStacks,d4,cleared,
      Function.update_same,Function.update_noteq (by decide : (5 : Fin 64)≠23),
      Function.update_noteq (by decide : (5 : Fin 64)≠22),
      Function.update_noteq (by decide : (25 : Fin 64)≠23),
      Function.update_noteq (by decide : (25 : Fin 64)≠22),
      Function.update_noteq (by decide : (23 : Fin 64)≠13),
      Function.update_noteq (by decide : (23 : Fin 64)≠25),
      Function.update_noteq (by decide : (22 : Fin 64)≠23),
      Function.update_noteq (by decide : (22 : Fin 64)≠13),
      Function.update_noteq (by decide : (22 : Fin 64)≠25),h25,List.append_nil]
    dsimp [appendCost]
    omega
  · intro i hi
    exact (cleared_register 22 d4 i (by omega)).trans
      ((cleared_register 23 d3 i (by omega)).trans
        ((fp i hi).trans ((copied_register 5 25 d1 i (by omega)).trans
          ((f1 i hi).trans (f0 i (by omega))))))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.appendSlot_eval_oai
