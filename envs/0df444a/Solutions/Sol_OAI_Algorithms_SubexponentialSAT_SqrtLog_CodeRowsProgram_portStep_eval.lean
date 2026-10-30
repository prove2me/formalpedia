-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:35:05.694998+00:00
-- url     : https://prove2.me/submissions/035b8c2a-deb2-41a3-aa62-6b6e8f87b1dd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_appendSlot_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_preparePort_eval

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

theorem clear_eval (src : Fin 64) (d : Data) :
    Eval (clear src) (2*(d.stacks src).length+3) d (cleared src d) :=
  Subexp.TupleProgram.clear_eval src 0 1 d

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

theorem cleared_register (src : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (cleared src d).regs i=d.regs i := by
  exact copied_register src src d i hi

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

theorem offsetWord_value_bits (d : Data) :
    BinaryArithmetic.toNat (offsetWord d)=coefficientValue (d.regs 8) (d.regs 9) (BinaryArithmetic.toNat (d.stacks 4)) := by
  cases h9 : d.regs 9 <;> cases h8 : d.regs 8 <;>
    simp [offsetWord,coefficientValue,h9,h8,toNat_cons,bitVal_false]

theorem coefficientValue_le (a b : Bool) (m : ℕ) : coefficientValue a b m ≤ 2*m := by
  cases b <;> cases a <;> simp [coefficientValue] ; omega

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

theorem appendCost_le (d : Data) (W : ℕ)
    (h21 : (d.stacks 21).length ≤ W) (h4 : (d.stacks 4).length ≤ W)
    (h5 : (d.stacks 5).length ≤ W) : appendCost d ≤ 500*(W+1)^2 := by
  have hs : (d.stacks 21).length+(d.stacks 4).length+2 ≤ 2*(W+1) := by omega
  have hsq := Nat.pow_le_pow_left hs 2
  dsimp [appendCost]
  nlinarith

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramCounter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem increment_eval (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    Eval (increment src) (CounterPrograms.rippleCost true (d.stacks src)+1)
      d (incremented d src hs) := by
  let p := counterPorts src hs
  have he := eval_call_lifted (CounterPrograms.rippleProgram true)
    p.register (CounterForPrograms.stackPorts p) d p.register.injective
    (CounterForPrograms.stackPorts p).injective
    (CounterForPrograms.ripple_local_trace true (d.regs 0) (d.regs 1) (d.regs 2) (d.stacks src))
  have hm : (CounterForPrograms.stackPorts p : Fin 2 → Fin 64)=incrementStacks src := by
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  change Eval _ _ (CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
    (d.stacks src) []) (incremented d src hs) at he
  have hself : CounterForPrograms.install p d (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks src) []=d := by
    have hh := CounterForPrograms.install_self p d
    simpa [p,counterPorts,low3,ht] using hh
  rw [hself] at he
  rw [hm] at he
  simpa [increment, p, counterPorts] using he

theorem incremented_stacks (d : Data) (src : Fin 64) (hs : src≠41)
    (ht : d.stacks 41=[]) :
    (incremented d src hs).stacks=
      Function.update d.stacks src (CounterPrograms.ripple true (d.stacks src)) := by
  funext i
  let b := CounterForPrograms.localData false false (d.regs 2)
    (CounterPrograms.ripple true (d.stacks src)) []
  unfold incremented CounterForPrograms.install
  by_cases hi : i=src
  · subst i
    have he := embedState_stack (counterPorts src hs).register
      (CounterForPrograms.stackPorts (counterPorts src hs)) d b
      (CounterForPrograms.stackPorts (counterPorts src hs)).injective 0
    simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks] using he
  · by_cases h41 : i=41
    · subst i
      have he := embedState_stack (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b
        (CounterForPrograms.stackPorts (counterPorts src hs)).injective 1
      simpa [b,counterPorts,CounterForPrograms.localData,CounterPrograms.counterStacks,hi,ht] using he
    · have hn : ¬∃ j, CounterForPrograms.stackPorts (counterPorts src hs) j=i := by
        rintro ⟨j,hj⟩
        fin_cases j
        · apply hi; simpa [counterPorts] using hj.symm
        · apply h41; simpa [counterPorts] using hj.symm
      have he := embedState_stack_frame (counterPorts src hs).register
        (CounterForPrograms.stackPorts (counterPorts src hs)) d b i hn
      simpa [hi] using he

theorem incremented_register (d : Data) (src : Fin 64) (hs : src≠41)
    (i : Fin 16) (hi : 3 ≤ i.val) : (incremented d src hs).regs i=d.regs i := by
  apply embedState_register_frame
  rintro ⟨j,hj⟩
  have hjlt : (low3 j).val < 3 := by simp [low3]
  rw [show (counterPorts src hs).register j = low3 j by rfl] at hj
  rw [hj] at hjlt
  exact (Nat.not_lt_of_ge hi) hjlt

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramFinish
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem finishPort_eval (d : Data)
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[])
    (hv : d.regs 7=true →
      BinaryArithmetic.toNat (d.stacks 21)+BinaryArithmetic.toNat (offsetWord d) < 2^(d.stacks 5).length) :
    ∃ n rf, Eval finishPort n d ⟨rf,finishedStacks d⟩ ∧
      n ≤ finishCost d ∧ (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have branch : ∃ n0 r0, Eval (.ite 7 appendSlot (.base .skip)) n0 d
      ⟨r0,Function.update d.stacks 13 (emitted d)⟩ ∧ n0 ≤ appendCost d+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → r0 i=d.regs i) := by
    cases hg : d.regs 7 with
    | false =>
      refine ⟨1,d.regs,?_,by omega,by intros; rfl⟩
      have he : (⟨d.regs,Function.update d.stacks 13 (emitted d)⟩ : Data)=d := by
        cases d with | mk regs stk => simp_all [emitted,Function.update_eq_self]
      rw [he]
      exact Eval.ite_false hg (.base (.skip d))
    | true =>
      obtain ⟨n0,r0,e0,b0,f0⟩ := appendSlot_eval d h22 h23 h24 h25 hw (hv hg)
      exact ⟨n0+1,r0,by simpa only [emitted,hg,ite_true, if_true] using Eval.ite_true hg e0,by omega,f0⟩
  obtain ⟨n0,r0,e0,b0,f0⟩ := branch
  let d0 : Data := ⟨r0,Function.update d.stacks 13 (emitted d)⟩
  let d1 := cleared 18 d0
  let d2 := cleared 20 d1
  let d3 := cleared 21 d2
  have e1 := clear_eval 18 d0
  have e2 := clear_eval 20 d1
  have e3 := clear_eval 21 d2
  have h41' : d3.stacks 41=[] := by simp [d3,d2,d1,d0,cleared,h41]
  have ei := increment_eval d3 14 (by decide) h41'
  let result := incremented d3 14 (by decide)
  have hout : result=⟨result.regs,finishedStacks d⟩ := by
    apply congrArg (StructuredProgram.State.mk result.regs)
    change result.stacks=finishedStacks d
    rw [show result.stacks=Function.update d3.stacks 14
      (CounterPrograms.ripple true (d3.stacks 14)) from
      incremented_stacks d3 14 (by decide) h41']
    simp [finishedStacks,d3,d2,d1,d0,cleared]
  let n := n0+(2*(d0.stacks 18).length+3+(2*(d1.stacks 20).length+3+
    (2*(d2.stacks 21).length+3+(CounterPrograms.rippleCost true (d3.stacks 14)+1))))
  have he : Eval finishPort n d result := e0.seq (e1.seq (e2.seq (e3.seq ei)))
  refine ⟨n,result.regs,by rw [←hout]; exact he,?_,?_⟩
  · have hi := CounterPrograms.rippleCost_le true (d3.stacks 14)
    simp only [d3,d2,d1,d0,cleared,Function.update_noteq (by decide : (14 : Fin 64)≠21),
      Function.update_noteq (by decide : (14 : Fin 64)≠20),
      Function.update_noteq (by decide : (14 : Fin 64)≠18),
      Function.update_noteq (by decide : (14 : Fin 64)≠13)] at hi
    dsimp [n]
    simp [d3,d2,d1,d0,cleared,finishCost] ; omega
  · intro i hi
    exact (incremented_register d3 14 (by decide) i (by omega)).trans
      ((cleared_register 21 d2 i (by omega)).trans
        ((cleared_register 20 d1 i (by omega)).trans
          ((cleared_register 18 d0 i (by omega)).trans (f0 i hi))))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPort
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem portStep_eval_oai (d : Data) (a b : Bool) (qt st : List Bool)
    (pairs : List (Bool × Bool))
    (hq : d.stacks 0=Cell.frame a b++qt)
    (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
    (hv : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (h22 : d.stacks 22=[]) (h23 : d.stacks 23=[])
    (h24 : d.stacks 24=[]) (h25 : d.stacks 25=[]) (h41 : d.stacks 41=[])
    (ha : ∀ i, d.stacks (arithmeticWork i)=[])
    (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[])
    (hcap : 3*BinaryArithmetic.toNat (d.stacks 4) ≤ 2^(d.stacks 5).length) :
    ∃ n rf, Eval portStep n d ⟨rf,portStacks d qt st (portAccum d a b pairs)⟩ ∧
      n ≤ 2000*(portWidth d+1)^2 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i) := by
  obtain ⟨np,rp,prod,idx,ep,vp,flagp,lp,li,bp,fp⟩ :=
    preparePort_eval d a b qt st pairs hq hs hv h17 h18 h19 h20 h21 h24 ha hc
  let p : Data := ⟨rp,preparedStacks d qt st (Shift.result (d.regs 12) pairs) prod idx⟩
  have p8 : p.regs 8=a := by simpa [p,coefficientRegs] using fp 8 (by decide)
  have p9 : p.regs 9=b := by simpa [p,coefficientRegs] using fp 9 (by decide)
  have po : BinaryArithmetic.toNat (offsetWord p)=coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)) := by
    rw [offsetWord_value_bits,p8,p9]
    simp [p,preparedStacks]
  have pv : BinaryArithmetic.toNat idx=portIndex d pairs := vp
  have pflag : p.regs 7=true ↔ portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) := by
    simpa [p,pv] using flagp
  have pha : ∀ i, p.stacks (arithmeticWork i)=[] := by
    intro i
    have h := ha i
    have h0 : arithmeticWork i ≠ (0 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 0 at hv
      omega
    have h1 : arithmeticWork i ≠ (1 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 1 at hv
      omega
    have h18 : arithmeticWork i ≠ (18 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 18 at hv
      omega
    have h20 : arithmeticWork i ≠ (20 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 20 at hv
      omega
    have h21 : arithmeticWork i ≠ (21 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 21 at hv
      omega
    simpa [p, preparedStacks, h0, h1, h18, h20, h21] using h
  have pcap : p.regs 7=true → BinaryArithmetic.toNat (p.stacks 21)+BinaryArithmetic.toNat (offsetWord p) < 2^(p.stacks 5).length := by
    intro hg
    have hlt := pflag.mp hg
    have hco := coefficientValue_le a b (BinaryArithmetic.toNat (d.stacks 4))
    change BinaryArithmetic.toNat idx+BinaryArithmetic.toNat (offsetWord p) < 2^(d.stacks 5).length
    rw [pv,po]
    exact lt_of_lt_of_le (by omega :
      portIndex d pairs+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)) < 3*BinaryArithmetic.toNat (d.stacks 4)) hcap
  obtain ⟨nf,rf,ef,bf,ff⟩ := finishPort_eval p
    (by simpa [p,preparedStacks] using h22) (by simpa [p,preparedStacks] using h23)
    (by simpa [p,preparedStacks] using h24) (by simpa [p,preparedStacks] using h25)
    (by simpa [p,preparedStacks] using h41) pha pcap
  have pe : emitted p=portAccum d a b pairs := by
    simp only [emitted,portAccum,pflag,po]
    change (if portIndex d pairs < BinaryArithmetic.toNat (d.stacks 4) then
      (SubexpLiftRing.fixedBits (d.stacks 5).length
        (BinaryArithmetic.toNat idx+coefficientValue a b (BinaryArithmetic.toNat (d.stacks 4)))).reverse++d.stacks 13
      else d.stacks 13) = _
    rw [pv]
  have pout : finishedStacks p=portStacks d qt st (portAccum d a b pairs) := by
    funext i
    by_cases h0i : i=0
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h1i : i=1
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h13i : i=13
    · subst i
      change emitted p=portAccum d a b pairs
      exact pe
    by_cases h14i : i=14
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks]
    by_cases h18i : i=18
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h18]
    by_cases h20i : i=20
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h20]
    by_cases h21i : i=21
    · subst i; simp [finishedStacks,portStacks,p,preparedStacks,h21]
    simp [finishedStacks,portStacks,p,preparedStacks,
      h0i,h1i,h13i,h14i,h18i,h20i,h21i]
  refine ⟨np+nf,rf,?_,?_,?_⟩
  · simpa only [pout] using ep.seq ef
  · have h4 : (p.stacks 4).length ≤ portWidth d := by simp [p,preparedStacks,portWidth] ; omega
    have h5 : (p.stacks 5).length ≤ portWidth d := by simp [p,preparedStacks,portWidth] ; omega
    have h21p : (p.stacks 21).length ≤ portWidth d := by simpa [p,preparedStacks] using li
    have bap := appendCost_le p (portWidth d) h21p h4 h5
    have hshift : (Shift.result (d.regs 12) pairs).length ≤ portWidth d := by
      have hpairs : pairs.length=(d.stacks 2).length := by rw [hv]; simp
      simp [Shift.result,hpairs,portWidth] ; omega
    have hport : (d.stacks 14).length ≤ portWidth d := by dsimp [portWidth]; omega
    have bfin : nf ≤ 500*(portWidth d+1)^2+14*portWidth d+20 := by
      change nf ≤ appendCost p+2*((Shift.result (d.regs 12) pairs).length+
        prod.length+idx.length)+8*(d.stacks 14).length+20 at bf
      omega
    nlinarith only [bp,bfin,Nat.zero_le (portWidth d)]
  · intro i hi
    exact (ff i hi).trans (fp i hi)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.portStep_eval_oai
