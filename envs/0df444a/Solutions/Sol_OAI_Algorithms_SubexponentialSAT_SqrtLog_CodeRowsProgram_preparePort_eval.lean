-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:36:29.290325+00:00
-- url     : https://prove2.me/submissions/c96d3695-fc15-4d6d-a274-c6533d16a7bd

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S118
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_Shift_command_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_belowClauseCount_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_CodeRowsProgram_readCoefficient_eval

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

theorem indexArithmetic_eval (d : State 8 64)
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf product idx, Eval indexArithmetic n d
      ⟨rf,Function.update (Function.update d.stacks 20 product) 21 idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      product.length ≤ indexWidth d ∧ idx.length ≤ indexWidth d ∧
      n ≤ 200*(indexWidth d)^2 := by
  have hv0 : Valid (arithmeticPorts 0) d := ⟨h20,hw⟩
  obtain ⟨t0,r0,w0,he0,hv0',hl0,ht0⟩ := multiplyAt_eval (arithmeticPorts 0) d hv0
  let a : State 8 64 := ⟨r0,Function.update d.stacks 20 w0⟩
  have hv1 : Valid (arithmeticPorts 1) a := by
    constructor
    · simpa [a,arithmeticPorts] using h21
    · intro i
      have hi : arithmeticWork i≠20 := (arithmeticPorts 0).work_ne_out i
      simpa [a,arithmeticPorts,hi] using hw i
  obtain ⟨t1,r1,w1,he1,hv1',hl1,ht1⟩ := addAt_eval (arithmeticPorts 1) a hv1
  have hval : BinaryArithmetic.toNat w1=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) := by
    simpa [a,arithmeticPorts,hv0'] using hv1'
  have hl0' : w0.length ≤ (d.stacks 18).length+(d.stacks 3).length+1 := by
    simpa [arithmeticPorts] using hl0
  have hl1' : w1.length ≤ w0.length+(d.stacks 14).length+1 := by
    simpa [a,arithmeticPorts] using hl1
  have hwidth0 : w0.length ≤ indexWidth d := by dsimp [indexWidth]; omega
  have hwidth1 : w1.length ≤ indexWidth d := by dsimp [indexWidth]; omega
  have ht0' : t0 ≤ 100*(indexWidth d)^2 := by
    apply ht0.trans
    apply Nat.mul_le_mul_left
    apply Nat.pow_le_pow_left
    simp [arithmeticPorts,indexWidth] ; omega
  have ht1' : t1 ≤ 100*(indexWidth d)^2 := by
    have hb : w0.length+(d.stacks 14).length+1 ≤ indexWidth d := by
      dsimp [indexWidth]
      omega
    have hh : t1 ≤ 100*(w0.length+(d.stacks 14).length+1)^2 := by
      simpa [a,arithmeticPorts] using ht1
    exact hh.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hb 2))
  exact ⟨t0+t1,r1,w0,w1,he0.seq he1,hval,hwidth0,hwidth1,by omega⟩

theorem low8_injective : Function.Injective low8 := Fin.castAdd_injective _ _

theorem index_eval (d : Data) (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[])
    (hw : ∀ i, d.stacks (arithmeticWork i)=[]) :
    ∃ n rf product idx, Eval (liftArithmetic indexArithmetic) n d
      ⟨rf,Function.update (Function.update d.stacks 20 product) 21 idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (d.stacks 18)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      product.length ≤ indexWidth (projectState low8 id d) ∧
      idx.length ≤ indexWidth (projectState low8 id d) ∧
      n ≤ 200*(indexWidth (projectState low8 id d))^2+1 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  obtain ⟨n,rr,product,idx,he,hvalue,hproduct,hidx,hcost⟩ :=
    indexArithmetic_eval (projectState low8 id d) h20 h21 hw
  let small : State 8 64 := ⟨rr,Function.update (Function.update d.stacks 20 product) 21 idx⟩
  let out := embedState low8 id d small
  have he' := eval_liftCommand_from_state indexArithmetic 0 0 low8 id d
    low8_injective Function.injective_id he
  have hout : out=⟨out.regs,Function.update (Function.update d.stacks 20 product) 21 idx⟩ := by
    apply congrArg (StructuredProgram.State.mk _)
    funext i
    exact Function.injective_id.extend_apply _ _ i
  change Eval (liftArithmetic indexArithmetic) (n+1) d out at he'
  rw [hout] at he'
  refine ⟨n+1,out.regs,product,idx,he',hvalue,hproduct,hidx,by omega,?_⟩
  intro i hi
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

theorem copied_register (src dst : Fin 64) (d : Data) (i : Fin 16)
    (hi : 2 ≤ i.val) : (copied src dst d).regs i=d.regs i := by
  have h0 : i≠0 := by intro h; subst i; simp at hi
  have h1 : i≠1 := by intro h; subst i; simp at hi
  simp [copied,readRegs,h0,h1]

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramShiftCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem shiftStacks_injective : Function.Injective shiftStacks := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [shiftStacks]

theorem shiftVertex_eval (d : Data) (pairs : List (Bool × Bool)) (tail : List Bool)
    (hsource : d.stacks 1=Shift.frames (pairs.map Prod.snd)++tail)
    (hvertex : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[])
    (h19 : d.stacks 19=[]) (h24 : d.stacks 24=[]) :
    ∃ rf, Eval shiftVertex (21*pairs.length+12) d
      ⟨rf,Function.update (Function.update d.stacks 1 tail) 18
        (Shift.result (d.regs 12) pairs)⟩ ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=d.regs i) := by
  have hc := copy_eval 2 17 d (by decide) (by decide) (by decide) h24
  let d0 := copied 2 17 d
  let d1 : Data := ⟨Function.update d0.regs 7 (d0.regs 12),d0.stacks⟩
  have hs : Eval (.base (.atom (.copy 7 12))) 1 d0 d1 := .base (.atom _ _)
  have hside : (d1.regs ∘ low8) 7=d.regs 12 := by simp [d1,d0,copied,readRegs,low8]
  obtain ⟨rr,hr,he⟩ := Shift.command_eval pairs (d.regs 12) (d1.regs ∘ low8) hside tail
  let a := Shift.state (d1.regs ∘ low8) (Shift.frames (pairs.map Prod.snd)++tail)
    (pairs.map Prod.fst) [] []
  let b := Shift.state rr tail [] [] (Shift.result (d.regs 12) pairs)
  have hin : embedState low8 shiftStacks d1 a=d1 := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective shiftStacks_injective
    · intro i; rfl
    · intro i hi; rfl
    · intro i
      fin_cases i <;> simp [a,Shift.state,shiftStacks,d1,d0,copied,StackRoutines.copyStacks,
        hsource,hvertex,h17,h18,h19]
    · intro i hi; rfl
  let rf := Function.extend low8 rr d1.regs
  have hout : embedState low8 shiftStacks d1 b=
      (⟨rf,Function.update (Function.update d.stacks 1 tail) 18
        (Shift.result (d.regs 12) pairs)⟩ : Data) := by
    apply embedState_eq_of_ports _ _ _ _ _ low8_injective shiftStacks_injective
    · intro i; exact low8_injective.extend_apply rr d1.regs i
    · intro i hi; exact Function.extend_apply' _ _ _ hi
    · intro i; fin_cases i <;> simp [b,Shift.state,shiftStacks,h17,h19]
    · intro i hi
      have h1i : i≠1 := fun h => hi ⟨0,by simpa [shiftStacks] using h.symm⟩
      have h17i : i≠17 := fun h => hi ⟨1,by simpa [shiftStacks] using h.symm⟩
      have h18i : i≠18 := fun h => hi ⟨3,by simpa [shiftStacks] using h.symm⟩
      simp [d1,d0,copied,StackRoutines.copyStacks,h1i,h17i,h18i]
  have ht : Trace Shift.program (14*pairs.length+6)
      (a.withPC (some Shift.program.entry)) (b.withPC none) := by
    convert compiled_halt_trace he 0 3 using 1 <;> rfl
  have hl := eval_call_lifted Shift.program low8 shiftStacks d1
    low8_injective shiftStacks_injective ht
  rw [hin,hout] at hl
  refine ⟨rf,?_,?_⟩
  · convert hc.seq (hs.seq hl) using 1
    all_goals try with_reducible_and_instances rfl
    simp [hvertex] ; omega
  · intro i hi
    have hframe : rf i=d1.regs i := by
      apply Function.extend_apply'
      rintro ⟨j,hj⟩
      have hv := congrArg Fin.val hj
      have hjlt := j.isLt
      dsimp [low8] at hv
      omega
    rw [hframe]
    have h7i : i≠7 := by
      intro h
      subst i
      change 8 ≤ 7 at hi
      omega
    simpa [d1,h7i] using copied_register 2 17 d i (by omega)

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_CodeRowsProgramPrepare
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.CodeRowsProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.BinaryArithmetic

theorem preparePort_eval_oai (d : Data) (a b : Bool) (qt st : List Bool)
    (pairs : List (Bool × Bool))
    (hq : d.stacks 0=Cell.frame a b++qt)
    (hs : d.stacks 1=Shift.frames (pairs.map Prod.snd)++st)
    (hv : d.stacks 2=pairs.map Prod.fst)
    (h17 : d.stacks 17=[]) (h18 : d.stacks 18=[]) (h19 : d.stacks 19=[])
    (h20 : d.stacks 20=[]) (h21 : d.stacks 21=[]) (h24 : d.stacks 24=[])
    (ha : ∀ i, d.stacks (arithmeticWork i)=[])
    (hc : ∀ i : Fin 8, 2 ≤ i.val → d.stacks (compareStacks i)=[]) :
    ∃ n rf product idx, Eval preparePort n d
      ⟨rf,preparedStacks d qt st (Shift.result (d.regs 12) pairs) product idx⟩ ∧
      BinaryArithmetic.toNat idx=BinaryArithmetic.toNat (Shift.result (d.regs 12) pairs)*BinaryArithmetic.toNat (d.stacks 3)+BinaryArithmetic.toNat (d.stacks 14) ∧
      (rf 7=true ↔ BinaryArithmetic.toNat idx < BinaryArithmetic.toNat (d.stacks 4)) ∧
      product.length ≤ portWidth d ∧ idx.length ≤ portWidth d ∧
      n ≤ 600*(portWidth d)^2 ∧
      (∀ i : Fin 16, 8 ≤ i.val → rf i=coefficientRegs d.regs a b i) := by
  have e0 := readCoefficient_eval d a b qt hq
  let d0 : Data := ⟨coefficientRegs d.regs a b,Function.update d.stacks 0 qt⟩
  obtain ⟨r1,e1,f1⟩ := shiftVertex_eval d0 pairs st
    (by simpa [d0] using hs) (by simpa [d0] using hv)
    (by simpa [d0] using h17) (by simpa [d0] using h18)
    (by simpa [d0] using h19) (by simpa [d0] using h24)
  have hm : d0.regs 12=d.regs 12 := by simp [d0,coefficientRegs]
  rw [hm] at e1
  let shifted := Shift.result (d.regs 12) pairs
  let d1 : Data := ⟨r1,Function.update (Function.update d0.stacks 1 st) 18 shifted⟩
  have ha1 : ∀ i, d1.stacks (arithmeticWork i)=[] := by
    intro i
    have h := ha i
    have hi0 : arithmeticWork i ≠ (0 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 0 at hv
      omega
    have hi1 : arithmeticWork i ≠ (1 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 1 at hv
      omega
    have hi18 : arithmeticWork i ≠ (18 : Fin 64) := by
      intro he
      have hv := congrArg Fin.val he
      change 28 + i.val = 18 at hv
      omega
    simpa [d1, d0, hi0, hi1, hi18] using h
  obtain ⟨n2,r2,product,idx,e2,v2,lprod,lidx,b2,f2⟩ := index_eval d1
    (by simpa [d1,d0] using h20) (by simpa [d1,d0] using h21) ha1
  let d2 : Data := ⟨r2,Function.update (Function.update d1.stacks 20 product) 21 idx⟩
  have hc2 : ∀ i : Fin 8, 2 ≤ i.val → d2.stacks (compareStacks i)=[] := by
    intro i hi
    have h := hc i hi
    fin_cases i <;> simp_all [d2,d1,d0,compareStacks]
  obtain ⟨r3,e3,flag3,f3⟩ := belowClauseCount_eval d2 hc2
  have hpairs : pairs.length=(d.stacks 2).length := by rw [hv]; simp
  have hiwidth : indexWidth (projectState low8 id d1) ≤ portWidth d := by
    simp [indexWidth,projectState,d1,d0,shifted,Shift.result,portWidth,hpairs] ; omega
  have hprod : product.length ≤ portWidth d := lprod.trans hiwidth
  have hidx : idx.length ≤ portWidth d := lidx.trans hiwidth
  have hnv : n2 ≤ 200*(portWidth d)^2+1 := by
    apply b2.trans
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hiwidth 2)) _
  let n := 6+(21*pairs.length+12+(n2+
    (52*((d2.stacks 21).length+(d2.stacks 4).length)+54)))
  refine ⟨n,r3,product,idx,e0.seq (e1.seq (e2.seq e3)),?_,?_,hprod,hidx,?_,?_⟩
  · simpa [d1,d0,shifted] using v2
  · simpa [d2,d1,d0] using flag3
  · have hW : 3 ≤ portWidth d := by dsimp [portWidth]; omega
    have hpW : pairs.length ≤ portWidth d := by rw [hpairs]; dsimp [portWidth]; omega
    have hmW : (d.stacks 4).length ≤ portWidth d := by dsimp [portWidth]; omega
    dsimp [n]
    simp only [d2,d1,d0,Function.update_same,
      Function.update_noteq (by decide : (4 : Fin 64)≠21),
      Function.update_noteq (by decide : (4 : Fin 64)≠20),
      Function.update_noteq (by decide : (4 : Fin 64)≠18),
      Function.update_noteq (by decide : (4 : Fin 64)≠1),
      Function.update_noteq (by decide : (4 : Fin 64)≠0)]
    nlinarith only [hW,hpW,hmW,hnv,hidx]
  · intro i hi
    exact (f3 i hi).trans ((f2 i hi).trans (f1 i hi))

end SubexponentialSAT.SqrtLog.CodeRowsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.CodeRowsProgram.preparePort_eval_oai
