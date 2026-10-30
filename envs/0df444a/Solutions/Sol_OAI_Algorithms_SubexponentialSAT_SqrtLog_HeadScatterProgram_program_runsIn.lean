-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:24:13.818994+00:00
-- url     : https://prove2.me/submissions/bb451d9f-2bf5-43ed-a649-95cf09649216

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S065
import Definitions.Def_OAIQ081S073
import Definitions.Def_OAIQ081S083
import Definitions.Def_OAIQ081S085

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_StackRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-alphabet stack routines

This module records stack-state transformations and proves instruction traces
for concrete programs over Boolean stacks. The number of symbols in a stack is
runtime data; no growing alphabet is used.
-/

namespace SubexponentialSAT.StackRoutines

universe u

theorem clearStacks_frame {S : Type u} [DecidableEq S] (src j : S) (stk : Stacks S)
    (hj : j ≠ src) : clearStacks src stk j = stk j := by
  simp [clearStacks, hj]

open BitProgram

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_BankRoutines
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed finite banks of stack-copy and stack-clear routines

The port lists below are part of the finite program syntax.  Word contents and
word lengths remain runtime inputs.  Each call is justified by an actual trace
of the existing stack routine, including its return instruction.  A final clear
of an already empty temporary gives a uniform reset of the two read registers,
including when the port list is empty.
-/

namespace SubexponentialSAT.BankRoutines

open BitProgram StackRoutines StructuredCalls

universe u

theorem clearBankStacks_cons {S : Type u} [DecidableEq S]
    (dst : S) (ports : List S) (stk : Stacks S) :
    clearBankStacks ports (clearStacks dst stk) =
      clearBankStacks (dst :: ports) stk := by
  funext j
  by_cases hj : j = dst
  · subst j
    simp [clearBankStacks]
  · simp [clearBankStacks, clearStacks, hj]

theorem clear_call_eval {r s : ℕ} (src : Fin s) (value present : Fin r)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) :
    Eval (.call (clearProgram src value present)) (2 * (stk src).length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearStacks src stk⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run src value present regs stk

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime scatter of head bits into the original ambient coordinate order.
Coordinate identifiers are framed unary words; array replacement is a genuine
runtime scan. No coordinate permutation is compiled into the instruction table. -/
namespace SubexponentialSAT.SqrtLog.HeadScatterProgram

open SubexponentialSAT BitProgram StructuredCalls Subexp.MatrixProgramSupport

theorem arrayPorts_injective : Function.Injective arrayPorts := by decide

theorem write_length (mask : List Bool) (j : ℕ) (bit : Bool) (hj : j < mask.length) :
    (write mask j bit).length = mask.length := by
  simp [write, List.length_take, List.length_drop, Nat.min_eq_left hj.le]
  omega

theorem scatterStep_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (j : ℕ) (js : List ℕ) (bit : Bool) (bits mask : List Bool) (hj : j < mask.length) :
    ∃ rf, Eval scatterStep (30*j+53)
      (state regs saved (j::js) (bit::bits) mask)
      (state rf saved js bits (write mask j bit)) := by
  let d := state regs saved (j::js) (bit::bits) mask
  let d0 : Data := ⟨readRegs d.regs 0 1 (some true),
    Function.update d.stacks 2 (Encoding.frame (unary j) ++ indices js)⟩
  have htag : Eval popIndexTag 1 d d0 := by
    simpa [popIndexTag,d0,d,state,indices,ProgramEncoding.encodeRecords,Encoding.encodeList,
      StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.pop (2 : Fin 13) (0 : Fin 8) 1) d))
  obtain ⟨a, ha, hsa⟩ := readFrame_eval (2 : Fin 13) 3 (by decide) d0
    (unary j) (indices js) (by simp [d0]) (by simp [d0,d,state])
  let b : Data := ⟨readRegs a.regs 0 1 (some bit), Function.update a.stacks 1 bits⟩
  have hb : Eval popBit 1 a b := by
    have hs : a.stacks 1 = bit::bits := by rw [hsa]; rfl
    simpa [popBit,b,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hs] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.pop (1 : Fin 13) (0 : Fin 8) 1) a))
  let c : Data := ⟨b.regs, Function.update b.stacks 4 [bit]⟩
  have hc : Eval pushBit 1 b c := by
    have hs : a.stacks 4 = [] := by simp [hsa,d0,d,state]
    simpa [pushBit,c,b,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,StructuredProgram.State.withPC,execInstr,hs,readRegs] using
      (Eval.base (StructuredProgram.Eval.atom
        (StructuredProgram.Atom.push (4 : Fin 13) (0 : Fin 8)) b))
  let earlier := (mask.take j).map (fun x => [x])
  have hearly : earlier.flatten = mask.take j := by
    change ((mask.take j).map (fun x => [x])).flatten = mask.take j
    induction mask.take j with
    | nil => rfl
    | cons x xs ih => simpa only [List.map_cons,List.flatten_cons,List.singleton_append] using congrArg (List.cons x) ih
  have helen : earlier.length = j := by
    simp [earlier,List.length_take,Nat.min_eq_left hj.le]
  have hsplit : mask = earlier.flatten ++ ([mask[j]] ++ mask.drop (j+1)) := by
    rw [hearly]
    have h := List.take_append_drop j mask
    rw [List.drop_eq_getElem_cons hj] at h
    simp
  let v := projectState id arrayPorts c
  have hrep := ArrayUpdatePrograms.replaceProgram_trace (0 : Fin 8) 1 (by decide)
    earlier [mask[j]] [bit] (mask.drop (j+1)) [true] (unary j) v.regs v.stacks
    (by simpa [v,projectState,arrayPorts,c,b,hsa,d0,d,state] using hsplit)
    (by simp [v,projectState,arrayPorts,c])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state,unary])
    (by simp [helen,unary])
    (by intro row hr; obtain ⟨x,_,rfl⟩ := List.mem_map.mp hr; rfl)
    rfl rfl
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
    (by simp [v,projectState,arrayPorts,c,b,hsa,d0,d,state])
  let out : State 8 8 := ⟨readRegs v.regs 0 1 none,
    ArrayUpdatePrograms.replaceStacks earlier [bit] (mask.drop (j+1)) v.stacks⟩
  have hr := eval_call_from_state (ArrayUpdatePrograms.replaceProgram (0 : Fin 8) 1)
    id arrayPorts c Function.injective_id arrayPorts_injective (b := out) hrep
  let e : Data := ⟨readRegs c.regs 0 1 none,
    Function.update (Function.update c.stacks 0 (write mask j bit)) 3 []⟩
  have hout : embedState id arrayPorts c out = e := by
    apply embedState_eq_of_ports id arrayPorts c e out
      Function.injective_id arrayPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;>
        simp [e,out,v,projectState,arrayPorts,ArrayUpdatePrograms.replaceStacks,write,hearly]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [arrayPorts] using h.symm⟩
      have h3 : i ≠ 3 := fun h => hi ⟨2,by simpa [arrayPorts] using h.symm⟩
      simp [e,h0,h3]
  rw [hout] at hr
  have hclear := StackRoutines.clearProgram_trace (4 : Fin 13) (0 : Fin 8) 1 e.regs e.stacks
  have hh := StackRoutines.halt_after_trace _ hclear 2 rfl rfl
  let f : Data := ⟨readRegs e.regs 0 1 none, StackRoutines.clearStacks 4 e.stacks⟩
  have hf : Eval clearBit (2*(e.stacks 4).length+3) e f := by
    apply Eval.call
    simpa [clearBit,f,StackRoutines.clearResult,StructuredProgram.State.withPC,
      StackRoutines.clearProgram,Nat.add_assoc] using hh
  have hfinal : f = state f.regs saved js bits (write mask j bit) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i; fin_cases i <;> simp [e,c,b,hsa,d0,d,state,StackRoutines.clearStacks]
  rw [hfinal] at hf
  refine ⟨f.regs, ?_⟩
  have he := htag.seq (ha.seq (hb.seq (hc.seq (hr.seq hf))))
  convert he using 1 <;> simp [scatterStep,replaceBit,helen,unary,e,c] ; omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem zeroTrace (count : List Bool) (regs : Fin 8 → Bool) (stk : Fin 13 → List Bool)
    (hc : stk 3=count) :
    Trace zeroProgram (4*count.length+2) ⟨some 0,regs,stk⟩
      ⟨some 4,readRegs regs 0 1 none,zeroStacks count.length stk⟩ := by
  induction count generalizing regs stk with
  | nil =>
      refine .cons (b := ⟨some 1,readRegs regs 0 1 none,Function.update stk 3 []⟩) ?_ ?_
      · simp [step,execInstr,hc]
      · refine .cons (b := ⟨some 4,readRegs regs 0 1 none,zeroStacks 0 stk⟩) ?_ (.refl _)
        simp [step,execInstr,readRegs,zeroStacks]
  | cons bit rest ih =>
      let r1 := readRegs regs 0 1 (some bit)
      let r2 := Function.update r1 0 false
      let s1 := Function.update stk 3 rest
      let s2 := Function.update s1 0 (false::stk 0)
      have ht := ih r2 s2 (by simp [s2,s1])
      have hr : readRegs r2 0 1 none=readRegs regs 0 1 none := by
        funext i; fin_cases i <;> simp [r2,r1,readRegs]
      have hs : zeroStacks rest.length s2=zeroStacks (bit::rest).length stk := by
        funext i; fin_cases i <;> simp [zeroStacks,s2,s1,List.replicate_succ',List.append_assoc]
      rw [hr,hs] at ht
      have he : Trace zeroProgram (4*rest.length+2+4) ⟨some 0,regs,stk⟩
          ⟨some 4,readRegs regs 0 1 none,zeroStacks (bit::rest).length stk⟩ := by
        refine .cons (b := ⟨some 1,r1,s1⟩) ?_ ?_
        · simp [step,execInstr,hc,r1,s1]
        · refine .cons (b := ⟨some 2,r1,s1⟩) ?_ ?_
          · simp [step,execInstr,r1,readRegs]
          · refine .cons (b := ⟨some 3,r2,s1⟩) ?_ ?_
            · simp [step,execInstr,r2]
            · refine .cons (b := ⟨some 0,r2,s2⟩) ?_ ht
              simp [step,execInstr,r2,s2,s1]
      convert he using 1
      all_goals try with_reducible_and_instances rfl

theorem zero_eval (d : Data) :
    Eval (.call zeroProgram) (4*(d.stacks 3).length+3) d
      ⟨readRegs d.regs 0 1 none,zeroStacks (d.stacks 3).length d.stacks⟩ := by
  apply Eval.call
  have ht := zeroTrace (d.stacks 3) d.regs d.stacks rfl
  have hh := StackRoutines.halt_after_trace _ ht 4 rfl rfl
  simpa [StructuredProgram.State.withPC,zeroProgram,Nat.add_assoc] using hh

theorem initCommand_eval (regs : Fin 8 → Bool) (js : List ℕ) (bits : List Bool) (n : ℕ) :
    ∃ rf, Eval initCommand (initCost js bits n) (input regs js bits n)
      (state rf (savedInputs js bits n) js bits (List.replicate n false)) := by
  let d := input regs js bits n
  have h1 := SubexpScanPrimitives.copy_eval d 10 2 3 0 1
    (by decide) (by decide) (by decide) (by decide) rfl
  let a := SubexpScanPrimitives.afterCopy d 10 2 0 1
  have h2 := SubexpScanPrimitives.copy_eval a 11 1 3 0 1
    (by decide) (by decide) (by decide) (by decide) (by simp [a,SubexpScanPrimitives.afterCopy,d,input,StackRoutines.copyStacks])
  let b := SubexpScanPrimitives.afterCopy a 11 1 0 1
  have h3 := SubexpScanPrimitives.copy_eval b 12 3 4 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [b,a,SubexpScanPrimitives.afterCopy,d,input,StackRoutines.copyStacks])
  let c := SubexpScanPrimitives.afterCopy b 12 3 0 1
  have h4 := zero_eval c
  let e : Data := ⟨readRegs c.regs 0 1 none,zeroStacks (c.stacks 3).length c.stacks⟩
  have h5 := Subexp.TupleProgram.pushConst_eval (5 : Fin 13) (0 : Fin 8) true e
  let f := Subexp.TupleProgram.pushedState (5 : Fin 13) (0 : Fin 8) true e
  have hf : f=state f.regs (savedInputs js bits n) js bits (List.replicate n false) := by
    apply congrArg (StructuredProgram.State.mk f.regs)
    funext i; fin_cases i <;>
      simp [e,c,b,a,d,input,savedInputs,
        zeroStacks,SubexpScanPrimitives.afterCopy,StackRoutines.copyStacks,unary]
  change Eval _ _ e f at h5
  rw [hf] at h5
  refine ⟨f.regs, ?_⟩
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  convert he using 1 <;>
    simp [initCommand,initCost,c,b,a,d,input,SubexpScanPrimitives.afterCopy,
      StackRoutines.copyStacks,unary] ; omega

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem peekBits_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool) :
    Eval peekBits 1 (state regs saved js bits mask) (ready regs saved js bits mask) := by
  exact Eval.base (StructuredProgram.Eval.atom _ _)

theorem scanLoop_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js, j < mask.length) :
    ∃ rf, Eval scanLoop (scanCost js) (ready regs saved js bits mask)
      (state rf saved [] [] (scatter js bits mask)) := by
  induction js generalizing regs bits mask with
  | nil =>
      have he : bits=[] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst bits
      refine ⟨readRegs regs 0 1 none, ?_⟩
      exact Eval.while_false (by simp [ready,state,readRegs])
  | cons j js ih =>
      cases bits with
      | nil => simp at hlen
      | cons b bits =>
          have hj := hb j (by simp)
          obtain ⟨rs,hs⟩ := scatterStep_eval (readRegs regs 0 1 (some b)) saved
            j js b bits mask hj
          have hw := write_length mask j b hj
          obtain ⟨rf,hf⟩ := ih rs bits (write mask j b)
            (by simpa using hlen) (by intro k hk; rw [hw]; exact hb k (by simp [hk]))
          have hbody := hs.seq (peekBits_eval rs saved js bits (write mask j b))
          have he := Eval.while_true (show (ready regs saved (j::js) (b::bits) mask).regs 1=true
            by simp [ready,state,readRegs]) hbody hf
          refine ⟨rf, ?_⟩
          convert he using 1 <;> simp [scanLoop,scanBody,scanCost,scatter] ; omega

theorem scanCommand_eval (regs : Fin 8 → Bool) (saved : Fin 3 → List Bool)
    (js : List ℕ) (bits mask : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js, j < mask.length) :
    ∃ rf, Eval scanCommand (scanCost js+1) (state regs saved js bits mask)
      (state rf saved [] [] (scatter js bits mask)) := by
  obtain ⟨rf,he⟩ := scanLoop_eval regs saved js bits mask hlen hb
  exact ⟨rf, by simpa [scanCommand,Nat.add_comm] using (peekBits_eval regs saved js bits mask).seq he⟩

theorem scanCost_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    scanCost js ≤ js.length*(30*n+55)+1 := by
  induction js with
  | nil => simp [scanCost]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [scanCost,List.length_cons]
      nlinarith

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_WorkspaceCleanupProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual fixed workspace cleanup

The selected ports are part of the finite program. Their initial contents
and lengths are arbitrary. Every clear is an existing measured instruction
loop, and all unselected stacks and non-scratch registers are preserved.
-/

namespace SubexponentialSAT.WorkspaceCleanupProgram

open BitProgram StackRoutines StructuredCalls

theorem finalRegs_after_reset {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (regs : Fin r → Bool) :
    finalRegs value present ports (readRegs regs value present none) =
      readRegs regs value present none := by
  cases ports <;> simp [finalRegs, readRegs_reset]

theorem command_eval {r s : ℕ} (value present : Fin r) (ports : List (Fin s))
    (hnodup : ports.Nodup) (d : State r s) :
    Eval (command value present ports) (cost ports d) d (finish value present ports d) := by
  rcases d with ⟨regs, stk⟩
  induction ports generalizing regs stk with
  | nil =>
      simpa [command, cost, finish, finalRegs] using
        (Eval.base (StructuredProgram.Eval.skip (⟨regs, stk⟩ : State r s)))
  | cons port rest ih =>
      have hn := List.nodup_cons.mp hnodup
      have hmap : rest.map (fun i => (clearStacks port stk i).length) =
          rest.map (fun i => (stk i).length) := by
        apply List.map_congr_left
        intro i hi
        have hne : i ≠ port := by
          intro h
          subst i
          exact hn.1 hi
        rw [clearStacks_frame port i stk hne]
      have hfirst := BankRoutines.clear_call_eval port value present regs stk
      have hrest := ih hn.2 (readRegs regs value present none) (clearStacks port stk)
      have hrun := Eval.seq hfirst hrest
      simpa only [command, cost, finish, finalRegs_after_reset, finalRegs_cons,
        List.map_cons, List.sum_cons, List.length_cons, hmap,
        BankRoutines.clearBankStacks_cons, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrun

end SubexponentialSAT.WorkspaceCleanupProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadScatterProgramRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadScatterProgram
open SubexponentialSAT BitProgram StructuredCalls

theorem command_eval (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, Eval command (totalCost n js bits-1) (input regs js bits n) (result rf js bits n) := by
  obtain ⟨ra,ha⟩ := initCommand_eval regs js bits n
  obtain ⟨rb,hb'⟩ := scanCommand_eval ra (savedInputs js bits n) js bits
    (List.replicate n false) hlen (by simpa using hb)
  let b := state rb (savedInputs js bits n) [] [] (mask n js bits)
  let rf := readRegs rb 0 1 none
  have hf : Eval finishWidth 10 b (result rf js bits n) := by
    have h := WorkspaceCleanupProgram.command_eval (0 : Fin 8) 1
      ([2,5] : List (Fin 13)) (by decide) b
    convert h using 1 <;>
      simp [finishWidth,WorkspaceCleanupProgram.cost,b,state,indices,
        ProgramEncoding.encodeRecords,Encoding.encodeList,result,rf,savedInputs]
    apply congrArg (StructuredProgram.State.mk _)
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  refine ⟨rf, ?_⟩
  have he := ha.seq (hb'.seq hf)
  convert he using 1 <;> simp [command,totalCost] ; omega

theorem indices_length_bound (n : ℕ) (js : List ℕ) (hb : ∀ j ∈ js,j < n) :
    (indices js).length ≤ js.length*(2*n+2)+1 := by
  induction js with
  | nil => simp [indices,ProgramEncoding.encodeRecords,Encoding.encodeList]
  | cons j js ih =>
      have hj := hb j (by simp)
      have ht := ih (by intro k hk; exact hb k (by simp [hk]))
      simp only [indices,List.map_cons,ProgramEncoding.encodeRecords,Encoding.encodeList,
        List.length_cons,List.length_append,Encoding.length_frame, id_eq, unary,List.length_replicate]
      change 2*j+1+(indices js).length+1 ≤ (js.length+1)*(2*n+2)+1
      nlinarith

theorem totalCost_polynomial (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    totalCost n js bits ≤ 100*(n+1)*(js.length+1) := by
  have hi := indices_length_bound n js hb
  have hs := scanCost_bound n js hb
  unfold totalCost initCost
  rw [← hlen]
  nlinarith

theorem program_runsIn_oai (regs : Fin 8 → Bool) (n : ℕ) (js : List ℕ) (bits : List Bool)
    (hlen : js.length=bits.length) (hb : ∀ j ∈ js,j < n) :
    ∃ rf, RunsIn program (100*(n+1)*(js.length+1))
      ((input regs js bits n).withPC (some program.entry))
      ((result rf js bits n).withPC none) := by
  obtain ⟨rf,he⟩ := command_eval regs n js bits hlen hb
  refine ⟨rf,totalCost n js bits-1+1,?_,compiled_halt_trace he 10 0⟩
  have hpos : 1 ≤ totalCost n js bits := by unfold totalCost; omega
  rw [Nat.sub_add_cancel hpos]
  exact totalCost_polynomial n js bits hlen hb

end SubexponentialSAT.SqrtLog.HeadScatterProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadScatterProgram.program_runsIn_oai
