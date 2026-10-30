-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T05:45:29.155518+00:00
-- url     : https://prove2.me/submissions/0ede93c5-6fa4-4c36-aa0a-dfeae27ae2e2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S119
import Definitions.Def_OAIQ081S137

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHeadColorProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Read a head color from its physical one-hot type encoding

Ports 0, 1, and 2 hold the flat type bytes, unary position, and unary color
width. The fixed array reader preserves these inputs. A five-label bit loop
counts the false prefix of the selected one-hot word; the remaining suffix is
cleared. Only output port 3 changes, and scratch ports 4--9 are restored.
-/

namespace SubexponentialSAT.SubexpHeadColorProgram

open BitProgram StructuredCalls SubexpScanPrimitives
open Subexp.AssignmentAlphabetSemantics

theorem readPorts_injective : Function.Injective readPorts := by decide

theorem select_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hsource : d.stacks 0 = earlier.flatten ++ (word ++ rest))
    (hindex : (d.stacks 1).length = earlier.length)
    (hwidth : word.length = (d.stacks 2).length)
    (hrows : ∀ row ∈ earlier, row.length = (d.stacks 2).length) (hclean : Clean d) :
    Eval select
      (earlier.length * (14*(d.stacks 2).length+17) + 15*(d.stacks 2).length+21)
      d (selected d word) := by
  have h4 := hclean 4 (by simp)
  have h5 := hclean 5 (by simp)
  have h6 := hclean 6 (by simp)
  have h7 := hclean 7 (by simp)
  have h8 := hclean 8 (by simp)
  have h9 := hclean 9 (by simp)
  let b := afterCopy d 1 4 0 1
  have hc := copy_eval d 1 4 6 0 1 (by decide) (by decide) (by decide) (by decide) h6
  let a := projectState id readPorts b
  have hs : a.stacks 0 = earlier.flatten ++ (word ++ rest) := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using hsource
  have hw : a.stacks 3 = d.stacks 2 := by rfl
  have hi : a.stacks 2 = d.stacks 1 := by
    simp [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks,h4]
  have hca : a.stacks 4 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h6
  have hta : a.stacks 5 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h7
  have hba : a.stacks 6 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h8
  have hpa : a.stacks 7 = [] := by
    simpa [a,b,projectState,readPorts,afterCopy,StackRoutines.copyStacks] using h9
  have ht := ArrayUpdatePrograms.readProgram_trace (0 : Fin 5) 1 (by decide)
    earlier word rest (d.stacks 2) (d.stacks 1) a.regs a.stacks
    hs hw hi hindex hrows hwidth hca hta hba hpa
  let z : State 5 8 :=
    ⟨readRegs a.regs 0 1 none,ArrayUpdatePrograms.readStacks word a.stacks⟩
  have hr := eval_call_from_state (ArrayUpdatePrograms.readProgram (0 : Fin 5) 1)
    id readPorts b Function.injective_id readPorts_injective (b := z) ht
  have hz : embedState id readPorts b z = selected d word := by
    apply embedState_eq_of_ports id readPorts b (selected d word) z
      Function.injective_id readPorts_injective
    · intro i
      simp [selected,z,a,b,projectState,afterCopy,StackRoutines.readRegs_reset]
    · intro i hi
      exact False.elim (hi ⟨i,rfl⟩)
    · intro i; fin_cases i <;>
        simp [selected,z,a,b,projectState,afterCopy,StackRoutines.copyStacks,
          ArrayUpdatePrograms.readStacks,readPorts,h4,h5]
    · intro i hi
      have h4' : i ≠ 4 := fun h => hi ⟨2,by simpa [readPorts] using h.symm⟩
      have h5' : i ≠ 5 := fun h => hi ⟨1,by simpa [readPorts] using h.symm⟩
      simp [selected,b,afterCopy,StackRoutines.copyStacks,h4',h5']
  rw [hz] at hr
  have he := hc.seq hr
  have hn : (7*(d.stacks 1).length+5)+
      (earlier.length*(14*(d.stacks 2).length+10)+15*(d.stacks 2).length+16) =
      earlier.length*(14*(d.stacks 2).length+17)+15*(d.stacks 2).length+21 := by
    rw [hindex]
    ring
  simpa only [select,copyIndex,readCell,hn] using he

end SubexponentialSAT.SubexpHeadColorProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_TypeBitProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A fixed seven-label routine reads a runtime-indexed bit and clears its
two inputs. An out-of-range read returns false, as `List.getD` does. -/

namespace SubexponentialSAT.Subexp.TypeBitProgram

open BitProgram

theorem cost_le (index bits : List Bool) : cost index bits ≤ 3 * index.length + 2 * bits.length + 6 := by
  induction index generalizing bits with
  | nil => simp only [cost,List.length_nil,Nat.mul_zero,Nat.zero_add,List.length_tail]; omega
  | cons b index ih =>
      have h := ih bits.tail
      have ht : bits.tail.length ≤ bits.length := by simp only [List.length_tail]; omega
      simp only [cost,List.length_cons]
      omega

theorem trace (index bits : List Bool) (regs : Fin 3 → Bool) :
    Trace program (cost index bits) (cfg (some 0) regs index bits)
      (cfg none (resultRegs (bits.getD index.length false)) [] []) := by
  induction index generalizing bits regs with
  | nil =>
      let r1 := readRegs regs 0 1 none
      let r2 := readRegs r1 2 1 bits.head?
      have ht := StackRoutines.clear_trace program 1 0 1 4 5 6 rfl rfl r2
        (ParserProgram.pair [] bits.tail)
      have hh := StackRoutines.halt_after_trace program ht 6 rfl rfl
      have hf : ⟨none, readRegs r2 0 1 none,
          StackRoutines.clearStacks 1 (ParserProgram.pair [] bits.tail)⟩ =
          cfg none (resultRegs (bits.getD 0 false)) [] [] := by
        apply congrArg₂ (fun (rs : Fin 3 → Bool) (ss : Fin 2 → List Bool) => (⟨none,rs,ss⟩ : Cfg 3 2 7))
        · funext i
          fin_cases i <;> simp [r2,r1,readRegs,resultRegs,List.getD_eq_getElem?_getD]
          cases bits <;> rfl
        · funext i
          fin_cases i <;> simp [StackRoutines.clearStacks,ParserProgram.pair]
      have hh' : Trace program (2 * bits.tail.length + 3) (cfg (some 4) r2 [] bits.tail)
          (cfg none (resultRegs (bits.getD 0 false)) [] []) := by
        simpa only [cfg,StackRoutines.clearResult,ParserProgram.pair,Matrix.cons_val_one,
          Matrix.head_cons, hf, ite_eq_right (by decide : (1 : Fin 2) ≠ 0), Nat.add_assoc] using hh
      have hs : Trace program 3 (cfg (some 0) regs [] bits) (cfg (some 4) r2 [] bits.tail) := by
        refine .cons (b := cfg (some 1) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 3) r1 [] bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      simpa [cost,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.trans hh'
  | cons b index ih =>
      let r1 := readRegs regs 0 1 (some b)
      let r2 := readRegs r1 0 1 bits.head?
      have hs : Trace program 3 (cfg (some 0) regs (b :: index) bits)
          (cfg (some 0) r2 index bits.tail) := by
        refine .cons (b := cfg (some 1) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,ParserProgram.pair]
        refine .cons (b := cfg (some 2) r1 index bits) ?_ ?_
        · simp [step,cfg,execInstr,r1,readRegs]
        refine .cons ?_ (.refl _)
        simp [step,cfg,execInstr,r2,ParserProgram.pair]
      have hg : bits.tail.getD index.length false = bits.getD (b :: index).length false := by
        cases bits <;> simp
      simpa only [cost,hg] using hs.trans (ih bits.tail r2)

end SubexponentialSAT.Subexp.TypeBitProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_SupportSelectionPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed copying, comparison and record emission for support selection. -/

namespace SubexponentialSAT.Subexp.SupportSelectionProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem emit_eval (dst : Fin 64) (h : dst ≠ 34) (d : Data) (v : ℕ)
    (hv : d.stacks 34 = unary v) :
    ∃ e, Eval (emit dst h) (5 * v + 7) d e ∧
      e.stacks = Function.update (Function.update d.stacks 34 []) dst
        (record v ++ d.stacks dst) := by
  let a := TupleProgram.pushedState dst 0 false d
  let b := TupleProgram.escapedState (emitPorts dst h) a
  let e := TupleProgram.pushedState dst 0 true b
  have h1 := TupleProgram.pushConst_eval dst 0 false d
  have h2 := TupleProgram.escape_eval_state (emitPorts dst h) a
  have h3 := TupleProgram.pushConst_eval dst 0 true b
  refine ⟨e, ?_, ?_⟩
  · have he := h1.seq (h2.seq h3)
    change Eval (emit dst h) _ d e at he
    convert he using 1
    all_goals try with_reducible_and_instances rfl
    simp [a, emitPorts, h.symm, hv] ; omega
  · funext j
    by_cases hj : j = dst
    · subst j
      simp [e, b, a,
        emitPorts, h.symm, hv, record, TupleProgram.frame_eq_escaped, List.append_assoc]
    · by_cases hk : j = 34
      · subst j
        simp [e, b, a,
          emitPorts, h.symm]
      · simp [e, b, a,
          emitPorts, hj, hk]

end SubexponentialSAT.Subexp.SupportSelectionProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical head-identifier selection uses the original ambient word array.
No packing-coverage predicate participates in the scan. -/
namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem wordRegs_injective : Function.Injective wordRegs := Fin.castAdd_injective _ _
theorem wordPorts_injective : Function.Injective wordPorts := by decide

theorem lookup_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 39).length=earlier.length)
    (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length)
    (hc : ∀ i ∈ ([16,17,36,18,19,20,21] : List (Fin 64)),d.stacks i=[]) :
    Eval lookup (lookupCost earlier.length (d.stacks 38).length) d (selected d word) := by
  let a := projectState wordRegs wordPorts d
  have hclean : SubexpHeadColorProgram.Clean a := by
    intro i hi
    fin_cases i <;> simp_all [a,projectState,wordPorts]
  have h := SubexpHeadColorProgram.select_eval a earlier word rest
    (by simpa [a,projectState,wordPorts] using hs)
    (by simpa [a,projectState,wordPorts] using hi)
    (by simpa [a,projectState,wordPorts] using hw)
    (by simpa [a,projectState,wordPorts] using hr) hclean
  have hl := eval_liftCommand_from_state SubexpHeadColorProgram.select 0 5 wordRegs wordPorts
    d wordRegs_injective wordPorts_injective h
  have hz : embedState wordRegs wordPorts d (SubexpHeadColorProgram.selected a word)=
      selected d word := by
    apply embedState_eq_of_ports wordRegs wordPorts d _ _ wordRegs_injective wordPorts_injective
    · intro i; fin_cases i <;> simp [SubexpHeadColorProgram.selected,selected,a,projectState,wordRegs,readRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun he => hi ⟨0,by simpa [wordRegs] using he.symm⟩
      have h1 : i ≠ 1 := fun he => hi ⟨1,by simpa [wordRegs] using he.symm⟩
      simp [selected,readRegs,h0,h1]
    · intro i; fin_cases i <;>
        simp [SubexpHeadColorProgram.selected,selected,a,projectState,wordPorts]
    · intro i hi
      have hn : i ≠ 36 := fun he => hi ⟨5,by simpa [wordPorts] using he.symm⟩
      simp [selected,hn]
  rw [hz] at hl
  simpa [lookup,lookupCost,a,projectState,wordPorts,Nat.add_assoc] using hl

theorem bitRegs_injective (low : Bool) : Function.Injective (bitRegs low) := by
  cases low <;> decide
theorem bitPorts_injective (low : Bool) : Function.Injective (bitPorts low) := by
  cases low <;> decide

theorem readBit_eval (d : Data) (low : Bool) :
    Eval (readBit low)
      (Subexp.TypeBitProgram.cost (d.stacks 12) (d.stacks (bitSource low)))
      d (bitResult d low ((d.stacks (bitSource low)).getD (d.stacks 12).length false)) := by
  let a := projectState (bitRegs low) (bitPorts low) d
  let b : State 3 2 :=
    ⟨Subexp.TypeBitProgram.resultRegs ((d.stacks (bitSource low)).getD (d.stacks 12).length false),
      ![[],[]]⟩
  have ht := Subexp.TypeBitProgram.trace (d.stacks 12) (d.stacks (bitSource low)) a.regs
  have ht' : Trace Subexp.TypeBitProgram.program
      (Subexp.TypeBitProgram.cost (d.stacks 12) (d.stacks (bitSource low)))
      (a.withPC (some Subexp.TypeBitProgram.program.entry)) (b.withPC none) := by
    have ha : a.withPC (some Subexp.TypeBitProgram.program.entry)=
        Subexp.TypeBitProgram.cfg (some 0) a.regs (d.stacks 12) (d.stacks (bitSource low)) := by
      apply congrArg (fun ss : Fin 2 → List Bool => (⟨some 0,a.regs,ss⟩ : Cfg 3 2 7))
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
    have hb : b.withPC none=Subexp.TypeBitProgram.cfg none b.regs [] [] := by
      apply congrArg (fun ss : Fin 2 → List Bool => (⟨none,b.regs,ss⟩ : Cfg 3 2 7))
      first | done | (first | done | (funext i; fin_cases i <;> rfl))
    rw [ha,hb]
    exact ht
  have he := eval_call_from_state Subexp.TypeBitProgram.program (bitRegs low) (bitPorts low)
    d (bitRegs_injective low) (bitPorts_injective low) ht'
  have hz : embedState (bitRegs low) (bitPorts low) d b=
      bitResult d low ((d.stacks (bitSource low)).getD (d.stacks 12).length false) := by
    apply embedState_eq_of_ports (bitRegs low) (bitPorts low) d _ _
      (bitRegs_injective low) (bitPorts_injective low)
    · intro i; cases low <;> fin_cases i <;>
        simp [b,Subexp.TypeBitProgram.resultRegs,bitRegs,bitFlag,bitResult,readRegs]
    · intro i hi
      have h0 : i ≠ 0 := fun he => hi ⟨0,by simpa [bitRegs] using he.symm⟩
      have h1 : i ≠ 1 := fun he => hi ⟨1,by simpa [bitRegs] using he.symm⟩
      have hf : i ≠ bitFlag low := fun he => hi ⟨2,by simpa [bitRegs] using he.symm⟩
      simp [bitResult,readRegs,h0,h1,hf]
    · intro i; cases low <;> fin_cases i <;> simp [b,bitPorts,bitSource,bitResult]
    · intro i hi
      have h12 : i ≠ 12 := fun he => hi ⟨0,by simpa [bitPorts] using he.symm⟩
      have hs : i ≠ bitSource low := fun he => hi ⟨1,by simpa [bitPorts] using he.symm⟩
      simp [bitResult,h12,hs]
  rw [hz] at he
  exact he

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem test_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 39).length=earlier.length)
    (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
    Eval test (testCost (d.stacks 39) (d.stacks 31) (d.stacks 32) word (d.stacks 38).length)
      d (tested d ((d.stacks 31).getD (d.stacks 39).length false)
        (word.getD (d.stacks 32).length false)) := by
  have hz12 := hc 12 (by decide)
  have hz13 := hc 13 (by decide)
  have hz36 := hc 36 (by decide)
  have hz42 := hc 42 (by decide)
  let a := afterCopy d 39 12 0 1
  have h1 : Eval (copy 39 12) (7*(d.stacks 39).length+5) d a :=
    copy_eval d 39 12 42 0 1 (by decide) (by decide) (by decide) (by decide) hz42
  let b := afterCopy a 31 13 0 1
  have h2 : Eval (copy 31 13) (7*(d.stacks 31).length+5) a b := by
    have he := copy_eval a 31 13 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [a,afterCopy,StackRoutines.copyStacks,hz42])
    simpa [copy, Subexp.SupportSelectionProgram.copy, b, a, afterCopy,
      StackRoutines.copyStacks] using he
  let c := bitResult b true ((d.stacks 31).getD (d.stacks 39).length false)
  have h3 : Eval (readBit true) (Subexp.TypeBitProgram.cost (d.stacks 39) (d.stacks 31)) b c := by
    simpa [c,b,a,afterCopy,StackRoutines.copyStacks,bitSource,hz12,hz13] using readBit_eval b true
  let e := selected c word
  have h4 : Eval lookup (lookupCost (d.stacks 39).length (d.stacks 38).length) c e := by
    have he := lookup_eval c earlier word rest
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hs)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hi)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hw)
      (by simpa [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks] using hr)
      (by
        intro i hi'
        have hi12 : i ≠ 12 := by intro he; subst i; simp at hi'
        have hi13 : i ≠ 13 := by intro he; subst i; simp at hi'
        simp [c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hi12,hi13,
          hc i (by simp at hi' ⊢; tauto)])
    simpa [e,c,b,a,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hi] using he
  let f := afterCopy e 32 12 0 1
  have h5 : Eval (copy 32 12) (7*(d.stacks 32).length+5) e f := by
    have he := copy_eval e 32 12 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [e,c,b,a,selected,bitResult,bitSource,afterCopy,StackRoutines.copyStacks,hz42])
    simpa [copy, Subexp.SupportSelectionProgram.copy, f, e, c, b, a, selected,
      bitResult, bitSource, afterCopy,
      StackRoutines.copyStacks] using he
  let z := bitResult f false (word.getD (d.stacks 32).length false)
  have h6 : Eval (readBit false) (Subexp.TypeBitProgram.cost (d.stacks 32) word) f z := by
    simpa [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,StackRoutines.copyStacks]
      using readBit_eval f false
  have hz : z=tested d ((d.stacks 31).getD (d.stacks 39).length false)
      (word.getD (d.stacks 32).length false) := by
    apply state_ext
    · funext i; fin_cases i <;>
        simp [z,f,e,c,b,a,selected,bitResult,bitFlag,afterCopy,tested,readRegs]
    · funext i
      by_cases h12 : i=12
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz12]
      by_cases h13 : i=13
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz13]
      by_cases h36 : i=36
      · subst i; simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,hz36]
      · simp [z,f,e,c,b,a,selected,bitResult,bitSource,afterCopy,tested,StackRoutines.copyStacks,h12,h13,h36]
  have he := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  rw [hz] at he
  simpa [test,testCost,Nat.add_assoc] using he

theorem testCost_bound (index low bitIndex word : List Bool) (W : ℕ)
    (hw : word.length=W) :
    testCost index low bitIndex word W ≤ lookupCost index.length W+
      10*index.length+9*low.length+10*bitIndex.length+2*W+27 := by
  have h1 := Subexp.TypeBitProgram.cost_le index low
  have h2 := Subexp.TypeBitProgram.cost_le bitIndex word
  unfold testCost
  omega

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HeadIdentifierProgramVisit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.HeadIdentifierProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem emit_eval (d : Data) (j : ℕ) (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ e, Eval emit (12*j+14) d e ∧
      e.stacks=Function.update (Function.update d.stacks 0 (record j++d.stacks 0))
        1 (false::d.stacks 1) := by
  let a := afterCopy d 39 34 0 1
  have h1 : Eval (copy 39 34) (7*j+5) d a := by
    have he := copy_eval d 39 34 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (hc 42 (by decide))
    simpa [copy,Subexp.SupportSelectionProgram.copy,a,afterCopy,hj] using he
  have ha : a.stacks 34=unary j := by
    simp [a,afterCopy,StackRoutines.copyStacks,hj,hc 34 (by decide)]
  obtain ⟨b,h2,hb⟩ := Subexp.SupportSelectionProgram.emit_eval 0 (by decide) a j ha
  let e := Subexp.TupleProgram.pushedState 1 0 false b
  have h3 := Subexp.TupleProgram.pushConst_eval (1 : Fin 64) (0 : Fin 16) false b
  refine ⟨e,?_,?_⟩
  · have he := h1.seq (h2.seq h3)
    convert he using 1 <;> first | rfl | omega
  · funext i
    by_cases hi : i=34
    · subst i; simp [e,hb,a,afterCopy,StackRoutines.copyStacks,hc 34 (by decide)]
    · simp [e,hb,a,afterCopy,StackRoutines.copyStacks,
        Function.update_apply,hi,record]

theorem choose_eval (d : Data) (j : ℕ) (hj : d.stacks 39=unary j) (hc : Clean d) :
    ∃ ticks e, ticks ≤ 12*j+16 ∧ Eval choose ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if d.regs 6 && d.regs 4 then record j++d.stacks 0 else d.stacks 0))
        1 (if d.regs 6 && d.regs 4 then false::d.stacks 1 else d.stacks 1) := by
  cases hl : d.regs 6 with
  | false =>
      refine ⟨1,d,by omega,Eval.ite_false hl (.base (.skip d)),?_⟩
      simp []
  | true =>
      cases hh : d.regs 4 with
      | false =>
          refine ⟨2,d,by omega,Eval.ite_true hl (Eval.ite_false hh (.base (.skip d))),?_⟩
          simp []
      | true =>
          obtain ⟨e,he,hs⟩ := emit_eval d j hj hc
          refine ⟨12*j+16,e,le_rfl,?_,?_⟩
          · simpa [choose,Nat.add_assoc] using Eval.ite_true hl (Eval.ite_true hh he)
          · simpa [hl,hh] using hs

theorem visit_eval_oai (d : Data) (earlier : List (List Bool)) (word rest : List Bool) (j : ℕ)
    (hs : d.stacks 33=earlier.flatten++(word++rest)) (hj : d.stacks 39=unary j)
    (hi : j=earlier.length) (hw : word.length=(d.stacks 38).length)
    (hr : ∀ row ∈ earlier,row.length=(d.stacks 38).length) (hc : Clean d) :
    ∃ ticks e, ticks ≤ visitBound j (d.stacks 38).length (d.stacks 31).length (d.stacks 32).length ∧
      Eval visit ticks d e ∧
      e.stacks=Function.update (Function.update d.stacks 0
        (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then record j++d.stacks 0 else d.stacks 0))
        1 (if (d.stacks 31).getD j false && word.getD (d.stacks 32).length false
          then false::d.stacks 1 else d.stacks 1) := by
  let a := tested d ((d.stacks 31).getD j false) (word.getD (d.stacks 32).length false)
  have ht : Eval test
      (testCost (d.stacks 39) (d.stacks 31) (d.stacks 32) word (d.stacks 38).length) d a := by
    simpa [a,hj] using test_eval d earlier word rest hs (by simp [hj,hi]) hw hr hc
  obtain ⟨nc,e,hnc,he,hse⟩ := choose_eval a j hj hc
  refine ⟨_,e,?_,ht.seq he,?_⟩
  · have hb := testCost_bound (d.stacks 39) (d.stacks 31) (d.stacks 32) word _ hw
    have hlength : (d.stacks 39).length=j := by simp [hj]
    rw [hlength] at hb
    unfold visitBound
    omega
  · simpa [a,tested,readRegs] using hse

end SubexponentialSAT.SqrtLog.HeadIdentifierProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HeadIdentifierProgram.visit_eval_oai
