-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:11:28.767751+00:00
-- url     : https://prove2.me/submissions/4890554b-9d57-42db-aee4-45b70f3f2b95

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S137
import Definitions.Def_OAIQ081S144

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Factor head selection uses the full original table and a paid ambient offset. -/
namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem wordRegs_injective : Function.Injective wordRegs := Fin.castAdd_injective _ _
theorem wordPorts_injective : Function.Injective wordPorts := by decide

theorem lookup_eval (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33=earlier.flatten++(word++rest))
    (hi : (d.stacks 40).length=earlier.length)
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


end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafHeadFactorsProgramTest
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem address_eval (d : Data) (h42 : d.stacks 42 = []) :
    Eval address (7 * (d.stacks 31).length + 7 * (d.stacks 39).length + 10)
      d (addressed d) := by
  have h1 := copy_eval d 31 40 42 0 1 (by decide) (by decide) (by decide) (by decide) h42
  have h2 := copy_eval (afterCopy d 31 40 0 1) 39 40 42 0 1
    (by decide) (by decide) (by decide) (by decide)
    (by simp [afterCopy, StackRoutines.copyStacks, h42])
  convert h1.seq h2 using 1 <;>
    simp [address, addressed, copy, Subexp.SupportSelectionProgram.copy, afterCopy,
      StackRoutines.copyStacks] ; try omega

theorem test_eval_oai (d : Data) (earlier : List (List Bool)) (word rest : List Bool)
    (hs : d.stacks 33 = earlier.flatten ++ (word ++ rest))
    (hi : (d.stacks 31).length + (d.stacks 39).length = earlier.length)
    (hw : word.length = (d.stacks 38).length)
    (hr : ∀ row ∈ earlier, row.length = (d.stacks 38).length) (hc : Clean d) :
    Eval test (testCost (d.stacks 31).length (d.stacks 39).length
      (d.stacks 38).length (d.stacks 32) word)
      d (tested d (word.getD (d.stacks 32).length false)) := by
  have hz12 := hc 12 (by decide)
  have hz36 := hc 36 (by decide)
  have hz40 := hc 40 (by decide)
  have hz42 := hc 42 (by decide)
  let a := addressed d
  have h1 := address_eval d hz42
  let b := selected a word
  have h2 : Eval lookup (lookupCost ((d.stacks 31).length + (d.stacks 39).length)
      (d.stacks 38).length) a b := by
    have he := lookup_eval a earlier word rest
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hs)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks, hz40, Nat.add_comm] using hi)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hw)
      (by simpa [a, addressed, afterCopy, StackRoutines.copyStacks] using hr)
      (by
        intro i hi'
        have h40 : i ≠ 40 := by intro he; subst i; simp at hi'
        simpa [a, addressed, afterCopy, StackRoutines.copyStacks, h40] using
          hc i (by simp at hi' ⊢; tauto))
    simpa [b, a, addressed, afterCopy, StackRoutines.copyStacks, hz40, ← hi, Nat.add_comm] using he
  let c := cleared b
  have h3 : Eval clearAddress (2 * ((d.stacks 31).length + (d.stacks 39).length) + 3) b c := by
    simpa [clearAddress, c, cleared, b, selected, a, addressed, afterCopy,
      StackRoutines.copyStacks, StackRoutines.clearStacks, hz40, Nat.add_comm] using
      Subexp.TupleProgram.clear_eval (40 : Fin 64) (0 : Fin 16) 1 b
  let e := afterCopy c 32 12 0 1
  have h4 : Eval (copy 32 12) (7 * (d.stacks 32).length + 5) c e := by
    have he := copy_eval c 32 12 42 0 1 (by decide) (by decide) (by decide) (by decide)
      (by simp [c, cleared, b, selected, a, addressed, afterCopy, StackRoutines.copyStacks, hz42])
    simpa [e, c, cleared, b, selected, a, addressed, copy,
      Subexp.SupportSelectionProgram.copy, afterCopy,
      StackRoutines.copyStacks] using he
  let z := HeadIdentifierProgram.bitResult e false (word.getD (d.stacks 32).length false)
  have h5 : Eval (HeadIdentifierProgram.readBit false)
      (Subexp.TypeBitProgram.cost (d.stacks 32) word) e z := by
    simpa [z, e, c, cleared, b, selected, a, addressed, afterCopy,
      StackRoutines.copyStacks, HeadIdentifierProgram.bitSource, hz12] using
      HeadIdentifierProgram.readBit_eval e false
  have heq : z = tested d (word.getD (d.stacks 32).length false) := by
    apply state_ext
    · funext i
      fin_cases i <;> simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
        HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitFlag, tested, readRegs]
    · funext i
      by_cases h12 : i = 12
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz12]
      by_cases h36 : i = 36
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz36]
      by_cases h40 : i = 40
      · subst i; simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, hz40]
      · simp [z, e, c, cleared, b, selected, a, addressed, afterCopy,
          HeadIdentifierProgram.bitResult, HeadIdentifierProgram.bitSource, tested,
          StackRoutines.copyStacks, h12, h36, h40]
  have he := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  rw [heq] at he
  convert he using 1 <;> simp [test, testCost] ; omega

end SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LeafHeadFactorsProgram.test_eval_oai
