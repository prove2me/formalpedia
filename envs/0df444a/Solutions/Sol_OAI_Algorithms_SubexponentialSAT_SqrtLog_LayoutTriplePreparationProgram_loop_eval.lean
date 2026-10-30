-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T04:31:34.655983+00:00
-- url     : https://prove2.me/submissions/0c5d0db7-7242-4355-86b4-1381793b51b9

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S089
import Definitions.Def_OAIQ081S091
import Definitions.Def_OAIQ081S098

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramArrays
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical access to the two-array integer matrix ABI. Every array entry is a
runtime-width binary word; its signed value is positive minus negative. The
fixed program below preserves both arrays, the index and width. It does not
assume a unit-cost array lookup or add an integer primitive to the machine. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.StackRoutines
open SubexponentialSAT.ArrayUpdateLifted

private theorem copyIndex_eval (d : ArrayData) (ht : d.stacks 7 = []) :
    Eval (.call (copyProgram 2 3 7 0 1)) (7 * (d.stacks 2).length + 5) d
      ⟨readRegs d.regs 0 1 none, copyStacks 2 3 d.stacks⟩ := by
  apply Eval.call
  have h := halt_after_trace _
    (copyProgram_trace (2 : Fin 11) 3 7 (0 : Fin 2) 1
      (by decide) (by decide) (by decide) (by decide) d.regs d.stacks ht)
    7 rfl rfl
  simpa [SubexponentialSAT.StructuredProgram.State.withPC, copyResult, copyProgram, Nat.add_assoc] using h

private theorem after_positive (positive : List Bool) (stk : Stacks (Fin 11))
    (h3 : stk 3 = []) :
    readStacksAt positivePorts positive (copyStacks 2 3 stk) =
      Function.update stk 5 (positive ++ stk 5) := by
  funext j
  fin_cases j <;> simp [readStacksAt, positivePorts, copyStacks, h3]

private theorem after_negative (negative : List Bool) (stk : Stacks (Fin 11))
    (h3 : stk 3 = []) :
    readStacksAt negativePorts negative (copyStacks 2 3 stk) =
      Function.update stk 6 (negative ++ stk 6) := by
  funext j
  fin_cases j <;> simp [readStacksAt, negativePorts, copyStacks, h3]

/-- The two signed components are read by actual preserving array scans.
No relation between the component magnitudes is needed. -/
theorem readSignedCommand_eval (d : ArrayData)
    (beforeP beforeN : List (List Bool))
    (positive negative restP restN width index : List Bool)
    (hp : d.stacks 0 = beforeP.flatten ++ (positive ++ restP))
    (hn : d.stacks 1 = beforeN.flatten ++ (negative ++ restN))
    (hi : d.stacks 2 = index) (hw : d.stacks 4 = width)
    (hip : index.length = beforeP.length) (hin : index.length = beforeN.length)
    (hwp : ∀ x ∈ beforeP, x.length = width.length)
    (hwn : ∀ x ∈ beforeN, x.length = width.length)
    (hlp : positive.length = width.length) (hln : negative.length = width.length)
    (h3 : d.stacks 3 = [])
    (hs : ∀ j : Fin 11, 7 ≤ j.val → d.stacks j = []) :
    Eval readSignedCommand
      (index.length * (28 * width.length + 34) + 30 * width.length + 42) d
      ⟨readRegs d.regs 0 1 none, readSignedStacks positive negative d.stacks⟩ := by
  let d1 : ArrayData := ⟨readRegs d.regs 0 1 none, copyStacks 2 3 d.stacks⟩
  have hc1 := copyIndex_eval d (hs 7 (by decide))
  have hp1 := readProgramAt_eval positivePorts (0 : Fin 2) 1 (by decide)
    beforeP positive restP width index d1.regs d1.stacks
    (by simpa [d1, positivePorts, copyStacks] using hp)
    (by simpa [d1, positivePorts, copyStacks] using hw)
    (by simp [d1, positivePorts, copyStacks, hi, h3]) hip hwp hlp
    (by simpa [d1, positivePorts, copyStacks] using hs 7 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 8 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 9 (by decide))
    (by simpa [d1, positivePorts, copyStacks] using hs 10 (by decide))
  let d2 : ArrayData := ⟨readRegs d.regs 0 1 none,
    Function.update d.stacks 5 (positive ++ d.stacks 5)⟩
  have hp2 : Eval (.call (readProgramAt positivePorts 0 1))
      (beforeP.length * (14 * width.length + 10) + 15 * width.length + 16) d1 d2 := by
    simpa [d1, d2, readRegs_reset, after_positive positive d.stacks h3] using hp1
  have hc2 := copyIndex_eval d2 (by simpa [d2] using hs 7 (by decide))
  let d3 : ArrayData := ⟨readRegs d2.regs 0 1 none, copyStacks 2 3 d2.stacks⟩
  have hn1 := readProgramAt_eval negativePorts (0 : Fin 2) 1 (by decide)
    beforeN negative restN width index d3.regs d3.stacks
    (by simpa [d3, d2, negativePorts, copyStacks] using hn)
    (by simpa [d3, d2, negativePorts, copyStacks] using hw)
    (by simp [d3, d2, negativePorts, copyStacks, hi, h3]) hin hwn hln
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 7 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 8 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 9 (by decide))
    (by simpa [d3, d2, negativePorts, copyStacks] using hs 10 (by decide))
  have hn2 : Eval (.call (readProgramAt negativePorts 0 1))
      (beforeN.length * (14 * width.length + 10) + 15 * width.length + 16) d3
      ⟨readRegs d.regs 0 1 none, readSignedStacks positive negative d.stacks⟩ := by
    have h3' : d2.stacks 3 = [] := by simpa [d2] using h3
    simpa [d3, after_negative negative d2.stacks h3', d2,
      readRegs_reset, readSignedStacks] using hn1
  have h := hc1.seq (hp2.seq (hc2.seq hn2))
  convert h using 1 ; simp [ hi, d2, ← hip, ← hin] ; ring

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramEntriesEmit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Actual signed-pair framing, with every unrelated stack preserved. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem emitPorts_injective (negative : Bool) : Function.Injective (emitPorts negative) := by
  cases negative <;> decide

theorem emitOne_eval (negative : Bool) (d : EmitData) :
    ∃ e : EmitData,
      Eval (emitOne negative) (5*(d.stacks (if negative then 1 else 0)).length+7) d e ∧
      e.stacks = emitOneStacks negative d := by
  let a := projectState id (emitPorts negative) d
  let bits := (d.stacks (if negative then 1 else 0)).reverse
  have ha : SubexpNormalizeProgram.filterState (d.regs 0) (d.regs 1) (d.regs 2)
      (d.stacks 3) (d.stacks 4) (d.stacks 2) bits.reverse = a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j; fin_cases j <;> rfl
    · funext j; cases negative <;> fin_cases j <;> simp [ bits, emitPorts,
        SubexpPostfixControl.quadruple]
  let b := SubexpNormalizeProgram.filterState true false (d.regs 2)
    (d.stacks 3) (d.stacks 4) (true :: (Encoding.frame bits ++ d.stacks 2)) []
  have ht := SubexpNormalizeProgram.emitRecord_trace bits (d.stacks 3) (d.stacks 4)
    (d.stacks 2) (d.regs 0) (d.regs 1) (d.regs 2)
  rw [ha] at ht
  have he := eval_call_lifted SubexpNormalizeProgram.emitRecordProgram id
    (emitPorts negative) d Function.injective_id (emitPorts_injective negative) ht
  rw [embedState_project id (emitPorts negative) d Function.injective_id
    (emitPorts_injective negative)] at he
  refine ⟨embedState id (emitPorts negative) d b, ?_, ?_⟩
  · simpa only [emitOne, bits, List.length_reverse] using he
  · have hbs : b.stacks = Function.update (Function.update a.stacks 3 []) 2
        (true :: (Encoding.frame bits ++ d.stacks 2)) := by
      funext i
      cases negative <;> fin_cases i <;> simp [b,a,projectState,emitPorts,
        SubexpNormalizeProgram.filterState,SubexpPostfixControl.quadruple]
    change Function.extend (emitPorts negative) b.stacks d.stacks = _
    rw [hbs, ProgramLinking.extend_update (emitPorts_injective negative),
      ProgramLinking.extend_update (emitPorts_injective negative)]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project id (emitPorts negative) d Function.injective_id
        (emitPorts_injective negative))
    change Function.extend (emitPorts negative) a.stacks d.stacks = d.stacks at hbase
    rw [hbase]
    cases negative <;> rfl

theorem emitPair_eval (d : EmitData) :
    ∃ e : EmitData,
      Eval emitPair (5*((d.stacks 0).length+(d.stacks 1).length)+15) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 0 []) 1 []) 2
        (pairPrefix (d.stacks 0) (d.stacks 1) ++ d.stacks 2) := by
  obtain ⟨a, ha, has⟩ := emitOne_eval true d
  let b := (StructuredProgram.Atom.pop 2 0 1).eval a
  have hb : Eval (.base (.atom (.pop 2 0 1))) 1 a b := .base (.atom _ _)
  have hbs : b.stacks = Function.update (Function.update d.stacks 1 []) 2
      (Encoding.frame (d.stacks 1).reverse ++ d.stacks 2) := by
    funext j
    simp [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      has, emitOneStacks, Function.update_apply]
  obtain ⟨e, he, hes⟩ := emitOne_eval false b
  refine ⟨e, ?_, ?_⟩
  · have hh := ha.seq (hb.seq he)
    convert hh using 1 ; simp [ hbs ] ; omega
  · rw [hes, emitOneStacks, hbs]
    funext j
    by_cases h0 : j=0 <;> by_cases h1 : j=1 <;> by_cases h2 : j=2 <;>
      simp_all [pairPrefix, List.append_assoc, Function.update_apply]

end SubexponentialSAT.SqrtLog.RowSelectionProgram.Entries

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutScalarEmitter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Preserving signed-pair emission into a reverse buffer. The existing exact
pair serializer is called on paid copies, and its output is transferred once.
All source words survive; the four work stacks are restored to empty. -/
namespace SubexponentialSAT.SqrtLog.LayoutScalarEmitter
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport

theorem pairRegisters_injective : Function.Injective pairRegisters := Fin.castAdd_injective _ _
theorem pairPorts_injective : Function.Injective pairPorts := by decide

theorem pairCall_eval (d : Data) :
    ∃ e, Eval pairCall (5*((d.stacks 3).length+(d.stacks 4).length)+16) d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 3 []) 4 []) 6
        (record (d.stacks 3) (d.stacks 4) ++ d.stacks 6) := by
  let a := projectState pairRegisters pairPorts d
  obtain ⟨b,hb,hsb⟩ := RowSelectionProgram.Entries.emitPair_eval a
  let e := embedState pairRegisters pairPorts d b
  have he := eval_liftCommand_from_state RowSelectionProgram.Entries.emitPair 0 2
    pairRegisters pairPorts d pairRegisters_injective pairPorts_injective hb
  refine ⟨e,?_,?_⟩
  · simpa [e, pairCall, a, projectState, pairPorts, Nat.add_assoc] using he
  · change Function.extend pairPorts b.stacks d.stacks = _
    rw [hsb,ProgramLinking.extend_update pairPorts_injective,
      ProgramLinking.extend_update pairPorts_injective,
      ProgramLinking.extend_update pairPorts_injective]
    have hbase := congrArg StructuredProgram.State.stacks
      (embedState_project pairRegisters pairPorts d pairRegisters_injective pairPorts_injective)
    change Function.extend pairPorts a.stacks d.stacks = d.stacks at hbase
    rw [hbase]
    rfl

theorem emitPair_eval (d : Data) (hready : Ready d) :
    ∃ e, Eval emitPair (18*((d.stacks 0).length+(d.stacks 1).length)+38) d e ∧
      e.stacks = Function.update d.stacks 2
        ((record (d.stacks 0) (d.stacks 1)).reverse ++ d.stacks 2) := by
  obtain ⟨h3,h4,h5,h6⟩ := hready
  obtain ⟨a,ha,hsa⟩ := copy_eval (0 : Fin 7) 3 5
    (by decide) (by decide) (by decide) d h5
  obtain ⟨b,hb,hsb⟩ := copy_eval (1 : Fin 7) 4 5
    (by decide) (by decide) (by decide) a (by simp [hsa,StackRoutines.copyStacks,h5])
  obtain ⟨c,hc,hsc⟩ := pairCall_eval b
  obtain ⟨e,he,hse⟩ := transfer_eval (6 : Fin 7) 2 (by decide) c
  have ha1 : a.stacks 1 = d.stacks 1 := by simp [hsa,StackRoutines.copyStacks]
  have hb3 : b.stacks 3 = d.stacks 0 := by simp [hsb,hsa,StackRoutines.copyStacks,h3]
  have hb4 : b.stacks 4 = d.stacks 1 := by simp [hsb,hsa,StackRoutines.copyStacks,h4]
  have hb6 : b.stacks 6 = [] := by simp [hsb,hsa,StackRoutines.copyStacks,h6]
  have hc6 : c.stacks 6 = record (d.stacks 0) (d.stacks 1) := by simp [hsc,hb3,hb4,hb6]
  have hall := ha.seq (hb.seq (hc.seq he))
  rw [ha1,hb3,hb4,hc6,record_length] at hall
  have ht : (7*(d.stacks 0).length+5)+((7*(d.stacks 1).length+5)+
      ((5*((d.stacks 0).length+(d.stacks 1).length)+16)+
        (3*(2*((d.stacks 0).length+(d.stacks 1).length)+3)+3))) =
      18*((d.stacks 0).length+(d.stacks 1).length)+38 := by omega
  rw [ht] at hall
  refine ⟨e,hall,?_⟩
  rw [hse,hsc,hsb,hsa]
  funext i; fin_cases i <;>
    simp [StackRoutines.transferStacks,StackRoutines.copyStacks,h3,h4,h5,h6]

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgramBasic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed port assignments for cache access and triple serialization. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem smallRegisters_injective : Function.Injective smallRegisters := Fin.castAdd_injective _ _
theorem workRegisters_injective : Function.Injective workRegisters := Fin.castAdd_injective _ _

theorem readPorts_injective (b : Bool) : Function.Injective (readPorts b) := by
  cases b <;> decide

/-- Source arrays, master index and width are preserved, including every bit
outside the two output stacks. The index scan and all copying are paid. -/
theorem readCached_eval (binomial : Bool) (d : Data)
    (beforeP beforeN : List (List Bool)) (p n restP restN : List Bool)
    (hp : d.stacks (readPorts binomial 0) = beforeP.flatten++(p++restP))
    (hn : d.stacks (readPorts binomial 1) = beforeN.flatten++(n++restN))
    (hip : (d.stacks (readPorts binomial 2)).length = beforeP.length)
    (hin : (d.stacks (readPorts binomial 2)).length = beforeN.length)
    (hwp : ∀ x ∈ beforeP, x.length = (d.stacks 4).length)
    (hwn : ∀ x ∈ beforeN, x.length = (d.stacks 4).length)
    (hlp : p.length = (d.stacks 4).length) (hln : n.length = (d.stacks 4).length)
    (h10 : d.stacks 10 = []) (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (readCached binomial)
      ((d.stacks (readPorts binomial 2)).length * (28*(d.stacks 4).length+34)+
        30*(d.stacks 4).length+43) d e ∧
      e.stacks = readResult d p n ∧ e.regs 8 = d.regs 8 := by
  let a := projectState smallRegisters (readPorts binomial) d
  have hw : a.stacks 4 = d.stacks 4 := by cases binomial <;> rfl
  have h3 : a.stacks 3 = [] := by cases binomial <;> exact h10
  have hwork : ∀ j : Fin 11, 7 ≤ j.val → a.stacks j = [] := by
    intro j hj
    fin_cases j <;> norm_num at hj
    all_goals cases binomial <;> exact hs _ (by decide) (by decide)
  have he := LayoutProgram.readSignedCommand_eval a beforeP beforeN p n restP restN
    (d.stacks 4) (d.stacks (readPorts binomial 2)) hp hn rfl hw hip hin hwp hwn hlp hln h3 hwork
  let e := embedState smallRegisters (readPorts binomial) d
    ⟨readRegs a.regs 0 1 none,LayoutProgram.readSignedStacks p n a.stacks⟩
  refine ⟨e,?_,?_,?_⟩
  · have hh := eval_liftCommand_from_state LayoutProgram.readSignedCommand 0 5
      smallRegisters (readPorts binomial) d smallRegisters_injective (readPorts_injective binomial) he
    simpa [readCached,a,Nat.add_assoc] using hh
  · change Function.extend (readPorts binomial) _ d.stacks = _
    rw [LayoutProgram.readSignedStacks,
      ProgramLinking.extend_update (readPorts_injective binomial),
      ProgramLinking.extend_update (readPorts_injective binomial)]
    have hb := congrArg StructuredProgram.State.stacks
      (embedState_project smallRegisters (readPorts binomial) d smallRegisters_injective
        (readPorts_injective binomial))
    change Function.extend (readPorts binomial) a.stacks d.stacks = d.stacks at hb
    rw [hb]
    cases binomial <;> rfl
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 8 at hv
    have := j.isLt
    omega

theorem emitPorts_injective (which : Fin 3) : Function.Injective (emitPorts which) := by
  fin_cases which <;> decide

theorem emitCached_eval (which : Fin 3) (d : Data)
    (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (emitCached which)
      (18*((d.stacks (emitPorts which 0)).length+(d.stacks (emitPorts which 1)).length)+39) d e ∧
      e.stacks = Function.update d.stacks 17
        ((LayoutScalarEmitter.record (d.stacks (emitPorts which 0))
          (d.stacks (emitPorts which 1))).reverse++d.stacks 17) ∧
      e.regs 8 = d.regs 8 := by
  let a := projectState workRegisters (emitPorts which) d
  have ha : LayoutScalarEmitter.Ready a := by
    fin_cases which <;>
      exact ⟨hs _ (by decide) (by decide),hs _ (by decide) (by decide),
        hs _ (by decide) (by decide),hs _ (by decide) (by decide)⟩
  obtain ⟨b,hb,hbs⟩ := LayoutScalarEmitter.emitPair_eval a ha
  let e := embedState workRegisters (emitPorts which) d b
  refine ⟨e,?_,?_,?_⟩
  · have hh := eval_liftCommand_from_state LayoutScalarEmitter.emitPair 0 2
      workRegisters (emitPorts which) d workRegisters_injective (emitPorts_injective which) hb
    simpa [emitCached,a,projectState,Nat.add_assoc] using hh
  · change Function.extend (emitPorts which) b.stacks d.stacks = _
    rw [hbs,ProgramLinking.extend_update (emitPorts_injective which)]
    have hf := congrArg StructuredProgram.State.stacks
      (embedState_project workRegisters (emitPorts which) d workRegisters_injective
        (emitPorts_injective which))
    change Function.extend (emitPorts which) a.stacks d.stacks = d.stacks at hf
    rw [hf]
    fin_cases which <;> rfl
  · apply embedState_register_frame
    rintro ⟨j,hj⟩
    have hv := congrArg Fin.val hj
    change j.val = 8 at hv
    have := j.isLt
    omega

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutTriplePreparationProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms


-- LayoutTriplePreparationProgramLookup.lean

/-! List-level cache representation for the preserving physical array scan. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem readCached_get (binomial : Bool) (d : Data)
    (ps ns : List (List Bool)) (i : ℕ)
    (hp : d.stacks (readPorts binomial 0) = ps.flatten)
    (hn : d.stacks (readPorts binomial 1) = ns.flatten)
    (hi : (d.stacks (readPorts binomial 2)).length = i)
    (hip : i < ps.length) (hin : i < ns.length)
    (hwp : ∀ w ∈ ps, w.length = (d.stacks 4).length)
    (hwn : ∀ w ∈ ns, w.length = (d.stacks 4).length)
    (h10 : d.stacks 10 = []) (hs : ∀ j : Fin 20, 13 ≤ j.val → j.val ≤ 16 → d.stacks j = []) :
    ∃ e, Eval (readCached binomial)
      (i*(28*(d.stacks 4).length+34)+30*(d.stacks 4).length+43) d e ∧
      e.stacks = readResult d (ps.getD i []) (ns.getD i []) ∧
      e.regs 8 = d.regs 8 := by
  have htp : (ps.take i).length = i := List.length_take_of_le (Nat.le_of_lt hip)
  have htn : (ns.take i).length = i := List.length_take_of_le (Nat.le_of_lt hin)
  obtain ⟨e,he,hst,hr⟩ := readCached_eval binomial d (ps.take i) (ns.take i)
    (ps.getD i []) (ns.getD i []) (ps.drop (i+1)).flatten (ns.drop (i+1)).flatten
    (by rw [hp]; exact SubexponentialSAT.Subexp.GatherProgram.row_decomposition ps i hip)
    (by rw [hn]; exact SubexponentialSAT.Subexp.GatherProgram.row_decomposition ns i hin)
    (by omega) (by omega)
    (fun w hw => hwp w (List.mem_of_mem_take hw))
    (fun w hw => hwn w (List.mem_of_mem_take hw))
    (by rw [List.getD_eq_getElem _ _ hip]; exact hwp _ (List.getElem_mem hip))
    (by rw [List.getD_eq_getElem _ _ hin]; exact hwn _ (List.getElem_mem hin)) h10 hs
  exact ⟨e,by simpa only [hi] using he,hst,hr⟩

theorem readH_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hp : hindex.length < c.Hpositive.length)
    (hn : hindex.length < c.Hnegative.length) :
    ∃ r, r 8 = regs 8 ∧
      Eval (readCached false)
        (hindex.length*(28*c.width.length+34)+30*c.width.length+43)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue parity (c.Hword hindex.length)) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  obtain ⟨e,he,hs,hr⟩ := readCached_get false d c.Hpositive c.Hnegative hindex.length
    rfl rfl rfl hp hn hu.1 hu.2.1 rfl (by
      intro j hj hj'
      fin_cases j <;> simp_all [d, cacheState])
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue parity (c.Hword hindex.length) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [readResult,d,cacheState,Cache.Hword]
  rw [heq] at he
  exact ⟨e.regs,hr,he⟩

theorem readB_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hp : kindex.length < c.Bpositive.length)
    (hn : kindex.length < c.Bnegative.length) :
    ∃ r, r 8 = regs 8 ∧
      Eval (readCached true)
        (kindex.length*(28*c.width.length+34)+30*c.width.length+43)
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r counter hindex kindex buffer queue parity (c.Bword kindex.length)) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  obtain ⟨e,he,hs,hr⟩ := readCached_get true d c.Bpositive c.Bnegative kindex.length
    rfl rfl rfl hp hn hu.2.2.1 hu.2.2.2 rfl (by
      intro j hj hj'
      fin_cases j <;> simp_all [d, cacheState])
  have heq : e = cacheState c e.regs counter hindex kindex buffer queue parity (c.Bword kindex.length) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs]
    funext j
    fin_cases j <;> simp [readResult,d,cacheState,Cache.Bword]
  rw [heq] at he
  exact ⟨e.regs,hr,he⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramStep.lean

/-! One real triple-production iteration: two scans, three serializers and
paid cleanup. Only a parity bit is kept outside the subroutine registers. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open RowSelectionProgram

theorem cacheEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) (which : Fin 3) :
    ∃ r, r 8 = regs 8 ∧
      Eval (emitCached which) (18*pairLength (selectedWord c work which)+39)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex
          ((LayoutScalarEmitter.record (selectedWord c work which).1
            (selectedWord c work which).2).reverse++buffer) queue parity work) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity work
  obtain ⟨e,he,hs,hr⟩ := emitCached_eval which d (by
    intro j hj hj'
    fin_cases j <;> simp_all [d, cacheState])
  have hs1 : d.stacks (emitPorts which 0) = (selectedWord c work which).1 := by
    fin_cases which <;> rfl
  have hs2 : d.stacks (emitPorts which 1) = (selectedWord c work which).2 := by
    fin_cases which <;> rfl
  have heq : e = cacheState c e.regs counter hindex kindex
      ((LayoutScalarEmitter.record (selectedWord c work which).1
        (selectedWord c work which).2).reverse++buffer) queue parity work := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hs,hs1,hs2]
    funext j
    fin_cases j <;> simp [d,cacheState]
  rw [heq,hs1,hs2] at he
  exact ⟨e.regs,hr,he⟩

theorem clearWork_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    Eval clearWork (2*pairLength work+6)
      (cacheState c regs counter hindex kindex buffer queue parity work)
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity) := by
  have h1 := SubexponentialSAT.Subexp.TupleProgram.clear_eval (11 : Fin 20) (0 : Fin 9) 1
    (cacheState c regs counter hindex kindex buffer queue parity work)
  have h2 := SubexponentialSAT.Subexp.TupleProgram.clear_eval (12 : Fin 20) (0 : Fin 9) 1
    (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2))
  have heq1 : StackRoutines.clearStacks 11
      (cacheState c regs counter hindex kindex buffer queue parity work).stacks =
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2)).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  have heq2 : StackRoutines.clearStacks 12
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity ([],work.2)).stacks =
      (cacheState c (readRegs regs 0 1 none) counter hindex kindex buffer queue parity).stacks := by
    funext j
    fin_cases j <;> simp [StackRoutines.clearStacks,cacheState]
  simp only [heq1] at h1
  simp only [heq2] at h2
  have hh := h1.seq h2
  convert hh using 1 <;> simp [clearWork,cacheState,pairLength,StackRoutines.readRegs_reset] ; ring

theorem cacheSignedEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    ∃ r, r 8 = regs 8 ∧
      Eval cacheSignedEmit (20*pairLength work+46)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex
          ((wordRecord (signedPair (regs 8) work.1 work.2)).reverse++buffer) queue parity) := by
  cases hg : regs 8
  · obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 0
    have hc := clearWork_eval c r counter hindex kindex
      ((wordRecord work).reverse++buffer) queue parity work
    refine ⟨readRegs r 0 1 none,by simpa [readRegs,hg] using hr,?_⟩
    have hh := (Eval.ite_false (yes := emitCached 1) (by simpa [cacheState] using hg) he).seq hc
    convert hh using 1 <;>
      simp [cacheSignedEmit,emitSigned,selectedWord,signedPair,wordRecord] ; ring
  · obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 1
    have hc := clearWork_eval c r counter hindex kindex
      ((wordRecord (work.2,work.1)).reverse++buffer) queue parity work
    refine ⟨readRegs r 0 1 none,by simpa [readRegs,hg] using hr,?_⟩
    have hh := (Eval.ite_true (no := emitCached 0) (by simpa [cacheState] using hg) he).seq hc
    convert hh using 1 <;>
      simp [cacheSignedEmit,emitSigned,selectedWord,signedPair,wordRecord,pairLength] ; ring

theorem cachePlainEmit_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) (work : WordPair) :
    ∃ r, r 8 = regs 8 ∧
      Eval cachePlainEmit (20*pairLength work+45)
        (cacheState c regs counter hindex kindex buffer queue parity work)
        (cacheState c r counter hindex kindex ((wordRecord work).reverse++buffer) queue parity) := by
  obtain ⟨r,hr,he⟩ := cacheEmit_eval c regs counter hindex kindex buffer queue parity work 0
  have hc := clearWork_eval c r counter hindex kindex ((wordRecord work).reverse++buffer) queue parity work
  refine ⟨readRegs r 0 1 none,by simpa [readRegs] using hr,?_⟩
  convert he.seq hc using 1 <;> simp [cachePlainEmit,selectedWord] ; ring

theorem advance_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    ∃ r, r 8 = !(regs 8) ∧ Eval advance 3
      (cacheState c regs counter hindex kindex buffer queue parity)
      (cacheState c r counter hindex (true::kindex) buffer queue parity) := by
  let d := cacheState c regs counter hindex kindex buffer queue parity
  let a := (StructuredProgram.Atom.bnot (8 : Fin 9) 8).eval d
  let b := (StructuredProgram.Atom.set (0 : Fin 9) true).eval a
  let e := (StructuredProgram.Atom.push (9 : Fin 20) (0 : Fin 9)).eval b
  have h1 : Eval (.base (.atom (.bnot 8 8))) 1 d a := .base (.atom _ _)
  have h2 : Eval (.base (.atom (.set 0 true))) 1 a b := .base (.atom _ _)
  have h3 : Eval (.base (.atom (.push 9 0))) 1 b e := .base (.atom _ _)
  have hr : e.regs 8 = !(regs 8) := by
    simp [e,b,a,d,cacheState,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  have heq : e = cacheState c e.regs counter hindex (true::kindex) buffer queue parity := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext j
    fin_cases j <;>
      simp [b,a,d,cacheState,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
        StructuredProgram.State.ofCfg,execInstr]
  have hall : Eval advance 3 d e := h1.seq (h2.seq h3)
  rw [heq] at hall
  exact ⟨e.regs,hr,hall⟩

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramBody.lean

/-! A fixed, paid iteration producing the three real scalar operands. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram

theorem Cache.Hword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Hpositive.length) (hn : i < c.Hnegative.length) :
    pairLength (c.Hword i) = 2*c.width.length := by
  have h1 := hu.1 (c.Hpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.1 (c.Hnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Hword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

theorem Cache.Bword_length (c : Cache) (hu : c.Uniform) (i : ℕ)
    (hp : i < c.Bpositive.length) (hn : i < c.Bnegative.length) :
    pairLength (c.Bword i) = 2*c.width.length := by
  have h1 := hu.2.2.1 (c.Bpositive[i]) (List.getElem_mem hp)
  have h2 := hu.2.2.2 (c.Bnegative[i]) (List.getElem_mem hn)
  simp only [Cache.Bword,pairLength,List.getD_eq_getElem _ _ hp,List.getD_eq_getElem _ _ hn]
  omega

theorem popH_eval (c : Cache) (regs : Fin 9 → Bool) (b : Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    Eval popH 1 (cacheState c regs counter (b::hindex) kindex buffer queue parity)
      (cacheState c (readRegs regs 0 1 (some b)) counter hindex kindex buffer queue parity) := by
  have h : Eval popH 1 (cacheState c regs counter (b::hindex) kindex buffer queue parity)
    ((StructuredProgram.Atom.pop (8 : Fin 20) (0 : Fin 9) 1).eval
      (cacheState c regs counter (b::hindex) kindex buffer queue parity)) := .base (.atom _ _)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [cacheState,StructuredProgram.Atom.instr,execInstr]

theorem body_eval (c : Cache) (regs : Fin 9 → Bool) (b : Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform)
    (hhp : hindex.length < c.Hpositive.length) (hhn : hindex.length < c.Hnegative.length)
    (hbp : kindex.length < c.Bpositive.length) (hbn : kindex.length < c.Bnegative.length) :
    ∃ r, r 8 = !(regs 8) ∧
      Eval body (bodyCost hindex.length kindex.length c.width.length (pairLength c.power))
        (cacheState c regs counter (b::hindex) kindex buffer queue parity)
        (cacheState c r counter hindex (true::kindex)
          ((tripleRecord (triple c (regs 8) hindex.length kindex.length)).reverse++buffer)
          queue parity) := by
  let r0 := readRegs regs 0 1 (some b)
  have hp := popH_eval c regs b counter hindex kindex buffer queue parity
  obtain ⟨r1,hr1,h1⟩ := readH_eval c r0 counter hindex kindex buffer queue parity hu hhp hhn
  obtain ⟨r2,hr2,h2⟩ := cacheSignedEmit_eval c r1 counter hindex kindex buffer queue parity
    (c.Hword hindex.length)
  have hr10 : r1 8 = regs 8 := by simpa [r0,readRegs] using hr1
  rw [hr10] at h2
  let Hrec := wordRecord (signedPair (regs 8) (c.Hword hindex.length).1 (c.Hword hindex.length).2)
  let PRec := wordRecord c.power
  let BRec := wordRecord (c.Bword kindex.length)
  obtain ⟨r3,hr3,h3⟩ := cacheEmit_eval c r2 counter hindex kindex (Hrec.reverse++buffer)
    queue parity ([],[]) 2
  simp only [selectedWord,show (2 : Fin 3) ≠ 0 by decide,show (2 : Fin 3) ≠ 1 by decide,
    ↓reduceIte] at h3
  obtain ⟨r4,hr4,h4⟩ := readB_eval c r3 counter hindex kindex
    (PRec.reverse++(Hrec.reverse++buffer)) queue parity hu hbp hbn
  obtain ⟨r5,hr5,h5⟩ := cachePlainEmit_eval c r4 counter hindex kindex
    (PRec.reverse++(Hrec.reverse++buffer)) queue parity (c.Bword kindex.length)
  obtain ⟨r6,hr6,h6⟩ := advance_eval c r5 counter hindex kindex
    (BRec.reverse++(PRec.reverse++(Hrec.reverse++buffer))) queue parity
  have h56 := h5.seq h6
  have h456 := h4.seq h56
  have h3456 := h3.seq h456
  have h23456 := h2.seq h3456
  have h123456 := h1.seq h23456
  have hall := hp.seq h123456
  have hlh := c.Hword_length hu hindex.length hhp hhn
  have hlb := c.Bword_length hu kindex.length hbp hbn
  rw [hlh,hlb] at hall
  have ht : 1 + ((hindex.length*(28*c.width.length+34)+30*c.width.length+43) +
      ((20*(2*c.width.length)+46) + ((18*pairLength c.power+39) +
        ((kindex.length*(28*c.width.length+34)+30*c.width.length+43) +
          ((20*(2*c.width.length)+45)+3))))) =
      bodyCost hindex.length kindex.length c.width.length (pairLength c.power) := by
    unfold bodyCost
    ring
  have hout : BRec.reverse++(PRec.reverse++(Hrec.reverse++buffer)) =
      (tripleRecord (triple c (regs 8) hindex.length kindex.length)).reverse++buffer := by
    simp only [tripleRecord,triple,Hrec,PRec,BRec,wordRecord,List.reverse_append,List.append_assoc]
  rw [ht,hout] at hall
  refine ⟨r6,by rw [hr6,hr5,hr4,hr3,hr2,hr10],?_⟩
  simpa only [body] using hall

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramLoop.lean

/-! The native unary loop produces all triples in increasing binomial index. -/
namespace SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls RowSelectionProgram
open SubexponentialSAT.Subexp.MatrixParityProgram (toggle)

theorem popCount_eval (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool) :
    Eval popCount 1 (cacheState c regs counter hindex kindex buffer queue parity)
      (cacheState c (readRegs regs 6 7 counter.head?) counter.tail hindex kindex buffer queue parity) := by
  have h : Eval popCount 1 (cacheState c regs counter hindex kindex buffer queue parity)
    ((StructuredProgram.Atom.pop (7 : Fin 20) (6 : Fin 9) 7).eval
      (cacheState c regs counter hindex kindex buffer queue parity)) := .base (.atom _ _)
  convert h using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [cacheState,StructuredProgram.Atom.instr,execInstr]

theorem eval_seq_decompose {first second : Code} {t : ℕ} {a z : Data}
    (h : Eval (.seq first second) t a z) :
    ∃ t₁ t₂ mid, t = t₁+t₂ ∧ Eval first t₁ a mid ∧ Eval second t₂ mid z := by
  cases h with
  | seq h₁ h₂ => exact ⟨_,_,_,rfl,h₁,h₂⟩

theorem loop_eval_oai (c : Cache) (regs : Fin 9 → Bool)
    (counter hindex kindex buffer queue parity : List Bool)
    (hu : c.Uniform) (hf : c.Fits (counter.length+kindex.length))
    (hlen : hindex.length = counter.length) :
    ∃ r, r 8 = toggle counter.length (regs 8) ∧
      Eval loop (loopCost counter.length kindex.length c.width.length (pairLength c.power))
        (cacheState c regs counter hindex kindex buffer queue parity)
        (cacheState c r [] [] (List.replicate counter.length true++kindex)
          ((preparedRecords c (regs 8) counter.length kindex.length).reverse++buffer) queue parity) := by
  induction counter generalizing regs hindex kindex buffer with
  | nil =>
    have hh : hindex = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst hindex
    let r := readRegs regs 6 7 none
    have hp := popCount_eval c regs [] [] kindex buffer queue parity
    have hr : r 7 = false := by simp [r,readRegs]
    refine ⟨r,by simp [r,readRegs,toggle],?_⟩
    have hw : Eval (.while 7 (.seq body popCount)) 1
        (cacheState c r [] [] kindex buffer queue parity)
        (cacheState c r [] [] kindex buffer queue parity) := .while_false hr
    simpa [loop,loopCost,preparedRecords,preparedTriples,r] using hp.seq hw
  | cons cb counter ih =>
    cases hindex with
    | nil => simp at hlen
    | cons hb hindex =>
      have hlen' : hindex.length = counter.length := by simpa using hlen
      let r0 := readRegs regs 6 7 (some cb)
      have hr0 : r0 8 = regs 8 := by simp [r0,readRegs]
      have hg : r0 7 = true := by simp [r0,readRegs]
      have hp := popCount_eval c regs (cb::counter) (hb::hindex) kindex buffer queue parity
      have hhp : hindex.length < c.Hpositive.length := by have := hf.1; simp only [List.length_cons] at this; omega
      have hhn : hindex.length < c.Hnegative.length := by have := hf.2.1; simp only [List.length_cons] at this; omega
      have hbp : kindex.length < c.Bpositive.length := by have := hf.2.2.1; simp only [List.length_cons] at this; omega
      have hbn : kindex.length < c.Bnegative.length := by have := hf.2.2.2; simp only [List.length_cons] at this; omega
      obtain ⟨r1,hr1,hs⟩ := body_eval c r0 hb counter hindex kindex buffer queue parity hu hhp hhn hbp hbn
      have hf' : c.Fits (counter.length+(true::kindex).length) := by
        simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hf
      obtain ⟨r2,hr2,ht⟩ := ih r1 hindex (true::kindex)
        ((tripleRecord (triple c (r0 8) hindex.length kindex.length)).reverse++buffer) hf' hlen'
      obtain ⟨t₁,t₂,mid,htime,htp,htw⟩ := eval_seq_decompose ht
      refine ⟨r2,?_,?_⟩
      · rw [hr2,hr1,hr0]
        rfl
      · have hall := hp.seq (Eval.while_true (test := 7)
          (show (cacheState c r0 counter (hb::hindex) kindex buffer queue parity).regs 7 = true
            from hg) (hs.seq htp) htw)
        have hcost : 1 + ((bodyCost hindex.length kindex.length c.width.length
              (pairLength c.power)+t₁)+t₂+1) =
            loopCost (cb::counter).length kindex.length c.width.length (pairLength c.power) := by
          simp only [List.length_cons] at htime
          simp only [List.length_cons,loopCost,hlen']
          omega
        rw [hcost,hr1,hr0] at hall
        simpa [loop,preparedRecords,preparedTriples,hlen',List.flatMap_cons,List.reverse_append,
          List.replicate_succ',List.append_assoc] using hall

end SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram

-- LayoutTriplePreparationProgramFinish.lean

/-! Initial unary copy/parity and final stream reversal are native paid calls. -/

/-! Complete cache-to-triple primitive program with all scans and copies paid. -/

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutTriplePreparationProgram.loop_eval_oai
