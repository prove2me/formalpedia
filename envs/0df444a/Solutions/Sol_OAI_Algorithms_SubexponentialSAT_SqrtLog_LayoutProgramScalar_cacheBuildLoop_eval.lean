-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:02:53.684659+00:00
-- url     : https://prove2.me/submissions/6d37d3ee-086b-4163-9359-ed1ff194ee47

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S098
import Definitions.Def_OAIQ081S125
import Definitions.Def_OAIQ081S143

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramParser
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Explicit framed input parsing for streams of signed binary word pairs. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

private theorem atom_pop_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) [false])
        (streamData regs' acc ([],[]) []) := by
  let d := streamData regs acc ([],[]) [false]
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = false := by
    simp [a, d, streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr, readRegs]
  have ha : a = streamData a.regs acc ([],[]) [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ d, streamData, StructuredProgram.Atom.instr, execInstr]
  refine ⟨a.regs, hg, ?_⟩
  rw [← ha]
  exact (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
    (Eval.ite_false hg (.base (.skip a)))

theorem parsePair_nil (regs : Fin 8 → Bool) (acc : WordPair) :
    ∃ regs', regs' 7 = false ∧
      Eval parsePair 2 (streamData regs acc ([],[]) (pairEncoding []))
        (streamData regs' acc ([],[]) []) := atom_pop_nil regs acc

theorem parsePair_cons (regs : Fin 8 → Bool) (acc next : WordPair) (rest : List WordPair) :
    ∃ regs', regs' 7 = true ∧
      Eval parsePair (6*pairLength next+10)
        (streamData regs acc ([],[]) (pairEncoding (next::rest)))
        (streamData regs' acc next (pairEncoding rest)) := by
  let d := streamData regs acc ([],[]) (pairEncoding (next::rest))
  let a := (StructuredProgram.Atom.pop 15 7 6).eval d
  have hg : a.regs 7 = true := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr, readRegs]
  have hs : a.stacks 15 = Encoding.frame next.1.reverse ++
      (Encoding.frame next.2.reverse ++ pairEncoding rest) := by
    simp [a, d, streamData, pairEncoding, StructuredProgram.Atom.eval,
      StructuredProgram.Atom.instr, StructuredProgram.State.ofCfg, execInstr]
  have hp : a.stacks 2 = [] := rfl
  have hi := RecordPrograms.state_eq_self positiveReader a (a.regs 0) (a.regs 1)
    (a.regs 7) _ [] rfl rfl rfl hs hp
  have hr := RecordPrograms.reader_eval positiveReader a next.1.reverse
    (Encoding.frame next.2.reverse ++ pairEncoding rest) [] (a.regs 0) (a.regs 1) (a.regs 7)
  rw [hi] at hr
  let b := RecordPrograms.state positiveReader a false true (a.regs 7)
    (Encoding.frame next.2.reverse ++ pairEncoding rest) next.1
  have hr' : Eval (RecordPrograms.reader positiveReader) (6*next.1.length+4) a b := by
    simpa [b] using hr
  have hs2 : b.stacks 15 = Encoding.frame next.2.reverse ++ pairEncoding rest := by
    simp [b, positiveReader, RecordPrograms.state]
  have hn : b.stacks 3 = [] := by
    simp [b, a, d, positiveReader, RecordPrograms.state, streamData,
      StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr]
  have hi2 := RecordPrograms.state_eq_self negativeReader b (b.regs 0) (b.regs 1)
    (b.regs 7) _ [] rfl rfl rfl hs2 hn
  have hr2 := RecordPrograms.reader_eval negativeReader b next.2.reverse
    (pairEncoding rest) [] (b.regs 0) (b.regs 1) (b.regs 7)
  rw [hi2] at hr2
  let c := RecordPrograms.state negativeReader b false true (b.regs 7)
    (pairEncoding rest) next.2
  have hr2' : Eval (RecordPrograms.reader negativeReader) (6*next.2.length+4) b c := by
    simpa [c] using hr2
  have hc : c = streamData c.regs acc next (pairEncoding rest) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j; fin_cases j <;>
        simp [ b, a, d, positiveReader, negativeReader, RecordPrograms.state,
          streamData, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
          StructuredProgram.State.ofCfg, execInstr]
  refine ⟨c.regs, ?_, ?_⟩
  · simpa [c, b, negativeReader, positiveReader, RecordPrograms.state] using hg
  · rw [← hc]
    convert (Eval.base (StructuredProgram.Eval.atom (.pop 15 7 6) d)).seq
      (Eval.ite_true (no := .base .skip) hg (hr'.seq hr2')) using 1 ;
      simp [ pairLength] ; omega

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

theorem parse_cons (regs : Fin 8 → Bool) (acc work next : WordPair)
    (rest : List WordPair) :
    ∃ r, r 7 = true ∧ Eval parse (6*pairLength next+11)
      (state regs acc work ([],[]) (pairEncoding (next::rest)))
      (state r acc work next (pairEncoding rest)) := by
  obtain ⟨r,hg,he⟩ := parsePair_cons regs work next rest
  exact ⟨r,hg,by simpa only [parse, Nat.add_assoc] using workCall_eval he acc⟩

theorem parse_nil (regs : Fin 8 → Bool) (acc work : WordPair) :
    ∃ r, r 7 = false ∧ Eval parse 3
      (state regs acc work ([],[]) (pairEncoding []))
      (state r acc work ([],[]) []) := by
  obtain ⟨r,hg,he⟩ := parsePair_nil regs work
  exact ⟨r,hg,workCall_eval he acc⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

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

theorem finishList_eval (d : Data) (h6 : d.stacks 6 = []) :
    ∃ e, Eval finishList (3*(d.stacks 2).length+8) d e ∧
      e.stacks = Function.update (Function.update d.stacks 2 []) 6
        ((d.stacks 2).reverse ++ [false]) := by
  let a := (StructuredProgram.Atom.set (0 : Fin 8) false).eval d
  let b := (StructuredProgram.Atom.push (2 : Fin 7) (0 : Fin 8)).eval a
  have ha : Eval (.base (.atom (.set 0 false))) 1 d a := .base (.atom _ _)
  have hb : Eval (.base (.atom (.push 2 0))) 1 a b := .base (.atom _ _)
  obtain ⟨e,he,hse⟩ := transfer_eval (2 : Fin 7) 6 (by decide) b
  have hbs : b.stacks = Function.update d.stacks 2 (false :: d.stacks 2) := by
    simp [b,a,StructuredProgram.Atom.eval,StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg,execInstr]
  have hall := ha.seq (hb.seq he)
  have hb2 : (b.stacks 2).length = (d.stacks 2).length+1 := by simp [hbs]
  rw [hb2] at hall
  have ht : 1+(1+(3*((d.stacks 2).length+1)+3)) = 3*(d.stacks 2).length+8 := by omega
  rw [ht] at hall
  refine ⟨e,hall,?_⟩
  rw [hse,hbs]
  funext i; fin_cases i <;> simp [StackRoutines.transferStacks,h6,List.reverse_cons]

end SubexponentialSAT.SqrtLog.LayoutScalarEmitter

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramScalarCacheCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The unsigned cache recurrence is executed by a one-bit shift followed by
the original finite little-endian adder. Its representation growth is linear
in the number of cells; no canonical-word assumption is used. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.BinaryArithmetic
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheWord_length (prior old : List Bool) :
    (cacheWord prior old).length ≤ max prior.length old.length+2 := by
  have h := length_add (false::prior) old
  dsimp [cacheWord]
  simp only [List.length_cons] at h
  omega

theorem cacheCellLocal_eval (regs : Fin 8 → Bool) (prior old : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+2)+2, ∃ r,
      Eval cacheCellLocal t (cacheCellState regs prior old)
        (cacheCellState r (cacheWord prior old) []) := by
  let r₀ := Function.update regs 0 false
  have hs : Eval (.base (.atom (.set 0 false))) 1
      (cacheCellState regs prior old) (cacheCellState r₀ prior old) := .base (.atom _ _)
  have hp : Eval (.base (.atom (.push 0 0))) 1
      (cacheCellState r₀ prior old) (cacheCellState r₀ (false::prior) old) := by
    convert (Eval.base (StructuredProgram.Eval.atom (.push (0 : Fin 3) (0 : Fin 8))
      (cacheCellState r₀ prior old))) using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases j <;> simp [cacheCellState,r₀,BinaryPrograms.Add.stackState,StructuredProgram.Atom.instr,execInstr]
  obtain ⟨r,t,ht,he⟩ := BinaryPrograms.Add.littleEndian_run r₀ (false::prior) old
  have ha : Eval (.call BinaryPrograms.Add.littleEndianProgram) t
      (cacheCellState r₀ (false::prior) old)
      (cacheCellState r (cacheWord prior old) []) := by
    apply Eval.call
    rw [show BinaryPrograms.Add.littleEndianProgram.entry = 0 from rfl]
    simpa [cacheCellState,cacheWord,r₀,add,
      StructuredProgram.State.withPC,BinaryPrograms.Add.littleEndianProgram] using he
  refine ⟨1+(1+t),?_,r,hs.seq (hp.seq ha)⟩
  simp only [List.length_cons] at ht
  omega

theorem cacheCellPorts_injective : Function.Injective cacheCellPorts := by decide

theorem cacheCell_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior old queue : List Bool) :
    ∃ t ≤ 16*(max prior.length old.length+2)+3, ∃ r,
      Eval cacheCell t (state regs acc (prior,[]) (old,[]) queue)
        (state r acc (cacheWord prior old,[]) ([],[]) queue) := by
  obtain ⟨t,ht,r,he⟩ := cacheCellLocal_eval regs prior old
  have hs : embedState id cacheCellPorts (state regs acc (prior,[]) (old,[]) queue)
      (cacheCellState regs prior old) = state regs acc (prior,[]) (old,[]) queue := by
    apply embedState_eq_of_ports id cacheCellPorts _ _ _
      Function.injective_id cacheCellPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [cacheCellState,cacheCellPorts,state,BinaryPrograms.Add.stackState]
    · intro i hi; rfl
  have hf : embedState id cacheCellPorts (state regs acc (prior,[]) (old,[]) queue)
      (cacheCellState r (cacheWord prior old) []) =
      state r acc (cacheWord prior old,[]) ([],[]) queue := by
    apply embedState_eq_of_ports id cacheCellPorts _ _ _
      Function.injective_id cacheCellPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [cacheCellState,cacheCellPorts,state,BinaryPrograms.Add.stackState]
    · intro i hi
      have h0 : i ≠ 0 := fun h => hi ⟨0,by simpa [cacheCellPorts] using h.symm⟩
      have h2 : i ≠ 2 := fun h => hi ⟨1,by simpa [cacheCellPorts] using h.symm⟩
      simp [state,h0,h2]
  have h := eval_call_lifted (compiled cacheCellLocal 0 0) id cacheCellPorts
    (state regs acc (prior,[]) (old,[]) queue) Function.injective_id cacheCellPorts_injective
    (compiled_halt_trace he 0 0)
  rw [hs,hf] at h
  exact ⟨t+1,by omega,r,h⟩

theorem cacheScan_word_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∀ x ∈ cacheScan prior xs, x.length ≤ B+2*xs.length := by
  induction xs generalizing prior B with
  | nil => simp [cacheScan]
  | cons old rest ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have hrest : ∀ x ∈ rest, x.length ≤ B+2 := by
      intro x h
      have hh := hx x (by simp [h])
      omega
    have ht := ih (cacheWord prior old) (B+2) hn hrest
    intro x h
    simp only [cacheScan,List.mem_cons] at h
    rcases h with rfl | h
    · simp only [List.length_cons]; omega
    · have hh := ht x h
      simp only [List.length_cons]; omega

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! One complete cache-row transform, including record parsing and preserving
emission of every newly computed value. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheEmitPorts_injective : Function.Injective cacheEmitPorts := by decide

theorem cacheEmit_eval (regs : Fin 8 → Bool) (acc : WordPair)
    (prior queue : List Bool) :
    ∃ r, Eval cacheEmit (18*prior.length+39)
      (state regs acc (prior,[]) ([],[]) queue)
      (state r ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        (prior,[]) ([],[]) queue) := by
  let d := state regs acc (prior,[]) ([],[]) queue
  let a := projectState id cacheEmitPorts d
  have ha : LayoutScalarEmitter.Ready a := by
    simp [LayoutScalarEmitter.Ready,a,d,projectState,cacheEmitPorts,state]
  obtain ⟨e,he,hs⟩ := LayoutScalarEmitter.emitPair_eval a ha
  have h := eval_liftCommand_from_state LayoutScalarEmitter.emitPair 0 2
    id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective he
  have hout : embedState id cacheEmitPorts d e =
      state e.regs ((LayoutScalarEmitter.record prior []).reverse++acc.1,acc.2)
        (prior,[]) ([],[]) queue := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      exact embedState_register id cacheEmitPorts d e Function.injective_id i
    · rw [hs,ProgramLinking.extend_update cacheEmitPorts_injective]
      have hbase := congrArg StructuredProgram.State.stacks
        (embedState_project id cacheEmitPorts d Function.injective_id cacheEmitPorts_injective)
      change Function.extend cacheEmitPorts a.stacks d.stacks = d.stacks at hbase
      rw [hbase]
      funext j
      fin_cases j <;> simp [a,d,projectState,cacheEmitPorts,state]
  refine ⟨e.regs,?_⟩
  rw [hout] at h
  simpa [cacheEmit,a,d,projectState,cacheEmitPorts,state,Nat.add_assoc] using h

theorem cacheRecords_encoding (xs : List (List Bool)) :
    pairEncoding (xs.map fun x => (x,[])) = cacheRecords xs++[false] := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp [pairEncoding,cacheRecords,LayoutScalarEmitter.record,
      RowSelectionProgram.Entries.pairPrefix,ih,List.append_assoc]

theorem cacheRow_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (acc : WordPair) (prior : List Bool) (B : ℕ)
    (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 200*(xs.length+1)*(B+2*xs.length+4), ∃ r,
      r 7 = false ∧
      Eval cacheRow t
        (state regs acc (prior,[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ((cacheRecords (cacheScan prior xs)).reverse++acc.1,acc.2)
          (cacheLast prior xs,[]) ([],[]) []) := by
  induction xs generalizing regs acc prior B with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc (prior,[])
    refine ⟨4,by simp; omega,r,hg,?_⟩
    simpa [cacheRow,cacheScan,cacheLast] using he.seq (.while_false hg)
  | cons old xs ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have hxs : ∀ x ∈ xs, x.length ≤ B+2 := by
      intro x h
      have hh := hx x (by simp [h])
      omega
    obtain ⟨r₁,hg₁,hp₁⟩ := parse_cons regs acc (prior,[]) (old,[])
      (xs.map fun x => (x,[]))
    obtain ⟨tc,htc,r₂,hc⟩ := cacheCell_eval r₁ acc prior old
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨r₃,he⟩ := cacheEmit_eval r₂ acc (cacheWord prior old)
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tt,htt,r₄,hg₄,ht⟩ := ih r₃
      ((LayoutScalarEmitter.record (cacheWord prior old) []).reverse++acc.1,acc.2)
      (cacheWord prior old) (B+2) hn hxs
    cases ht with
    | seq hparse hwhile =>
      rename_i tp tw between
      refine ⟨6*pairLength (old,[])+11+(tc+(18*(cacheWord prior old).length+39)+tp+tw+1),
        ?_,r₄,hg₄,?_⟩
      · simp only [pairLength,List.length_nil,Nat.add_zero,List.length_cons] at *
        have hm : max prior.length old.length ≤ B := by omega
        have hwork :
            6 * old.length + 11 + (tc + (18 * (cacheWord prior old).length + 39)) + 1 ≤
              200 * (B + 2 * xs.length + 6) := by
          omega
        have htt' : tp + tw ≤
            200 * (xs.length + 1) * (B + 2 * xs.length + 6) := by
          have hinner : B + 2 + 2 * xs.length + 4 =
              B + (2 * xs.length + 6) := by omega
          rw [hinner] at htt
          exact htt
        calc
          6 * old.length + 11 +
                (tc + (18 * (cacheWord prior old).length + 39) + tp + tw + 1) =
              (6 * old.length + 11 + (tc + (18 * (cacheWord prior old).length + 39)) + 1) +
                (tp + tw) := by omega
          _ ≤ 200 * (B + 2 * xs.length + 6) +
                200 * (xs.length + 1) * (B + 2 * xs.length + 6) :=
            Nat.add_le_add hwork htt'
          _ = 200 * ((old :: xs).length + 1) *
                (B + 2 * (old :: xs).length + 4) := by
            simp only [List.length_cons]
            ring
      · have hall := hp₁.seq (.while_true hg₁ (hc.seq (he.seq hparse)) hwhile)
        simpa [cacheRow,cacheScan,cacheLast,cacheRecords,List.reverse_append,
          List.append_assoc,Nat.add_assoc] using hall

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! Complete reusable cache pass: read one encoded row, compute and emit its
new row, append the end marker, reverse the output, and clear the carry. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheFinishPorts_injective : Function.Injective cacheFinishPorts := by decide

theorem cacheFinishList_eval (regs : Fin 8 → Bool) (acc : WordPair) (prior : List Bool) :
    ∃ r, Eval cacheFinishList (3*acc.1.length+9)
      (state regs acc (prior,[]) ([],[]) [])
      (state r ([],acc.2) (prior,[]) ([],[]) (acc.1.reverse++[false])) := by
  let d := state regs acc (prior,[]) ([],[]) []
  let a := projectState id cacheFinishPorts d
  obtain ⟨e,he,hs⟩ := LayoutScalarEmitter.finishList_eval a
    (by simp [a,d,projectState,cacheFinishPorts,state])
  have h := eval_liftCommand_from_state LayoutScalarEmitter.finishList 2 6
    id cacheFinishPorts d Function.injective_id cacheFinishPorts_injective he
  have hout : embedState id cacheFinishPorts d e =
      state e.regs ([],acc.2) (prior,[]) ([],[]) (acc.1.reverse++[false]) := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      exact embedState_register id cacheFinishPorts d e Function.injective_id i
    · rw [hs,ProgramLinking.extend_update cacheFinishPorts_injective,
        ProgramLinking.extend_update cacheFinishPorts_injective]
      have hbase := congrArg StructuredProgram.State.stacks
        (embedState_project id cacheFinishPorts d Function.injective_id cacheFinishPorts_injective)
      change Function.extend cacheFinishPorts a.stacks d.stacks = d.stacks at hbase
      rw [hbase]
      funext j
      fin_cases j <;> simp [a,d,projectState,cacheFinishPorts,state]
  refine ⟨e.regs,?_⟩
  rw [hout] at h
  simpa [cacheFinishList,a,d,projectState,cacheFinishPorts,state,Nat.add_assoc] using h

theorem cacheClear_eval (regs : Fin 8 → Bool) (acc : WordPair) (prior queue : List Bool) :
    Eval cacheClear (2*prior.length+3)
      (state regs acc (prior,[]) ([],[]) queue)
      (state (readRegs regs 0 1 none) acc ([],[]) ([],[]) queue) := by
  have h := SubexponentialSAT.Subexp.TupleProgram.clear_eval (0 : Fin 18) (0 : Fin 8) 1
    (state regs acc (prior,[]) ([],[]) queue)
  have hs : StackRoutines.clearStacks 0 (state regs acc (prior,[]) ([],[]) queue).stacks =
      (state (readRegs regs 0 1 none) acc ([],[]) ([],[]) queue).stacks := by
    funext j
    fin_cases j <;> simp [state,StackRoutines.clearStacks]
  rw [hs] at h
  have h0 : (state regs acc (prior, []) ([], []) queue).stacks 0 = prior := by
    simp [state]
  have hr : (state regs acc (prior, []) ([], []) queue).regs = regs := rfl
  rw [h0, hr] at h
  simpa only [cacheClear, state] using h

theorem cacheLast_length (prior : List Bool) (xs : List (List Bool))
    (B : ℕ) (hp : prior.length ≤ B) (hx : ∀ x ∈ xs, x.length ≤ B) :
    (cacheLast prior xs).length ≤ B+2*xs.length := by
  induction xs generalizing prior B with
  | nil => simpa [cacheLast] using hp
  | cons old xs ih =>
    have ho := hx old (by simp)
    have hn : (cacheWord prior old).length ≤ B+2 :=
      (cacheWord_length prior old).trans (by omega)
    have ht := ih (cacheWord prior old) (B+2) hn (by
      intro x h
      have hh := hx x (by simp [h]); omega)
    simpa [cacheLast,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ht

theorem cacheRecords_length_le (xs : List (List Bool)) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    (cacheRecords xs).length ≤ xs.length*(2*B+3) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hh := hx x (by simp)
    have ht := ih (by intro y h; exact hx y (by simp [h]))
    simp only [cacheRecords_cons,List.length_append,LayoutScalarEmitter.record_length,
      List.length_nil,Nat.add_zero,List.length_cons]
    nlinarith

theorem cachePass_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (counter : List Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 300*(xs.length+1)*(B+2*xs.length+4), ∃ r,
      Eval cachePass t
        (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (state r ([],counter) ([],[]) ([],[])
          (pairEncoding ((cacheScan [] xs).map fun x => (x,[])))) := by
  obtain ⟨tr,htr,r₁,_,hr⟩ := cacheRow_eval xs regs ([],counter) [] B (by simp) hx
  obtain ⟨r₂,hf⟩ := cacheFinishList_eval r₁
    ((cacheRecords (cacheScan [] xs)).reverse++[],counter) (cacheLast [] xs)
  have hc := cacheClear_eval r₂ ([],counter) (cacheLast [] xs)
    (((cacheRecords (cacheScan [] xs)).reverse++[]).reverse++[false])
  have hout : ((cacheRecords (cacheScan [] xs)).reverse++[]).reverse++[false] =
      pairEncoding ((cacheScan [] xs).map fun x => (x,[])) := by
    simpa using (cacheRecords_encoding (cacheScan [] xs)).symm
  have hword := cacheScan_word_length [] xs B (by simp) hx
  have hlen := cacheRecords_length_le (cacheScan [] xs) (B+2*xs.length) hword
  rw [cacheScan_length] at hlen
  have hlast := cacheLast_length [] xs B (by simp) hx
  refine ⟨tr+((3*((cacheRecords (cacheScan [] xs)).reverse++[]).length+9)+
      (2*(cacheLast [] xs).length+3)),?_,readRegs r₂ 0 1 none,?_⟩
  · simp only [List.length_append,List.length_reverse,List.length_nil,Nat.add_zero]
    let inner := B + 2 * xs.length + 4
    have hinner : 1 ≤ inner := by dsimp [inner]; omega
    have hrec : (cacheRecords (cacheScan [] xs)).length ≤
        2 * xs.length * inner := by
      calc
        (cacheRecords (cacheScan [] xs)).length ≤
            xs.length * (2 * (B + 2 * xs.length) + 3) := hlen
        _ ≤ xs.length * (2 * inner) := by
          apply Nat.mul_le_mul_left
          dsimp [inner]
          omega
        _ = 2 * xs.length * inner := by ring
    have hlast' : (cacheLast [] xs).length ≤ inner := by
      exact hlast.trans (by dsimp [inner]; omega)
    have hrec3 := Nat.mul_le_mul_left 3 hrec
    have hlast2 := Nat.mul_le_mul_left 2 hlast'
    have hconst : 12 ≤ 12 * inner := by omega
    have hover : 3 * (cacheRecords (cacheScan [] xs)).length + 9 +
        (2 * (cacheLast [] xs).length + 3) ≤
          100 * (xs.length + 1) * inner := by
      calc
        3 * (cacheRecords (cacheScan [] xs)).length + 9 +
              (2 * (cacheLast [] xs).length + 3) =
            (3 * (cacheRecords (cacheScan [] xs)).length +
              2 * (cacheLast [] xs).length) + 12 := by omega
        _ ≤ (3 * (2 * xs.length * inner) + 2 * inner) + 12 :=
          Nat.add_le_add_right (Nat.add_le_add hrec3 hlast2) 12
        _ = 6 * xs.length * inner + 2 * inner + 12 := by ring
        _ ≤ 6 * xs.length * inner + 2 * inner + 12 * inner := by omega
        _ = (6 * xs.length + 14) * inner := by ring
        _ ≤ (100 * (xs.length + 1)) * inner :=
          Nat.mul_le_mul_right inner (by omega)
        _ = 100 * (xs.length + 1) * inner := by ring
    calc
      tr + (3 * (cacheRecords (cacheScan [] xs)).length + 9 +
          (2 * (cacheLast [] xs).length + 3)) ≤
        200 * (xs.length + 1) * inner + 100 * (xs.length + 1) * inner :=
          Nat.add_le_add htr hover
      _ = 300 * (xs.length + 1) * (B + 2 * xs.length + 4) := by
        dsimp [inner]
        ring
  · simpa only [hout] using hr.seq (hf.seq hc)

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The number of coefficient-cache rows is runtime unary data. This fixed
loop invokes the complete paid row pass and preserves the current encoded row.
-/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheRead_eval (regs : Fin 8 → Bool) (counter : List Bool)
    (xs : List (List Bool)) :
    Eval cacheRead 1
      (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
      (cacheAfterRead regs counter xs) := by
  convert (Eval.base (StructuredProgram.Eval.atom (.pop (17 : Fin 18) (7 : Fin 8) 6)
    (state regs ([],counter) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))))) using 1
  all_goals try with_reducible_and_instances rfl
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext j
    fin_cases j <;>
      simp [state,StructuredProgram.Atom.instr,execInstr]

theorem cacheLoop_eval (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(counter.length+1)*(xs.length+1)*(B+2*counter.length*xs.length+4),
    ∃ r, Eval cacheLoop t (cacheAfterRead regs counter xs)
      (state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((cacheIter counter.length xs).map fun x => (x,[])))) := by
  induction counter generalizing xs regs B with
  | nil =>
    refine ⟨1,by simp; nlinarith,readRegs regs 7 6 none,?_⟩
    simpa [cacheLoop,cacheAfterRead,cacheIter] using
      (Eval.while_false (test := (6 : Fin 8)) (body := .seq cachePass cacheRead)
        (a := cacheAfterRead regs [] xs)
        (by simp [cacheAfterRead,state,readRegs_present]))
  | cons bit counter ih =>
    let rr := readRegs regs 7 6 (some bit)
    obtain ⟨tp,htp,rp,hp⟩ := cachePass_eval xs rr counter B hx
    have hr := cacheRead_eval rp counter (cacheScan [] xs)
    have hscan := cacheScan_word_length [] xs B (by simp) hx
    obtain ⟨tl,htl,rl,hl⟩ := ih (cacheScan [] xs) rp (B+2*xs.length) hscan
    refine ⟨tp+1+tl+1,?_,rl,?_⟩
    · rw [cacheScan_length] at htl
      simp only [List.length_cons]
      have henv : B+2*xs.length+2*counter.length*xs.length+4 =
          B+2*(counter.length+1)*xs.length+4 := by ring
      rw [henv] at htl
      have he : B+2*xs.length+4 ≤ B+2*(counter.length+1)*xs.length+4 := by nlinarith
      have hprod := Nat.mul_le_mul_left (300*(xs.length+1)) he
      nlinarith
    · have he := Eval.while_true (test := (6 : Fin 8))
        (by simp [state,rr,readRegs_present]) (hp.seq hr) hl
      simpa [cacheLoop,cacheAfterRead,cacheIter,rr] using he

theorem cacheProgram_runsIn (counter : List Bool) (xs : List (List Bool))
    (regs : Fin 8 → Bool) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ r, RunsIn cacheProgram
      (400*(counter.length+1)*(xs.length+1)*(B+2*counter.length*xs.length+4)+2)
      ((state regs ([],counter) ([],[]) ([],[])
        (pairEncoding (xs.map fun x => (x,[])))).withPC (some cacheProgram.entry))
      ((state r ([],[]) ([],[]) ([],[])
        (pairEncoding ((cacheIter counter.length xs).map fun x => (x,[])))).withPC none) := by
  obtain ⟨t,ht,r,he⟩ := cacheLoop_eval counter xs regs B hx
  refine ⟨r,1+t+1,by omega,?_⟩
  exact compiled_halt_trace ((cacheRead_eval regs counter xs).seq he) 17 15

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

/-! The physical unsigned cache computes the original coefficient recurrence's
natural magnitudes, in ascending degree order. -/

/-! A fixed loop builds the initial all-one cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned H cache from the unary
runtime parameters A and R. No coefficient or initial cache is free input. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgramScalar

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem cacheBuildPorts_injective : Function.Injective cacheBuildPorts := Fin.castAdd_injective _ _

theorem cacheBuildLoop_eval_oai (regs : Fin 8 → Bool) (a : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 400*(a.length+1)*(xs.length+1)*(B+2*a.length*xs.length+4)+2,
    ∃ regs', Eval cacheBuildLoop t
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[])))) := by
  obtain ⟨regs',t,ht,he⟩ := cacheProgram_runsIn a xs regs B hx
  have hs : embedState id cacheBuildPorts
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (state regs ([],a) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))) =
      buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))) := by
    apply embedState_eq_of_ports id cacheBuildPorts _ _ _
      Function.injective_id cacheBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,cacheBuildPorts]
    · intro i hi; rfl
  have hf : embedState id cacheBuildPorts
      (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
      (state regs' ([],[]) ([],[]) ([],[])
        (pairEncoding ((cacheIter a.length xs).map fun x => (x,[])))) =
      buildState regs' [] [] (pairEncoding ((cacheIter a.length xs).map fun x => (x,[]))) := by
    apply embedState_eq_of_ports id cacheBuildPorts _ _ _
      Function.injective_id cacheBuildPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [buildState,state,cacheBuildPorts]
    · intro i hi
      have hrange : ∀ j : Fin 19, j ≠ 18 → j ∈ Set.range cacheBuildPorts := by decide
      have hj : i = 18 := by by_contra h; exact hi (hrange i h)
      subst i
      simp [buildState]
  have h := eval_call_lifted cacheProgram id cacheBuildPorts
    (buildState regs a [] (pairEncoding (xs.map fun x => (x,[]))))
    Function.injective_id cacheBuildPorts_injective he
  rw [hs,hf] at h
  exact ⟨t,ht,regs',h⟩

end SubexponentialSAT.SqrtLog.LayoutProgramScalar

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgramScalar.cacheBuildLoop_eval_oai
