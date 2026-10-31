-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:01:58.029339+00:00
-- url     : https://prove2.me/submissions/4068bfbd-abbb-4c67-97a4-489401f927d8

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S142

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramNormalize
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime-width normalization for signed-component matrix words. This uses
only the existing padding, clear and transfer bit programs. In particular,
normalizing a component never invokes modular integer arithmetic. -/

namespace SubexponentialSAT.SqrtLog.LayoutProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.ModularArithmetic SubexponentialSAT.StackRoutines
open SubexponentialSAT.ModularRingPrograms

variable {s : ℕ}

private theorem normalize_embed_input (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) :
    embedState id ports d
      ⟨d.regs, normalizationState (d.stacks (ports 0)) (d.stacks (ports 7)) []
        (d.stacks (ports 5))⟩ = d := by
  apply embedState_eq_of_ports id ports d d _ Function.injective_id ports.injective
  · intro i; rfl
  · intro j hj; exact (hj ⟨j,rfl⟩).elim
  · intro i
    fin_cases i <;> simp [normalizationState] <;>
      try exact hd _ (by decide) (by decide) (by decide)
  · intro j hj; rfl

private theorem normalize_embed_output (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) (rf : Fin 8 → Bool) :
    embedState id ports d
      ⟨rf, normalizationState (padTo (d.stacks (ports 7)) (d.stacks (ports 0))) [] []
        (d.stacks (ports 5))⟩ = ⟨rf, normalizedStacks ports d⟩ := by
  apply embedState_eq_of_ports id ports d _ _ Function.injective_id ports.injective
  · intro i; rfl
  · intro j hj; exact (hj ⟨j,rfl⟩).elim
  · intro i
    have he (a b : Fin 8) : ports a = ports b ↔ a = b := ports.injective.eq_iff
    fin_cases i <;> simp [normalizedStacks, normalizationState, he] <;>
      try exact hd _ (by decide) (by decide) (by decide)
  · intro j hj
    have h0 : j ≠ ports 0 := fun h => hj ⟨0,h.symm⟩
    have h7 : j ≠ ports 7 := fun h => hj ⟨7,h.symm⟩
    simp [normalizedStacks, h0, h7]

/-- Even a long input with redundant zero bits is normalized by an actual
finite program. Both its source length and its requested width are paid. -/
theorem normalizeAt_eval (ports : Fin 8 ↪ Fin s) (d : State 8 s)
    (hd : normalizeReady ports d) :
    ∃ n ≤ 7 * (d.stacks (ports 7)).length + 2 * (d.stacks (ports 0)).length + 9,
    ∃ rf, Eval (normalizeAt ports) n d ⟨rf, normalizedStacks ports d⟩ := by
  obtain ⟨rf, n, hn, ht⟩ := normalize_correct d.regs
    (d.stacks (ports 0)) (d.stacks (ports 7)) (d.stacks (ports 5))
  have h := eval_call_lifted normalizeProgram id ports d
    Function.injective_id ports.injective
    (a := ⟨d.regs, normalizationState (d.stacks (ports 0)) (d.stacks (ports 7)) [] (d.stacks (ports 5))⟩)
    (b := ⟨rf, normalizationState (padTo (d.stacks (ports 7)) (d.stacks (ports 0))) [] [] (d.stacks (ports 5))⟩) ht
  refine ⟨n, hn, rf, ?_⟩
  simpa only [normalizeAt, normalize_embed_input ports d hd,
    normalize_embed_output ports d hd rf] using h

end SubexponentialSAT.SqrtLog.LayoutProgram

end OAI.Algorithms
end

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutBinomialProgramCell
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Consolidated fixed-control binomial-cache implementation. Component module
paths re-export this file so all interfaces remain stable. -/

/-! A Pascal cell saves the old entry, adds and emits the new entry, then
restores the saved entry as the carry. Every copy and clear is paid. -/

/-! One paid Pascal row pass over the framed cache. -/

/-! A fixed while loop consumes the runtime unary iteration count. -/

/-! A fixed loop builds the initial zero cache row from a runtime unary
length. The constant program contains one record, independent of that length. -/

/-! One fixed program builds the complete unsigned binomial row from the unary
runtime parameters h and R. No coefficient or initial cache is free input. -/

/-! A fixed component routine copies the runtime width, pads or truncates one
word, and consumes that word into a reverse output buffer. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.LayoutProgram

theorem normalizeComponent_eval (regs : Fin 8 → Bool) (word width buffer : List Bool) :
    ∃ t ≤ 17*width.length+2*word.length+17, ∃ r,
      Eval normalizeComponent t (normalizeState regs word width buffer)
        (normalizeState r [] width ((ModularArithmetic.padTo width word).reverse++buffer)) := by
  let d := normalizeState regs word width buffer
  obtain ⟨a,ha,hsa⟩ := copy_eval (1 : Fin 9) 3 4
    (by decide) (by decide) (by decide) d (by simp [d,normalizeState])
  have has : a.stacks = ![word,width,buffer,width,[],[],[],[],[]] := by
    rw [hsa]
    funext j; fin_cases j <;> simp [d,normalizeState,StackRoutines.copyStacks]
  have har : normalizeReady normalizePorts a := by
    intro i h0 h5 h7
    fin_cases i <;> simp [normalizePorts,has] at h0 h5 h7 ⊢
  obtain ⟨tn,htn,rn,hn⟩ := normalizeAt_eval normalizePorts a har
  let b : NormalizeData := ⟨rn,normalizedStacks normalizePorts a⟩
  have hbs : b.stacks = ![ModularArithmetic.padTo width word,width,buffer,[],[],[],[],[],[]] := by
    funext j; fin_cases j <;> simp [b,normalizedStacks,normalizePorts,has]
  obtain ⟨e,he,hse⟩ := transfer_eval (0 : Fin 9) 2 (by decide) b
  have hout : e = normalizeState e.regs [] width
      ((ModularArithmetic.padTo width word).reverse++buffer) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hse,hbs]
    funext j; fin_cases j <;> simp [StackRoutines.transferStacks]
  rw [hout] at he
  refine ⟨(7*width.length+5)+(tn+(3*width.length+3)),?_,e.regs,?_⟩
  · simp [normalizePorts,has] at htn
    omega
  · have hb0 : (b.stacks 0).length = width.length := by
      rw [hbs]
      exact ModularArithmetic.padTo_length width word
    have hh := ha.seq (hn.seq he)
    simpa [normalizeComponent,d,normalizeState,hb0] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Generic framed unsigned rows are converted to flat signed-component
arrays at a supplied runtime width. Both output arrays are physically built.
-/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.LayoutProgramScalar
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem basePorts_injective : Function.Injective basePorts := Fin.castAdd_injective _ _

theorem embed_wide (width : List Bool) (a b : State 8 18) :
    embedState id basePorts (wide width a) b = wide width b := by
  apply embedState_eq_of_ports id basePorts _ _ _ Function.injective_id basePorts_injective
  · intro i; rfl
  · intro i hi; exact (hi ⟨i,rfl⟩).elim
  · intro i; simp [wide,basePorts]
  · intro i hi
    have hh : ¬i.val < 18 := by
      intro h
      exact hi ⟨⟨i.val,h⟩,by apply Fin.ext; rfl⟩
    simp [wide,hh]

theorem wide_eval {c : Cmd 8 18} {n : ℕ} {a b : State 8 18}
    (h : Eval c n a b) (width : List Bool) :
    Eval (liftCommand c 15 15 id basePorts) (n+1) (wide width a) (wide width b) := by
  have hh := eval_liftCommand h 15 15 id basePorts (wide width a)
    Function.injective_id basePorts_injective
  simpa only [embed_wide] using hh

theorem positivePorts_injective : Function.Injective positivePorts := by decide
theorem negativePorts_injective : Function.Injective negativePorts := by decide

theorem flatPositive_eval (regs : Fin 8 → Bool) (width : List Bool)
    (acc : WordPair) (positive negative queue : List Bool) :
    ∃ t ≤ 17*width.length+2*positive.length+18, ∃ r,
      Eval flatPositive t (flatState regs width acc ([],[]) (positive,negative) queue)
        (flatState r width ((ModularArithmetic.padTo width positive).reverse++acc.1,acc.2)
          ([],[]) ([],negative) queue) := by
  obtain ⟨t,ht,r,he⟩ := normalizeComponent_eval regs positive width acc.1
  have hs : embedState id positivePorts
      (flatState regs width acc ([],[]) (positive,negative) queue)
      (normalizeState regs positive width acc.1) =
      flatState regs width acc ([],[]) (positive,negative) queue := by
    apply embedState_eq_of_ports id positivePorts _ _ _
      Function.injective_id positivePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,positivePorts,normalizeState]
    · intro i hi; rfl
  have hf : embedState id positivePorts
      (flatState regs width acc ([],[]) (positive,negative) queue)
      (normalizeState r [] width ((ModularArithmetic.padTo width positive).reverse++acc.1)) =
      flatState r width ((ModularArithmetic.padTo width positive).reverse++acc.1,acc.2)
        ([],[]) ([],negative) queue := by
    apply embedState_eq_of_ports id positivePorts _ _ _
      Function.injective_id positivePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,positivePorts,normalizeState]
    · intro i hi
      have h2 : i ≠ 2 := fun h => hi ⟨0,by simpa [positivePorts] using h.symm⟩
      have h16 : i ≠ 16 := fun h => hi ⟨2,by simpa [positivePorts] using h.symm⟩
      fin_cases i <;> simp [flatState,wide,state] at h2 h16 ⊢
  have hh := eval_liftCommand he 0 2 id positivePorts
    (flatState regs width acc ([],[]) (positive,negative) queue)
    Function.injective_id positivePorts_injective
  rw [hs,hf] at hh
  exact ⟨t+1,by omega,r,hh⟩

theorem flatNegative_eval (regs : Fin 8 → Bool) (width : List Bool)
    (acc : WordPair) (negative queue : List Bool) :
    ∃ t ≤ 17*width.length+2*negative.length+18, ∃ r,
      Eval flatNegative t (flatState regs width acc ([],[]) ([],negative) queue)
        (flatState r width (acc.1,(ModularArithmetic.padTo width negative).reverse++acc.2)
          ([],[]) ([],[]) queue) := by
  obtain ⟨t,ht,r,he⟩ := normalizeComponent_eval regs negative width acc.2
  have hs : embedState id negativePorts
      (flatState regs width acc ([],[]) ([],negative) queue)
      (normalizeState regs negative width acc.2) =
      flatState regs width acc ([],[]) ([],negative) queue := by
    apply embedState_eq_of_ports id negativePorts _ _ _
      Function.injective_id negativePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,negativePorts,normalizeState]
    · intro i hi; rfl
  have hf : embedState id negativePorts
      (flatState regs width acc ([],[]) ([],negative) queue)
      (normalizeState r [] width ((ModularArithmetic.padTo width negative).reverse++acc.2)) =
      flatState r width (acc.1,(ModularArithmetic.padTo width negative).reverse++acc.2)
        ([],[]) ([],[]) queue := by
    apply embedState_eq_of_ports id negativePorts _ _ _
      Function.injective_id negativePorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [flatState,wide,state,negativePorts,normalizeState]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨0,by simpa [negativePorts] using h.symm⟩
      have h17 : i ≠ 17 := fun h => hi ⟨2,by simpa [negativePorts] using h.symm⟩
      fin_cases i <;> simp [flatState,wide,state] at h3 h17 ⊢
  have hh := eval_liftCommand he 0 2 id negativePorts
    (flatState regs width acc ([],[]) ([],negative) queue)
    Function.injective_id negativePorts_injective
  rw [hs,hf] at hh
  exact ⟨t+1,by omega,r,hh⟩

theorem flatRow_eval (xs : List (List Bool)) (regs : Fin 8 → Bool)
    (width : List Bool) (acc : WordPair) (B : ℕ)
    (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 100*(xs.length+1)*(width.length+B+4), ∃ r,
      r 7 = false ∧
      Eval flatRow t
        (flatState regs width acc ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[]))))
        (flatState r width ((flatWords width xs).reverse++acc.1,
          (flatZeros width xs).reverse++acc.2) ([],[]) ([],[]) []) := by
  induction xs generalizing regs acc with
  | nil =>
    obtain ⟨r,hg,he⟩ := parse_nil regs acc ([],[])
    have hh := wide_eval he width
    refine ⟨5,by simp; omega,r,hg,?_⟩
    simpa [flatRow,flatParse,flatState,flatWords,flatZeros] using hh.seq (.while_false hg)
  | cons x xs ih =>
    have hx0 := hx x (by simp)
    obtain ⟨r₁,hg₁,hp₁⟩ := parse_cons regs acc ([],[]) (x,[]) (xs.map fun x => (x,[]))
    have hp := wide_eval hp₁ width
    obtain ⟨tp,htp,r₂,hp₂⟩ := flatPositive_eval r₁ width acc x []
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tn,htn,r₃,hn₃⟩ := flatNegative_eval r₂ width
      ((ModularArithmetic.padTo width x).reverse++acc.1,acc.2) []
      (pairEncoding (xs.map fun x => (x,[])))
    obtain ⟨tt,htt,r₄,hg₄,ht⟩ := ih r₃
      ((ModularArithmetic.padTo width x).reverse++acc.1,
        (ModularArithmetic.padTo width []).reverse++acc.2)
      (fun y hy => hx y (by simp [hy]))
    cases ht with
    | seq hparse hwhile =>
      rename_i tparse twhile between
      refine ⟨(6*pairLength (x,[])+12)+(tp+tn+tparse+twhile+1),?_,r₄,hg₄,?_⟩
      · simp only [pairLength,List.length_nil,Nat.add_zero,List.length_cons] at *
        nlinarith only [htp, htn, htt, hx0, Nat.zero_le B, Nat.zero_le xs.length,
          Nat.zero_le width.length, Nat.zero_le x.length]
      · have hh := hp.seq (.while_true hg₁ (hp₂.seq (hn₃.seq hparse)) hwhile)
        simpa [flatRow,flatParse,flatState,flatWords,flatZeros,List.flatMap_cons,
          List.reverse_append,List.append_assoc,Nat.add_assoc] using hh

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Finish the generic cache adapter by reversing both physically accumulated
arrays. The common width is preserved for downstream indexed reads. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.Subexp.MatrixProgramSupport
open SubexponentialSAT.SqrtLog.RowSelectionProgram
open SubexponentialSAT.SqrtLog.LayoutProgramScalar

theorem flatFinish_eval (regs : Fin 8 → Bool) (width positive negative : List Bool) :
    ∃ r, Eval flatFinish (3*positive.length+3*negative.length+6)
      (flatState regs width (positive,negative) ([],[]) ([],[]) [])
      (flatState r width ([],[]) (positive.reverse,negative.reverse) ([],[]) []) := by
  let d := flatState regs width (positive,negative) ([],[]) ([],[]) []
  obtain ⟨a,ha,hsa⟩ := transfer_eval (16 : Fin 19) 0 (by decide) d
  obtain ⟨b,hb,hsb⟩ := transfer_eval (17 : Fin 19) 1 (by decide) a
  have han : a.stacks 17 = negative := by
    rw [hsa]; simp [d,flatState,wide,state,StackRoutines.transferStacks]
  have hout : b = flatState b.regs width ([],[]) (positive.reverse,negative.reverse) ([],[]) [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    rw [hsb,hsa]
    funext j
    fin_cases j <;> simp [d,flatState,wide,state,StackRoutines.transferStacks]
  rw [hout] at hb
  refine ⟨b.regs,?_⟩
  have hh := ha.seq hb
  have htime : (3*(d.stacks 16).length+3)+(3*(a.stacks 17).length+3) =
      3*positive.length+3*negative.length+6 := by
    simp only [han]
    have hd : d.stacks 16 = positive := by simp [d,flatState,wide,state]
    rw [hd]
    omega
  rw [htime] at hh
  simpa only [flatFinish,d] using hh

theorem flatProgram_runsIn (regs : Fin 8 → Bool) (width : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ r, RunsIn flatProgram (110*(xs.length+1)*(width.length+B+4)+7)
      ((flatState regs width ([],[]) ([],[]) ([],[])
        (pairEncoding (xs.map fun x => (x,[])))).withPC (some flatProgram.entry))
      ((flatState r width ([],[]) (flatWords width xs,flatZeros width xs) ([],[]) []).withPC none) := by
  obtain ⟨tr,htr,rr,_,hr⟩ := flatRow_eval xs regs width ([],[]) B hx
  obtain ⟨rf,hf⟩ := flatFinish_eval rr width (flatWords width xs).reverse (flatZeros width xs).reverse
  simp only [List.append_nil] at hr
  simp only [List.reverse_reverse,List.length_reverse,flatWords_length,flatZeros_length] at hf
  refine ⟨rf,tr+(3*(xs.length*width.length)+3*(xs.length*width.length)+6)+1,?_,?_⟩
  · nlinarith only [htr, Nat.zero_le B, Nat.zero_le xs.length, Nat.zero_le width.length]
  · exact compiled_halt_trace (hr.seq hf) 15 0

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

/-! Value and shape contracts for the generic adapter and binomial row. -/

/-! Complete fixed-control binomial cache construction. The three parameters
are runtime unary stacks; the output consists of actual flat fixed-width
positive and negative arrays in increasing column order. -/
namespace SubexponentialSAT.SqrtLog.LayoutBinomialProgram

attribute [local simp] Fin.coe_ofNat_eq_mod

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem flatFinalPorts_injective : Function.Injective flatFinalPorts := by decide

theorem finalFlatten_eval_oai (regs : Fin 8 → Bool) (width : List Bool)
    (xs : List (List Bool)) (B : ℕ) (hx : ∀ x ∈ xs, x.length ≤ B) :
    ∃ t ≤ 110*(xs.length+1)*(width.length+B+4)+7, ∃ regs',
      Eval finalFlatten t
        (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
        (finalState regs' [] [] width [] (flatWords width xs) (flatZeros width xs)) := by
  obtain ⟨rf,t,ht,he⟩ := flatProgram_runsIn regs width xs B hx
  have hs : embedState id flatFinalPorts
      (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
      (flatState regs width ([],[]) ([],[]) ([],[]) (pairEncoding (xs.map fun x => (x,[])))) =
      finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [] := by
    apply embedState_eq_of_ports id flatFinalPorts _ _ _ Function.injective_id flatFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,flatState,wide,LayoutProgramScalar.state,flatFinalPorts]
    · intro i hi; rfl
  have hf : embedState id flatFinalPorts
      (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
      (flatState rf width ([],[]) (flatWords width xs,flatZeros width xs) ([],[]) []) =
      finalState rf [] [] width [] (flatWords width xs) (flatZeros width xs) := by
    apply embedState_eq_of_ports id flatFinalPorts _ _ _ Function.injective_id flatFinalPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i,rfl⟩).elim
    · intro i; fin_cases i <;> simp [finalState,flatState,wide,LayoutProgramScalar.state,flatFinalPorts]
    · intro i hi
      have hrange : ∀ j : Fin 20, j≠18 → j∈Set.range flatFinalPorts := by decide
      have hj : i=18 := by
        by_contra hn
        exact hi (hrange i hn)
      subst i; simp [finalState]
  have hh := eval_call_lifted flatProgram id flatFinalPorts
    (finalState regs [] [] width (pairEncoding (xs.map fun x => (x,[]))) [] [])
    Function.injective_id flatFinalPorts_injective he
  rw [hs,hf] at hh
  exact ⟨t,ht,rf,hh⟩

end SubexponentialSAT.SqrtLog.LayoutBinomialProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutBinomialProgram.finalFlatten_eval_oai
