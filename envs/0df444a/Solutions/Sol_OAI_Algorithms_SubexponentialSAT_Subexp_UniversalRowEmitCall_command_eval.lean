-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:19:11.623597+00:00
-- url     : https://prove2.me/submissions/75bdec44-5ce5-4f46-9e41-39f5ef82272a

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ParserProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control parsers for the canonical formula encoding

These programs operate on two Boolean stacks and two Boolean registers.
Stack 0 is input; stack 1 accumulates output. Register 0 holds the last data
bit and register 1 records whether the last pop succeeded. Thus register 1
is true on successful delimiter termination and false on malformed input.
All stated running times count actual `BitProgram.step` transitions.
-/

namespace SubexponentialSAT.ParserProgram

open SubexponentialSAT.BitProgram

/-! ## In-place removal of one escape frame -/

theorem restore_trace (input output : List Bool) (v p : Bool) :
    Trace restoreProgram (3 * output.length + 3)
      (cfg (some 0) v p input output)
      (cfg none false false (output.reverse ++ input) []) := by
  have h := StackRoutines.transferProgram_trace (r := 2) (s := 2)
    1 0 0 1 (by decide) (by decide) (pair v p) (pair input output)
  have ht : Trace restoreProgram (3 * output.length + 2)
      (cfg (some 0) v p input output)
      (cfg (some 3) false false (output.reverse ++ input) []) := by
    simpa [restoreProgram, cfg, StackRoutines.transferResult,
      StackRoutines.transferStacks, readRegs] using h
  have hh : step restoreProgram (cfg (some 3) false false (output.reverse ++ input) []) =
      some (cfg none false false (output.reverse ++ input) []) := by
    simp [step, cfg, execInstr]
  simpa [Nat.add_assoc] using ht.trans (.cons hh (.refl _))

/-- The linked finite table restores forward order and clears its scratch stack. -/
theorem unframe_trace (bits rest : List Bool) (v p : Bool) :
    Trace unframeProgram (9 * bits.length + 7)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false false (bits ++ rest) []) := by
  have hp : Trace frameProgram (6 * bits.length + 4)
      (cfg (some 0) v p (Encoding.frame bits ++ rest) [])
      (cfg none false true rest bits.reverse) := by
    simpa using frame_trace bits rest [] v p
  have hq : Trace restoreProgram (3 * bits.length + 3)
      (ProgramLinking.enter restoreProgram (cfg (l := 7) none false true rest bits.reverse))
      (cfg none false false (bits ++ rest) []) := by
    simpa [ProgramLinking.enter, restoreProgram, StackRoutines.transferProgram, cfg]
      using restore_trace rest bits.reverse false true
  have h := ProgramLinking.link_trace frameProgram restoreProgram hp rfl hq
  have hc : (6 * bits.length + 4) + (3 * bits.length + 3) = 9 * bits.length + 7 := by omega
  have hzero : Fin.castAdd 4 (0 : Fin 7) = (0 : Fin 11) := rfl
  simpa only [hc, unframeProgram, ProgramLinking.relabelCfg, ProgramLinking.relocatePc,
    hzero, cfg]
    using h

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpHornerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control source generation for factored Horner expressions

Input payloads are coefficient representations, never precomputed instruction
streams. The emitter writes the actual serialized postfix tags and frames.
-/

namespace SubexponentialSAT.SubexpHornerProgram

open BitProgram

namespace Literal

theorem prefix_trace (payload out : List Bool) (v p c : Bool) :
    Trace program 3 (cfg (some 0) v p c payload out [])
      (cfg (some 3) false p true payload (false :: out) []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, triple]

theorem copy_cycle (b v p : Bool) (bs out scratch : List Bool) :
    Trace program 5 (cfg (some 3) v p true (b :: bs) out scratch)
      (cfg (some 3) b true true bs (b :: true :: out) (b :: scratch)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_finish (v p : Bool) (out scratch : List Bool) :
    Trace program 3 (cfg (some 3) v p true [] out scratch)
      (cfg (some 9) false false true [] (false :: out) scratch) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem copy_trace (payload out scratch : List Bool) (v p : Bool) :
    Trace program (5 * payload.length + 3)
      (cfg (some 3) v p true payload out scratch)
      (cfg (some 9) false false true []
        ((Encoding.frame payload).reverse ++ out) (payload.reverse ++ scratch)) := by
  induction payload generalizing out scratch v p with
  | nil => simpa [Encoding.frame] using copy_finish v p out scratch
  | cons b bs ih =>
      have h := (copy_cycle b v p bs out scratch).trans
        (ih (b :: true :: out) (b :: scratch) b true)
      convert h using 1 <;>
        simp [Encoding.frame, List.reverse_cons, List.append_assoc] ; omega

theorem restore_cycle (b v p : Bool) (bs payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out (b :: bs))
      (cfg (some 9) b true true (b :: payload) out bs) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_finish (v p : Bool) (payload out : List Bool) :
    Trace program 3 (cfg (some 9) v p true payload out [])
      (cfg none false false true payload out []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, cfg, step, program, execInstr, readRegs, triple]

theorem restore_trace (scratch payload out : List Bool) (v p : Bool) :
    Trace program (3 * scratch.length + 3)
      (cfg (some 9) v p true payload out scratch)
      (cfg none false false true (scratch.reverse ++ payload) out []) := by
  induction scratch generalizing payload v p with
  | nil => simpa using restore_finish v p payload out
  | cons b bs ih =>
      have h := (restore_cycle b v p bs payload out).trans (ih (b :: payload) b true)
      convert h using 1 <;> simp [List.reverse_cons, List.append_assoc] ; omega

/-- Copy a raw literal payload, frame it, and emit its push opcode. The
payload is restored exactly and the scratch port is again empty. -/
theorem trace (payload out : List Bool) (v p c : Bool) :
    Trace program (8 * payload.length + 9)
      (cfg (some 0) v p c payload out [])
      (cfg none false false true payload
        ((false :: Encoding.frame payload).reverse ++ out) []) := by
  have hc := copy_trace payload (false :: out) [] false p
  simp only [List.append_nil] at hc
  have hr := restore_trace payload.reverse []
    ((Encoding.frame payload).reverse ++ false :: out) false false
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := (prefix_trace payload out v p c).trans (hc.trans hr)
  convert h using 1 <;> (try simp [List.reverse_cons, List.append_assoc]) ; omega

end Literal

end SubexponentialSAT.SubexpHornerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpKernelControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# A fixed controller constructing the separated postfix source

The input contains literal payloads and the three nested lists of blocks,
color groups, and terms.  The controller only parses frames, copies bits,
and emits postfix tags.  It has no arithmetic callback and never builds a
Cartesian product of the inner lists.  Three unary stacks hold the pending
right-fold operators, so the emitted source has exactly the association of
`SubexpAlgorithm.momentExpression`.
-/

namespace SubexponentialSAT.SubexpKernelControl

open BitProgram StructuredCalls

theorem operators_succ (mul : Bool) (n : ℕ) :
    operators mul (n + 1) = operators mul n ++ operator mul := by
  simp [operators, List.replicate_succ', List.flatten_append]

/-! ## Fixed source-constructor control -/

local infixr:60 " ;; " => Cmd.seq

/-! ## Concrete machine states and elementary traces -/

theorem emit_emit (x y : Word) (a : Accumulator) : emit y (emit x a) = emit (x ++ y) a := by
  cases a
  simp [emit, List.reverse_append, List.append_assoc]

theorem popTag_eval (b v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval popTag 1 (state v p (b :: source) zero one a)
      (state b true source zero one a) := by
  have h : (StructuredProgram.Atom.pop (0 : Fin 8) (0 : Fin 3) 1).eval
      (state v p (b :: source) zero one a) = state b true source zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, readRegs, state, SubexpHornerProgram.triple]
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state]
  rw [← h]
  exact .base (.atom _ _)

theorem setValue_eval (b v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.set 0 b)) 1 (state v p source zero one a)
      (state b p source zero one a) := by
  have h : (StructuredProgram.Atom.set (s := 8) (0 : Fin 3) b).eval
      (state v p source zero one a) = state b p source zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
    · rfl
  rw [← h]
  exact .base (.atom _ _)

theorem pushValue_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.push 3 0)) 1 (state v p source zero one a)
      (state v p source zero one { a with output := v :: a.output }) := by
  have h : (StructuredProgram.Atom.push (3 : Fin 8) (0 : Fin 3)).eval
      (state v p source zero one a) =
      state v p source zero one { a with output := v :: a.output } := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
  rw [← h]
  exact .base (.atom _ _)

theorem pushTrue_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (atom (.push 3 2)) 1 (state v p source zero one a)
      (state v p source zero one { a with output := true :: a.output }) := by
  have h : (StructuredProgram.Atom.push (3 : Fin 8) (2 : Fin 3)).eval
      (state v p source zero one a) =
      state v p source zero one { a with output := true :: a.output } := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i
      fin_cases i <;> simp [ StructuredProgram.Atom.instr,
        execInstr, state, SubexpHornerProgram.triple]
  rw [← h]
  exact .base (.atom _ _)

theorem emitOperator_eval (mul v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (emitOperator mul) (if mul then 2 else 3)
      (state v p source zero one a)
      (state (if mul then v else false) p source zero one (emit (operator mul) a)) := by
  cases mul
  · simpa [emitOperator, emit, operator] using
      Eval.seq (pushTrue_eval v p source zero one a)
        (Eval.seq (setValue_eval false v p source zero one { a with output := true :: a.output })
          (pushValue_eval false p source zero one { a with output := true :: a.output }))
  · simpa [emitOperator, emit, operator] using
      Eval.seq (pushTrue_eval v p source zero one a)
        (pushTrue_eval v p source zero one { a with output := true :: a.output })

private theorem extend_pair {α β : Type} [DecidableEq α] (x y : α) (hxy : x ≠ y)
    (a b : β) (base : α → β) :
    Function.extend (ParserProgram.pair x y) (ParserProgram.pair a b) base =
      Function.update (Function.update base x a) y b := by
  classical
  have hinj : Function.Injective (ParserProgram.pair x y) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [ParserProgram.pair, Ne.symm hxy]
  funext z
  by_cases hx : z = x
  · subst z
    have h := hinj.extend_apply (ParserProgram.pair a b) base (0 : Fin 2)
    simpa [ParserProgram.pair, hxy] using h
  · by_cases hy : z = y
    · subst z
      have h := hinj.extend_apply (ParserProgram.pair a b) base (1 : Fin 2)
      simpa [ParserProgram.pair] using h
    · have hout : ¬ ∃ i, ParserProgram.pair x y i = z := by
        rintro ⟨i, hi⟩
        fin_cases i <;> simp [ParserProgram.pair] at hi <;> subst z <;> contradiction
      rw [Function.extend_apply' _ _ _ hout]
      simp [hx, hy]

private theorem extend_triple {α β : Type} [DecidableEq α] (x y z : α)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (a b c : β) (base : α → β) :
    Function.extend (SubexpHornerProgram.triple x y z)
        (SubexpHornerProgram.triple a b c) base =
      Function.update (Function.update (Function.update base x a) y b) z c := by
  classical
  have hinj : Function.Injective (SubexpHornerProgram.triple x y z) := by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [SubexpHornerProgram.triple,
        Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
  funext w
  by_cases hwx : w = x
  · subst w
    have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (0 : Fin 3)
    simpa [SubexpHornerProgram.triple, hxy, hxz] using h
  · by_cases hwy : w = y
    · subst w
      have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (1 : Fin 3)
      simpa [SubexpHornerProgram.triple, hyz] using h
    · by_cases hwz : w = z
      · subst w
        have h := hinj.extend_apply (SubexpHornerProgram.triple a b c) base (2 : Fin 3)
        simpa [SubexpHornerProgram.triple] using h
      · have hout : ¬ ∃ i, SubexpHornerProgram.triple x y z i = w := by
          rintro ⟨i, hi⟩
          fin_cases i <;> simp [SubexpHornerProgram.triple] at hi <;>
            subst w <;> contradiction
        rw [Function.extend_apply' _ _ _ hout]
        simp [hwx, hwy, hwz]

private theorem registerMap_eq : registerMap = ParserProgram.pair (0 : Fin 3) 1 := by
  first | done | (funext i; fin_cases i <;> rfl)

private theorem embed_parser_scratch (v p v' p' : Bool) (src src' zero one : Word)
    (a : Accumulator) :
    embedState registerMap (pairMap 0 4) (state v p src zero one a)
      (parserState v' p' src' []) = state v' p' src' zero one a := by
  unfold embedState parserState
  rw [registerMap_eq]
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair 0 1) (ParserProgram.pair v' p') _)
    (Function.extend (ParserProgram.pair 0 4) (ParserProgram.pair src' []) _) = _
  rw [extend_pair _ _ (by decide), extend_pair _ _ (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [state, SubexpHornerProgram.triple]
  · funext i
    fin_cases i <;> simp [state]

theorem unframe_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval unframe (9 * bits.length + 7)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false false (bits ++ rest) zero one a) := by
  have h := eval_call_lifted ParserProgram.unframeProgram registerMap (pairMap 0 4)
    (state v p (Encoding.frame bits ++ rest) zero one a)
    (by decide) (by decide)
    (a := parserState v p (Encoding.frame bits ++ rest) [])
    (b := parserState false false (bits ++ rest) [])
    (ParserProgram.unframe_trace bits rest v p)
  simpa only [unframe, embed_parser_scratch] using h

private theorem embed_capture (v p v' p' : Bool) (src src' zero one out : Word)
    (a : Accumulator) :
    embedState registerMap (tripleMap 0 4 3) (state v p src zero one a)
      (captureState v' p' src' out) = state v' p' src' zero one { a with output := out } := by
  unfold embedState captureState
  rw [registerMap_eq]
  change StructuredProgram.State.mk
    (Function.extend (ParserProgram.pair 0 1) (ParserProgram.pair v' p') _)
    (Function.extend (SubexpHornerProgram.triple 0 4 3)
      (SubexpHornerProgram.triple src' [] out) _) = _
  rw [extend_pair _ _ (by decide),
    extend_triple _ _ _ (by decide) (by decide) (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    fin_cases i <;> simp [state, SubexpHornerProgram.triple]
  · funext i
    fin_cases i <;> simp [state]

theorem captureFrame_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval captureFrame (7 * bits.length + 5)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit (Encoding.frame bits) a)) := by
  have h := eval_call_lifted { ExecCNFRecords.captureProgram with entry := 4 }
    registerMap (tripleMap 0 4 3)
    (state v p (Encoding.frame bits ++ rest) zero one a)
    (by decide) (by decide)
    (a := captureState v p (Encoding.frame bits ++ rest) a.output)
    (b := captureState false true rest ((Encoding.frame bits).reverse ++ a.output))
    (ExecCNFRecords.capture_frame_trace bits rest [] a.output v p)
  simpa only [captureFrame, embed_capture, emit] using h

theorem emitFramedLiteral_eval (v p : Bool) (bits rest zero one : Word) (a : Accumulator) :
    Eval emitFramedLiteral (7 * bits.length + 7)
      (state v p (Encoding.frame bits ++ rest) zero one a)
      (state false true rest zero one (emit (pushWord bits) a)) := by
  have hs := setValue_eval false v p (Encoding.frame bits ++ rest) zero one a
  have hp := pushValue_eval false p (Encoding.frame bits ++ rest) zero one a
  have hc := captureFrame_eval false p bits rest zero one { a with output := false :: a.output }
  convert Eval.seq hs (Eval.seq hp hc) using 1 <;>
    simp [ emit, pushWord, List.reverse_cons, List.append_assoc, Nat.add_comm ] ; omega

private theorem extend_id {α β : Type*} (f base : α → β) : Function.extend id f base = f := by
  funext x
  exact Function.injective_id.extend_apply f base x

private theorem embed_literal (which v p v' p' : Bool) (src zero one out : Word)
    (a : Accumulator) :
    embedState id (tripleMap (if which then 2 else 1) 3 4) (state v p src zero one a)
      (literalState v' p' (if which then one else zero) out) =
      state v' p' src zero one { a with output := out } := by
  unfold embedState literalState
  rw [extend_id]
  change StructuredProgram.State.mk _
    (Function.extend (SubexpHornerProgram.triple (if which then 2 else 1) 3 4)
      (SubexpHornerProgram.triple (if which then one else zero) out []) _) = _
  rw [extend_triple _ _ _ (by cases which <;> decide)
    (by cases which <;> decide) (by decide)]
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    cases which <;> fin_cases i <;> simp [state]

theorem emitLiteral_eval (which v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval (emitLiteral (if which then 2 else 1))
      (8 * (if which then one else zero).length + 9)
      (state v p src zero one a)
      (state false false src zero one (emit (pushWord (if which then one else zero)) a)) := by
  have h := eval_call_lifted SubexpHornerProgram.Literal.program id
    (tripleMap (if which then 2 else 1) 3 4) (state v p src zero one a)
    Function.injective_id (by cases which <;> decide)
    (a := literalState v p (if which then one else zero) a.output)
    (b := literalState false false (if which then one else zero)
      ((pushWord (if which then one else zero)).reverse ++ a.output))
    (SubexpHornerProgram.Literal.trace (if which then one else zero) a.output v p true)
  simpa only [emitLiteral, embed_literal, emit] using h

theorem countOne_eval (i : Fin 3) (v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval (countOne (counterPort i)) 1 (state v p src zero one a)
      (state v p src zero one (setCounter i (true :: counterWord i a) a)) := by
  have h : (StructuredProgram.Atom.push (counterPort i) (2 : Fin 3)).eval
      (state v p src zero one a) =
      state v p src zero one (setCounter i (true :: counterWord i a) a) := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext j
      fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, state, SubexpHornerProgram.triple, counterPort, counterWord, setCounter]
  rw [← h]
  exact .base (.atom _ _)

theorem popCounter_eval (i : Fin 3) (word : Word) (v p : Bool)
    (src zero one : Word) (a : Accumulator) :
    Eval (atom (.pop (counterPort i) 0 1)) 1
      (state v p src zero one (setCounter i word a))
      (afterCounter i word src zero one a) := by
  have h : (StructuredProgram.Atom.pop (counterPort i) (0 : Fin 3) 1).eval
      (state v p src zero one (setCounter i word a)) =
      afterCounter i word src zero one a := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext j
      cases word <;> fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, readRegs, state, SubexpHornerProgram.triple,
          counterPort, setCounter]
    · funext j
      cases word <;> fin_cases i <;> fin_cases j <;>
        simp [ StructuredProgram.Atom.instr,
          execInstr, state, counterPort, setCounter]
  rw [← h]
  exact .base (.atom _ _)

theorem operators_cons (mul : Bool) (n : ℕ) :
    operator mul ++ operators mul n = operators mul (n + 1) := by
  simp [operators, List.replicate_succ, List.flatten_cons]

theorem drainLoop_eval (i : Fin 3) (mul : Bool) (word src zero one : Word) (a : Accumulator) :
    Eval (.while 1 (emitOperator mul ;; atom (.pop (counterPort i) 0 1)))
      ((if mul then 4 else 5) * word.length + 1)
      (afterCounter i word src zero one a)
      (state false false src zero one (emit (operators mul word.length) (setCounter i [] a))) := by
  induction word generalizing a with
  | nil =>
      simpa [afterCounter] using
        (Eval.while_false (test := (1 : Fin 3))
          (body := emitOperator mul ;; atom (.pop (counterPort i) 0 1))
          (a := state false false src zero one (setCounter i [] a)) (by rfl))
  | cons b bs ih =>
      have hop := emitOperator_eval mul b true src zero one (setCounter i bs a)
      have hpop := popCounter_eval i bs (if mul then b else false) true src zero one
        (emit (operator mul) a)
      rw [setCounter_emit] at hpop
      have hrest := ih (emit (operator mul) a)
      have hguard : (afterCounter i (b :: bs) src zero one a).regs 1 = true := by rfl
      have h := Eval.while_true hguard (Eval.seq hop hpop) hrest
      rw [setCounter_emit, emit_emit, operators_cons] at h
      cases mul <;> convert h using 1 <;>
        simp [ Nat.mul_add, Nat.add_left_comm, Nat.add_comm] <;> omega

theorem drain_eval (i : Fin 3) (mul : Bool) (word : Word) (v p : Bool)
    (src zero one : Word) (a : Accumulator) :
    Eval (drain (counterPort i) mul) ((if mul then 4 else 5) * word.length + 2)
      (state v p src zero one (setCounter i word a))
      (state false false src zero one (emit (operators mul word.length) (setCounter i [] a))) := by
  have h := Eval.seq (popCounter_eval i word v p src zero one a)
    (drainLoop_eval i mul word src zero one a)
  cases mul <;> convert h using 1 <;>
    simp [ Nat.add_comm] <;> omega

/-! The following induction rule accounts for actual executions of the fixed
payload body. Its premises will be proved for `termBody`, `groupBody`, and
`blockBody`; the exported whole-controller statement has no callback argument. -/

theorem popList_eval {α : Type*} (encode : α → Word) (xs : List α)
    (v p : Bool) (rest zero one : Word) (a : Accumulator) :
    Eval popTag 1 (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (afterTag encode xs rest zero one a) := by
  cases xs with
  | nil => simpa [afterTag, Encoding.encodeList] using popTag_eval false v p rest zero one a
  | cons x xs =>
      simpa [afterTag, Encoding.encodeList, List.append_assoc] using
        popTag_eval true v p (Encoding.frame (encode x) ++
          (Encoding.encodeList encode xs ++ rest)) zero one a

theorem scanLoop_eval {α : Type*} (body : Cmd 3 8) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scanLoop body) (1 + scanCost encode cost xs)
      (afterTag encode xs rest zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  induction xs generalizing a with
  | nil =>
      apply Eval.while_false
      simp [afterTag, state, SubexpHornerProgram.triple]
  | cons x xs ih =>
      let tail := Encoding.encodeList encode xs ++ rest
      have hread := unframe_eval true true (encode x) tail zero one a
      have hrun := hbody x tail a ha
      have hpop := popList_eval encode xs vb pb rest zero one (update x a)
      have hrest := ih (update x a) (hpreserve x a ha)
      have hguard : (afterTag encode (x :: xs) rest zero one a).regs 0 = true := by
        simp [afterTag, state, SubexpHornerProgram.triple]
      have hstep := Eval.seq hread (Eval.seq hrun hpop)
      have h := Eval.while_true hguard hstep hrest
      convert h using 1 <;>
        simp [ scanCost, List.foldl_cons,
          Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] ; omega

theorem scan_eval {α : Type*} (body : Cmd 3 8) (encode : α → Word)
    (cost : α → ℕ) (update : α → Accumulator → Accumulator)
    (invariant : Accumulator → Prop) (zero one : Word) (vb pb : Bool)
    (hbody : ∀ x rest a, invariant a →
      Eval body (cost x) (state false false (encode x ++ rest) zero one a)
        (state vb pb rest zero one (update x a)))
    (hpreserve : ∀ x a, invariant a → invariant (update x a))
    (xs : List α) (v p : Bool) (rest : Word) (a : Accumulator) (ha : invariant a) :
    Eval (scan body) (2 + scanCost encode cost xs)
      (state v p (Encoding.encodeList encode xs ++ rest) zero one a)
      (state false true rest zero one (xs.foldl (fun a x => update x a) a)) := by
  have hpop := popList_eval encode xs v p rest zero one a
  have hloop := scanLoop_eval body encode cost update invariant zero one vb pb
    hbody hpreserve xs rest a ha
  convert Eval.seq hpop hloop using 1 ; omega

theorem fold_bump_emit {α : Type*} (i : Fin 3) (code : α → Word)
    (xs : List α) (a : Accumulator) :
    xs.foldl (fun a x => bump i (emit (code x) a)) a =
      emit ((xs.map code).flatten)
        (setCounter i (List.replicate xs.length true ++ counterWord i a) a) := by
  induction xs generalizing a with
  | nil => simp
  | cons x xs ih =>
      rw [List.foldl_cons, ih]
      simp [bump, emit_emit, List.replicate_succ', List.append_assoc]

/-- The traversal count sums individual payload costs. No product of inner
list lengths occurs in the actual loop bound. -/
theorem scanCost_le_input {α : Type*} (encode : α → Word) (cost : α → ℕ)
    (xs : List α) (a b : ℕ) (hcost : ∀ x ∈ xs, cost x ≤ a * (encode x).length + b) :
    scanCost encode cost xs ≤ (a + b + 18) * (Encoding.encodeList encode xs).length := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := hcost x (by simp)
      have ht := ih (fun y hy => hcost y (by simp [hy]))
      simp only [scanCost, List.map_cons, List.sum_cons] at *
      rw [Encoding.length_encodeList_cons]
      nlinarith

/-! ## Forward-output service boundary -/

theorem transferOutput_eval (v p : Bool) (src zero one : Word) (a : Accumulator) :
    Eval transferOutput (3 * a.output.length + 3)
      (state v p src zero one a)
      (state false false (a.output.reverse ++ src) zero one { a with output := [] }) := by
  let d := state v p src zero one a
  let final := state false false (a.output.reverse ++ src) zero one { a with output := [] }
  have hregs : readRegs d.regs 0 1 none = final.regs := by
    funext i
    fin_cases i <;> simp [d, final, state, readRegs, SubexpHornerProgram.triple]
  have hstacks : StackRoutines.transferStacks (3 : Fin 8) 0 d.stacks = final.stacks := by
    funext i
    fin_cases i <;> simp [d, final, state, StackRoutines.transferStacks]
  have h := StackRoutines.transferProgram_trace (r := 3) (s := 8) 3 0 0 1
    (by decide) (by decide) d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  simp only [StackRoutines.transferResult] at hh
  rw [hregs, hstacks] at hh
  apply Eval.call
  simpa [transferOutput, StructuredProgram.State.withPC,
    d, final, state, Nat.add_assoc] using hh

@[simp] theorem operators_length (mul : Bool) (n : ℕ) :
    (operators mul n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [operators_succ, List.length_append, ih]; simp [operator]; omega

theorem flattenedCode_le_scanCost {α : Type*} (encode code : α → Word) (cost : α → ℕ)
    (xs : List α) (h : ∀ x ∈ xs, (code x).length ≤ cost x) :
    ((xs.map code).flatten).length ≤ scanCost encode cost xs := by
  induction xs with
  | nil => simp [scanCost]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, List.flatten_cons, List.length_append,
        scanCost, List.sum_cons] at *
      omega

end SubexponentialSAT.SubexpKernelControl

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical source construction for universal interpolation rows

The input holds raw coefficient payloads, node inverses, and negative nodes.
It does not contain polynomial instructions. Fixed nested scans emit the
Lagrange products and correction sum as postfix source in canonical list order.
The surrounding row-data producer supplies the selected mismatch positions;
its matrix, cache, and type-mask construction is tracked separately.
-/

namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

theorem literalPorts_injective : Function.Injective literalPorts := by decide

private theorem embed_literal (v p v' p' : Bool) (source zero one out : Word) (a : Accumulator) :
    embedState id literalPorts (state v p source zero one a)
      ⟨SubexpHornerProgram.triple v' p' true, SubexpHornerProgram.triple a.outer out []⟩ =
      state v' p' source zero one {a with output := out} := by
  apply embedState_eq_of_ports _ _ _ _ _ Function.injective_id literalPorts_injective
  · intro i; rfl
  · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h3 : i ≠ 3 := fun h => hi ⟨1, h.symm⟩
    fin_cases i <;> simp_all [state]

theorem emitX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval emitX (8 * a.outer.length + 9) (state v p source zero one a)
      (state false false source zero one (emit (pushWord a.outer) a)) := by
  have ht := eval_call_lifted SubexpHornerProgram.Literal.program id literalPorts
    (state v p source zero one a) Function.injective_id literalPorts_injective
    (a := ⟨SubexpHornerProgram.triple v p true,
      SubexpHornerProgram.triple a.outer a.output []⟩)
    (b := ⟨SubexpHornerProgram.triple false false true,
      SubexpHornerProgram.triple a.outer ((pushWord a.outer).reverse ++ a.output) []⟩)
    (SubexpHornerProgram.Literal.trace a.outer a.output v p true)
  simpa only [SubexpHornerProgram.Literal.cfg, StructuredProgram.State.withPC,
    embed_literal, emitX, emit, pushWord] using ht

/-- A real byte-level affine-factor construction from two scalar payloads. -/
theorem factorBody_eval (f : Factor Word) (source zero one : Word) (a : Accumulator) :
    Eval factorBody (factorCost a.outer f)
      (state false false (encodeFactor f ++ source) zero one a)
      (state false true source zero one (factorUpdate a.outer f a)) := by
  let a1 := emit (pushWord f.inverseDifference) a
  let a2 := emit (pushWord a.outer) a1
  let a3 := emit (pushWord f.negativeNode) a2
  let a4 := emit (operator false) a3
  let a5 := emit (operator true) a4
  have h1 := SubexpKernelControl.emitFramedLiteral_eval false false f.inverseDifference
    (Encoding.frame f.negativeNode ++ source) zero one a
  have h2 := emitX_eval false true (Encoding.frame f.negativeNode ++ source) zero one a1
  have h3 := SubexpKernelControl.emitFramedLiteral_eval false false f.negativeNode source zero one a2
  have h4 := SubexpKernelControl.emitOperator_eval false false true source zero one a3
  have h5 := SubexpKernelControl.emitOperator_eval true false true source zero one a4
  have h6 := SubexpKernelControl.countOne_eval 1 false true source zero one a5
  have ht := h1.seq (h2.seq (h3.seq (h4.seq (h5.seq h6))))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [factorBody, factorCost, factorUpdate, factorCode, encodeFactor,
    a1, a2, a3, a4, a5, SubexpKernelControl.emit_emit, emit, bump,
    counterPort, counterWord, setCounter, List.append_assoc]
  all_goals omega

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Fixed nested source emitter and its actual byte-level execution bound. -/
namespace SubexponentialSAT.Subexp.UniversalRowProgram

open BitProgram StructuredCalls
open SubexpKernelControl (Word Accumulator pushWord operator operators emit bump
  state counterWord setCounter counterPort popTag unframe emitFramedLiteral emitLiteral
  emitOperator countOne drain scan scanCost)

theorem productBody_eval (fs : List (Factor Word)) (source zero one x : Word)
    (a : Accumulator) (hx : a.outer = x) (hprod : a.groups = []) :
    Eval productBody (productCost one x fs)
      (state false false (Encoding.encodeList encodeFactor fs ++ source) zero one a)
      (state false false source zero one (emit (productCode one x fs) a)) := by
  let pre := (fs.map (factorCode x)).flatten
  let pending := List.replicate fs.length true
  have hs := SubexpKernelControl.scan_eval factorBody encodeFactor (factorCost x)
    (factorUpdate x) (fun a => a.outer = x) zero one false true
    (fun f rest a ha => by simpa only [ha] using factorBody_eval f rest zero one a)
    (fun f a ha => by simpa [factorUpdate, bump, setCounter, emit] using ha)
    fs false false source a hx
  have hs' : Eval (scan factorBody) (2 + scanCost encodeFactor (factorCost x) fs)
      (state false false (Encoding.encodeList encodeFactor fs ++ source) zero one a)
      (state false true source zero one (emit pre (setCounter 1 pending a))) := by
    simpa [factorUpdate, SubexpKernelControl.fold_bump_emit, pre, pending, counterWord, hprod] using hs
  have ho := SubexpKernelControl.emitLiteral_eval true false true source zero one
    (emit pre (setCounter 1 pending a))
  have hd := SubexpKernelControl.drain_eval 1 true pending false false source zero one
    (emit (pre ++ pushWord one) a)
  have hd' : Eval (drain 6 true) (4 * fs.length + 2)
      (state false false source zero one (emit (pushWord one) (emit pre (setCounter 1 pending a))))
      (state false false source zero one (emit (productCode one x fs) a)) := by
    have hclear := SubexpKernelControl.setCounter_same (1 : Fin 3) a
    have hword : counterWord (1 : Fin 3) a = [] := hprod
    rw [hword] at hclear
    simpa [counterPort, pending, productCode, pre, SubexpKernelControl.emit_emit,
      SubexpKernelControl.setCounter_emit, hclear, List.append_assoc] using hd
  have ht := hs'.seq (ho.seq hd')
  convert ht using 1 <;> simp [productBody, productCost] ; omega

theorem termBody_eval (t : Term Word) (source zero one x : Word) (a : Accumulator)
    (hx : a.outer = x) (hprod : a.groups = []) :
    Eval termBody (termCost one x t)
      (state false false (encodeTerm t ++ source) zero one a)
      (state false false source zero one (termUpdate one x t a)) := by
  let tail := Encoding.encodeList encodeFactor t.factors ++ source
  let a1 := emit (pushWord t.value) a
  let a2 := emit (pushWord t.inverseNode) a1
  let a3 := emit (pushWord x) a2
  let a4 := emit (operator true) a3
  let a5 := emit (productCode one x t.factors) a4
  let a6 := emit (operator true) a5
  let a7 := emit (operator true) a6
  have h1 := SubexpKernelControl.emitFramedLiteral_eval false false t.value
    (Encoding.frame t.inverseNode ++ tail) zero one a
  have h2 := SubexpKernelControl.emitFramedLiteral_eval false true t.inverseNode tail zero one a1
  have h3 := emitX_eval false true tail zero one a2
  have h4 := SubexpKernelControl.emitOperator_eval true false false tail zero one a3
  have h5 := productBody_eval t.factors source zero one x a4
    (by simpa [a4, a3, a2, a1, emit] using hx) (by simpa [a4, a3, a2, a1, emit] using hprod)
  have h6 := SubexpKernelControl.emitOperator_eval true false false source zero one a5
  have h7 := SubexpKernelControl.emitOperator_eval true false false source zero one a6
  have h8 := SubexpKernelControl.countOne_eval 2 false false source zero one a7
  have h3' : Eval emitX (8 * x.length + 9) (state false true tail zero one a2)
      (state false false tail zero one a3) := by
    simpa [a2, a1, a3, emit, hx] using h3
  have ht := h1.seq (h2.seq (h3'.seq (h4.seq (h5.seq (h6.seq (h7.seq h8))))))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [termBody, termCost, termUpdate, termCode, encodeTerm, tail,
    a1, a2, a3, a4, a5, a6, a7, SubexpKernelControl.emit_emit, bump,
    counterPort, List.append_assoc]
  all_goals omega

theorem rowBody_eval (r : Row Word) (v p : Bool) (source zero one x : Word)
    (a : Accumulator) (hx : a.outer = x) (hprod : a.groups = []) (hsum : a.terms = []) :
    Eval rowBody (rowCost zero one x r)
      (state v p (encodeRow r ++ source) zero one a)
      (state false false source zero one (emit (rowCode zero one x r) a)) := by
  let a0 := emit (pushWord r.delta) a
  let pre := (r.terms.map (termCode one x)).flatten
  let pending := List.replicate r.terms.length true
  have h0 := SubexpKernelControl.emitFramedLiteral_eval v p r.delta
    (Encoding.encodeList encodeTerm r.terms ++ source) zero one a
  have hs := SubexpKernelControl.scan_eval termBody encodeTerm (termCost one x)
    (termUpdate one x) (fun a => a.outer = x ∧ a.groups = []) zero one false false
    (fun t rest a ha => termBody_eval t rest zero one x a ha.1 ha.2)
    (fun t a ha => by simpa [termUpdate, bump, setCounter, emit] using ha)
    r.terms false true source a0 (by simpa [a0, emit] using And.intro hx hprod)
  have hs' : Eval (scan termBody) (2 + scanCost encodeTerm (termCost one x) r.terms)
      (state false true (Encoding.encodeList encodeTerm r.terms ++ source) zero one a0)
      (state false true source zero one (emit pre (setCounter 2 pending a0))) := by
    simp only [termUpdate] at hs
    rw [SubexpKernelControl.fold_bump_emit] at hs
    simpa [pre, pending, counterWord, a0, emit, hsum] using hs
  have hz := SubexpKernelControl.emitLiteral_eval false false true source zero one
    (emit pre (setCounter 2 pending a0))
  have hd := SubexpKernelControl.drain_eval 2 false pending false false source zero one
    (emit (pre ++ pushWord zero) a0)
  have hd' : Eval (drain 7 false) (5 * r.terms.length + 2)
      (state false false source zero one (emit (pushWord zero) (emit pre (setCounter 2 pending a0))))
      (state false false source zero one
        (emit (pre ++ pushWord zero ++ operators false r.terms.length) a0)) := by
    have hclear := SubexpKernelControl.setCounter_same (2 : Fin 3) a0
    have hword : counterWord (2 : Fin 3) a0 = [] := by simpa [a0, counterWord, emit] using hsum
    rw [hword] at hclear
    simpa [counterPort, pending, SubexpKernelControl.emit_emit,
      SubexpKernelControl.setCounter_emit, hclear, List.append_assoc] using hd
  have ha := SubexpKernelControl.emitOperator_eval false false false source zero one
    (emit (pre ++ pushWord zero ++ operators false r.terms.length) a0)
  have ht := h0.seq (hs'.seq (hz.seq (hd'.seq ha)))
  convert ht using 1
  all_goals try with_reducible_and_instances rfl
  all_goals simp [rowBody, rowCost, rowCode, encodeRow, pre, a0,
    SubexpKernelControl.emit_emit, List.append_assoc]
  all_goals omega


private theorem copyX_eval (which v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval (.call (StackRoutines.copyProgram (if which then 2 else 1) (5 : Fin 8) 4 (0 : Fin 3) 1))
      (7 * (if which then one else zero).length + 5)
      (state v p source zero one a)
      (state false false source zero one
        {a with outer := (if which then one else zero) ++ a.outer}) := by
  let d := state v p source zero one a
  have ht := ListRegisterProgram.copy_run (if which then (2 : Fin 8) else 1) 5 4 (0 : Fin 3) 1
    (by cases which <;> decide) (by cases which <;> decide) (by decide) (by decide)
    d.regs d.stacks (by rfl)
  have hf : (⟨readRegs d.regs 0 1 none,
      StackRoutines.copyStacks (if which then 2 else 1) 5 d.stacks⟩ : State 3 8) =
      state false false source zero one {a with outer := (if which then one else zero) ++ a.outer} := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [d, state, readRegs, SubexpHornerProgram.triple]
    · funext i; cases which <;> fin_cases i <;> simp [d, state, StackRoutines.copyStacks]
  have he := Eval.call _ (a := d)
    (b := (⟨readRegs d.regs 0 1 none,
      StackRoutines.copyStacks (if which then 2 else 1) 5 d.stacks⟩ : State 3 8)) ht
  change Eval _ _ d _ at he
  rw [hf] at he
  cases which <;> simpa [d, state] using he

theorem prepareX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) (hx : a.outer = []) :
    Eval prepareX (7 * (zero.length + one.length) + 10)
      (state v p source zero one a)
      (state false false source zero one {a with outer := zero ++ one}) := by
  have h1 := copyX_eval true v p source zero one a
  have h2 := copyX_eval false false false source zero one {a with outer := one ++ a.outer}
  have h := h1.seq h2
  convert h using 1 <;> simp [prepareX, hx] ; omega

theorem clearX_eval (v p : Bool) (source zero one : Word) (a : Accumulator) :
    Eval clearX (2 * a.outer.length + 3) (state v p source zero one a)
      (state false false source zero one {a with outer := []}) := by
  let d := state v p source zero one a
  have ht := ListRegisterProgram.clear_run (5 : Fin 8) (0 : Fin 3) 1 d.regs d.stacks
  have hf : (⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 5 d.stacks⟩ : State 3 8) =
      state false false source zero one {a with outer := []} := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [d, state, readRegs, SubexpHornerProgram.triple]
    · funext i; fin_cases i <;> simp [d, state, StackRoutines.clearStacks]
  have he := Eval.call _ (a := d)
    (b := (⟨readRegs d.regs 0 1 none, StackRoutines.clearStacks 5 d.stacks⟩ : State 3 8)) ht
  change Eval _ _ d _ at he
  rw [hf] at he
  simpa [clearX, d, state] using he

theorem command_eval (zero one : Word) (r : Row Word) :
    Eval command (commandCost zero one r)
      (SubexpKernelControl.serviceState (encodeRow r) zero one)
      (SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one) := by
  let empty := SubexpKernelControl.emptyAccumulator
  let prepared : Accumulator := {empty with outer := zero ++ one}
  let output := rowCode zero one (zero ++ one) r
  have hin : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) true).eval
      (SubexpKernelControl.serviceState (encodeRow r) zero one) =
      state false false (encodeRow r) zero one empty := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr,
        SubexpKernelControl.serviceState, state, SubexpHornerProgram.triple]
    · rfl
  have henter : Eval (.base (.atom (.set 2 true))) 1
      (SubexpKernelControl.serviceState (encodeRow r) zero one)
      (state false false (encodeRow r) zero one empty) := by
    rw [← hin]
    exact .base (.atom _ _)
  have hp := prepareX_eval false false (encodeRow r) zero one empty rfl
  have hr := rowBody_eval r false false [] zero one (zero ++ one) prepared rfl rfl rfl
  have hc := clearX_eval false false [] zero one (emit output prepared)
  have ht := SubexpKernelControl.transferOutput_eval false false [] zero one (emit output empty)
  have heq : (StructuredProgram.Atom.set (s := 8) (2 : Fin 3) false).eval
      (state false false output zero one empty) =
      SubexpKernelControl.serviceState output zero one := by
    apply congrArg₂ StructuredProgram.State.mk
    · funext i; fin_cases i <;> simp [ StructuredProgram.Atom.instr, execInstr, state, SubexpHornerProgram.triple]
    · rfl
  have hexit : Eval (.base (.atom (.set 2 false))) 1 (state false false output zero one empty)
      (SubexpKernelControl.serviceState output zero one) := by
    rw [← heq]
    exact .base (.atom _ _)
  have hr' : Eval rowBody (rowCost zero one (zero ++ one) r)
      (state false false (encodeRow r) zero one prepared)
      (state false false [] zero one (emit output prepared)) := by simpa [output] using hr
  have hc' : Eval clearX (2 * (zero.length + one.length) + 3)
      (state false false [] zero one (emit output prepared))
      (state false false [] zero one (emit output empty)) := by
    simpa [prepared, empty, emit, SubexpKernelControl.emptyAccumulator] using hc
  have ht' : Eval SubexpKernelControl.transferOutput (3 * output.length + 3)
      (state false false [] zero one (emit output empty))
      (state false false output zero one empty) := by
    simpa [empty, emit, SubexpKernelControl.emptyAccumulator] using ht
  have h := henter.seq (hp.seq (hr'.seq (hc'.seq (ht'.seq hexit))))
  convert h using 1 ; simp [ commandCost, output] ; omega

theorem program_trace (zero one : Word) (r : Row Word) :
    Trace program (commandCost zero one r + 1)
      ((SubexpKernelControl.serviceState (encodeRow r) zero one).withPC (some program.entry))
      ((SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one).withPC none) :=
  compiled_halt_trace (command_eval zero one r) 0 0


theorem factorCost_le_input (x : Word) (f : Factor Word) :
    factorCost x f ≤ 7 * (encodeFactor f).length + (8 * x.length + 29) := by
  simp [factorCost, encodeFactor]
  omega

theorem productCost_le_input (one x : Word) (fs : List (Factor Word)) :
    productCost one x fs ≤ (8 * x.length + 60) * (Encoding.encodeList encodeFactor fs).length +
      (8 * one.length + 13) := by
  have hs := SubexpKernelControl.scanCost_le_input encodeFactor (factorCost x) fs
    7 (8 * x.length + 29) (fun f _ => factorCost_le_input x f)
  have hl := Encoding.length_encodeList_lower encodeFactor fs
  unfold productCost
  nlinarith

theorem termCost_le_input (one x : Word) (t : Term Word) :
    termCost one x t ≤ (16 * x.length + 16 * one.length + 200) * (encodeTerm t).length := by
  have hp := productCost_le_input one x t.factors
  have hl := Encoding.length_encodeList_lower encodeFactor t.factors
  unfold termCost encodeTerm
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * t.value.length), Nat.zero_le (x.length * t.inverseNode.length),
    Nat.zero_le (one.length * t.value.length), Nat.zero_le (one.length * t.inverseNode.length),
    Nat.zero_le (one.length * (Encoding.encodeList encodeFactor t.factors).length)]

theorem rowCost_le_input (zero one x : Word) (r : Row Word) :
    rowCost zero one x r ≤
      (16 * x.length + 16 * one.length + 16 * zero.length + 300) * (encodeRow r).length := by
  have hs := SubexpKernelControl.scanCost_le_input encodeTerm (termCost one x) r.terms
    (16 * x.length + 16 * one.length + 200) 0
    (fun t _ => by simpa using termCost_le_input one x t)
  have hl := Encoding.length_encodeList_lower encodeTerm r.terms
  unfold rowCost encodeRow
  simp only [List.length_append, Encoding.length_frame]
  nlinarith [Nat.zero_le (x.length * r.delta.length), Nat.zero_le (one.length * r.delta.length),
    Nat.zero_le (zero.length * r.delta.length),
    Nat.zero_le (zero.length * (Encoding.encodeList encodeTerm r.terms).length)]

theorem factorCode_length_le (x : Word) (f : Factor Word) :
    (factorCode x f).length ≤ factorCost x f := by
  simp [factorCode, factorCost, operator, SubexpKernelControl.pushWord_length]
  omega

theorem productCode_length_le (one x : Word) (fs : List (Factor Word)) :
    (productCode one x fs).length ≤ productCost one x fs := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeFactor (factorCode x)
    (factorCost x) fs (fun f _ => factorCode_length_le x f)
  simp only [productCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, productCost]
  omega

theorem termCode_length_le (one x : Word) (t : Term Word) :
    (termCode one x t).length ≤ termCost one x t := by
  have hp := productCode_length_le one x t.factors
  simp only [termCode, List.length_append, SubexpKernelControl.pushWord_length,
    operator, List.length_cons, List.length_nil, termCost]
  omega

theorem rowCode_length_le (zero one x : Word) (r : Row Word) :
    (rowCode zero one x r).length ≤ rowCost zero one x r := by
  have h := SubexpKernelControl.flattenedCode_le_scanCost encodeTerm (termCode one x)
    (termCost one x) r.terms (fun t _ => termCode_length_le one x t)
  simp only [rowCode, List.length_append, SubexpKernelControl.pushWord_length,
    SubexpKernelControl.operators_length, operator, List.length_cons, List.length_nil, rowCost]
  omega

theorem rowCost_quadratic (zero one : Word) (r : Row Word) :
    rowCost zero one (zero ++ one) r ≤ 300 * inputSize zero one r ^ 2 := by
  have h := rowCost_le_input zero one (zero ++ one) r
  simp only [List.length_append] at h
  have hc : 16 * (zero.length + one.length) + 16 * one.length + 16 * zero.length + 300 ≤
      300 * inputSize zero one r := by unfold inputSize; omega
  have hl : (encodeRow r).length ≤ inputSize zero one r := by unfold inputSize; omega
  have hm := Nat.mul_le_mul hc hl
  nlinarith

theorem program_runsIn (zero one : Word) (r : Row Word) :
    RunsIn program (2048 * inputSize zero one r ^ 2)
      ((SubexpKernelControl.serviceState (encodeRow r) zero one).withPC (some program.entry))
      ((SubexpKernelControl.serviceState (rowCode zero one (zero ++ one) r) zero one).withPC none) := by
  refine ⟨_, ?_, program_trace zero one r⟩
  have hr := rowCost_quadratic zero one r
  have hc := rowCode_length_le zero one (zero ++ one) r
  have hn : 1 ≤ inputSize zero one r := by unfold inputSize; omega
  have hl : zero.length + one.length ≤ inputSize zero one r := by unfold inputSize; omega
  have hs : inputSize zero one r ≤ inputSize zero one r ^ 2 := by nlinarith
  unfold commandCost
  nlinarith

end SubexponentialSAT.Subexp.UniversalRowProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_Subexp_UniversalRowEmitCall
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A framed call to the actual row source emitter inside the row workspace. -/

namespace SubexponentialSAT.Subexp.UniversalRowEmitCall

open BitProgram StructuredCalls
open UniversalRowProgram (Row)
open SubexpKernelControl (Word)

theorem regs_injective : Function.Injective regs := Fin.castAdd_injective 3 5
theorem stackMap_injective : Function.Injective stackMap := by decide

theorem reset_eval (a : Data) : Eval reset 3 a (resetState a) := by
  exact .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

theorem command_eval_oai (a : Data) (zero one : Word) (r : Row Word)
    (hrow : a.stacks 31 = UniversalRowProgram.encodeRow r)
    (hzero : a.stacks 3 = zero) (hone : a.stacks 10 = one)
    (h1 : a.stacks 1 = []) (h2 : a.stacks 2 = []) (h4 : a.stacks 4 = [])
    (h5 : a.stacks 5 = []) (h6 : a.stacks 6 = []) :
    ∃ n ≤ 2048 * UniversalRowProgram.inputSize zero one r ^ 2 + 3,
      Eval command n a (result a (UniversalRowProgram.rowCode zero one (zero ++ one) r)) := by
  let prepared := resetState a
  let first := SubexpKernelControl.serviceState (UniversalRowProgram.encodeRow r) zero one
  let last := SubexpKernelControl.serviceState (UniversalRowProgram.rowCode zero one (zero ++ one) r)
    zero one
  have hin : embedState regs stackMap prepared first = prepared := by
    apply embedState_eq_of_ports _ _ _ _ _ regs_injective stackMap_injective
    · intro j
      fin_cases j <;> simp [regs, prepared, resetState, first, SubexpKernelControl.serviceState]
    · intros; rfl
    · intro j
      fin_cases j <;> simp [stackMap, prepared, resetState, first,
        SubexpKernelControl.serviceState, SubexpKernelControl.state,
        SubexpKernelControl.emptyAccumulator, hrow, hzero, hone, h1, h2, h4, h5, h6]
    · intros; rfl
  have hout : embedState regs stackMap prepared last =
      result a (UniversalRowProgram.rowCode zero one (zero ++ one) r) := by
    apply embedState_eq_of_ports _ _ _ _ _ regs_injective stackMap_injective
    · intro j
      fin_cases j <;> simp [regs, result, resetState, last, SubexpKernelControl.serviceState]
    · intro j hj
      rfl
    · intro j
      fin_cases j <;> simp [stackMap, result, last, SubexpKernelControl.serviceState,
        SubexpKernelControl.state, SubexpKernelControl.emptyAccumulator,
        hzero, hone, h1, h2, h4, h5, h6]
    · intro j hj
      have h31 : j ≠ 31 := fun h => hj ⟨0, h.symm⟩
      simp [result, prepared, resetState, h31]
  obtain ⟨n, hn, ht⟩ := UniversalRowProgram.program_runsIn zero one r
  have he := eval_call_lifted UniversalRowProgram.program regs stackMap prepared
    regs_injective stackMap_injective (a := first) (b := last) ht
  have hem : Eval emit n prepared
      (result a (UniversalRowProgram.rowCode zero one (zero ++ one) r)) := by
    simpa only [emit, hin, hout] using he
  exact ⟨3 + n, by omega, (reset_eval a).seq hem⟩

end SubexponentialSAT.Subexp.UniversalRowEmitCall

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.Subexp.UniversalRowEmitCall.command_eval_oai
