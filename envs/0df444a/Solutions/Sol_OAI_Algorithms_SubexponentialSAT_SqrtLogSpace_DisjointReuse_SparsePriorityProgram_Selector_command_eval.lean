-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:24:56.004592+00:00
-- url     : https://prove2.me/submissions/c188db37-5202-4fbc-9b1e-53be34d0a4da

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S136
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_checkCandidate_eval
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram_Selector_familyInit_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ArithmeticExpressionSupport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

namespace SubexponentialSAT.ArithmeticExpressionSupport

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem bits_value (n : ℕ) : BinaryArithmetic.toNat n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp []
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn]
      cases b <;> simp [BinaryArithmetic.toNat, ih, Nat.bit, Nat.add_comm]

end SubexponentialSAT.ArithmeticExpressionSupport

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_CoreMaskProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Applying a runtime mask to an encoded clause

The mask and clause occupy separate Boolean stacks.  Selection consumes one
mask bit per literal, treating a missing bit as false and leaving excess mask
bits unread.  Payloads are copied as framed bit strings without interpreting
their contents.
-/

namespace SubexponentialSAT.CoreMaskProgram

open SubexponentialSAT.BitProgram
open SubexponentialSAT.StructuredProgram

theorem frame_eq_prefix (bits : List Bool) :
    Encoding.frame bits = framePrefix bits ++ [false] := by
  induction bits with
  | nil => rfl
  | cons b bs ih => simp [Encoding.frame_cons, framePrefix, ih]

theorem encode_eq_prefix (records : List (List Bool)) :
    Encoding.encodeList id records = recordPrefix records ++ [false] := by
  induction records with
  | nil => rfl
  | cons item rest ih => simp [Encoding.encodeList, recordPrefix, ih, List.append_assoc]

theorem selected_encoded_length_le (mask : List Bool) (records : List (List Bool)) :
    (Encoding.encodeList id (select mask records)).length ≤
      (Encoding.encodeList id records).length := by
  induction records generalizing mask with
  | nil => simp [select]
  | cons item rest ih =>
      simp only [select]
      split
      · simpa only [Encoding.length_encodeList_cons, id_eq] using
          Nat.add_le_add_left (ih mask.tail) (2 * item.length + 2)
      · exact (ih mask.tail).trans (by rw [Encoding.length_encodeList_cons]; omega)

theorem emitCost_le (keep : Bool) : emitCost keep ≤ 2 := by
  cases keep <;> decide

theorem popTag_eval (t p k d b : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (b :: source) mask accum output)
      (state b true k d source mask accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (0 : Fin 4) 0 1)
    (state t p k d (b :: source) mask accum output) using 1
  all_goals try with_reducible_and_instances rfl
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem popBit_eval (t p k d b : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popBit 1
      (state t p k d (b :: source) mask accum output)
      (state t true k b source mask accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (0 : Fin 4) 3 1)
    (state t p k d (b :: source) mask accum output) using 1
  all_goals try with_reducible_and_instances rfl
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem popMask_eval (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval popMask 1 (state t p k d source mask accum output)
      (state t (!mask.isEmpty) (mask.headD false) d source mask.tail accum output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.pop (1 : Fin 4) 2 1)
    (state t p k d source mask accum output) using 1
  all_goals try with_reducible_and_instances rfl
  cases mask <;>
    simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state, readRegs]

theorem push_eval (r : Fin 4) (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval (atom (.push 2 r)) 1
      (state t p k d source mask accum output)
      (state t p k d source mask (regs t p k d r :: accum) output) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.push (2 : Fin 4) r)
    (state t p k d source mask accum output) using 1
  all_goals try with_reducible_and_instances rfl
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state]

theorem emit_eval (r : Fin 4) (t p k d : Bool) (source mask accum output : List Bool) :
    StructuredCalls.Eval (emit r) (emitCost k)
      (state t p k d source mask accum output)
      (state t p k d source mask
        (if k then regs t p k d r :: accum else accum) output) := by
  cases k with
  | false =>
      exact StructuredCalls.Eval.ite_false rfl (.base (.skip _))
  | true =>
      exact StructuredCalls.Eval.ite_true rfl (push_eval r t p true d source mask accum output)

theorem pop_frame_eval (bits tail mask accum output : List Bool) (t p k d : Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (Encoding.frame bits ++ tail) mask accum output)
      (frameReady bits tail mask accum output k d) := by
  cases bits with
  | nil => exact popTag_eval t p k d false tail mask accum output
  | cons b bs => exact popTag_eval t p k d true _ mask accum output

theorem frameLoop_eval (bits tail mask accum output : List Bool) (keep bit : Bool) :
    ∃ steps ≤ 7 * bits.length + 1, ∃ last : Bool,
      StructuredCalls.Eval frameLoop steps
        (frameReady bits tail mask accum output keep bit)
        (state false true keep last tail mask
          (if keep then (framePrefix bits).reverse ++ accum else accum) output) := by
  induction bits generalizing accum bit with
  | nil =>
      refine ⟨1, by simp, bit, ?_⟩
      have h : StructuredCalls.Eval frameLoop 1
          (state false true keep bit tail mask accum output)
          (state false true keep bit tail mask accum output) :=
        StructuredCalls.Eval.while_false rfl
      simpa [frameReady, framePrefix] using h
  | cons b bs ih =>
      let a₁ := if keep then true :: accum else accum
      let a₂ := if keep then b :: a₁ else a₁
      have h₁ := emit_eval 0 true true keep bit
        (b :: (Encoding.frame bs ++ tail)) mask accum output
      have h₂ := popBit_eval true true keep bit b
        (Encoding.frame bs ++ tail) mask a₁ output
      have h₃ := emit_eval 3 true true keep b
        (Encoding.frame bs ++ tail) mask a₁ output
      have h₄ := pop_frame_eval bs tail mask a₂ output true true keep b
      have hb : StructuredCalls.Eval frameBody
          (emitCost keep + (1 + (emitCost keep + 1)))
          (frameReady (b :: bs) tail mask accum output keep bit)
          (frameReady bs tail mask a₂ output keep b) :=
        .seq h₁ (.seq h₂ (.seq h₃ h₄))
      obtain ⟨n, hn, last, hi⟩ := ih a₂ b
      have hrun := StructuredCalls.Eval.while_true
        (test := (0 : Fin 4)) (body := frameBody) rfl hb hi
      refine ⟨(emitCost keep + (1 + (emitCost keep + 1))) + n + 1, ?_, last, ?_⟩
      · have he := emitCost_le keep
        simp only [List.length_cons]
        omega
      · convert hrun using 1
        · rfl
        · cases keep <;>
            simp [framePrefix, a₁, a₂, List.reverse_cons, List.append_assoc]

theorem scanFrame_eval (bits tail mask accum output : List Bool) (t p keep bit : Bool) :
    ∃ steps ≤ 7 * bits.length + 4, ∃ last : Bool,
      StructuredCalls.Eval scanFrame steps
        (state t p keep bit (Encoding.frame bits ++ tail) mask accum output)
        (state false true keep last tail mask
          (if keep then (Encoding.frame bits).reverse ++ accum else accum) output) := by
  obtain ⟨n, hn, last, hi⟩ := frameLoop_eval bits tail mask accum output keep bit
  have hp := pop_frame_eval bits tail mask accum output t p keep bit
  have he := emit_eval 0 false true keep last tail mask
    (if keep then (framePrefix bits).reverse ++ accum else accum) output
  have hrun := StructuredCalls.Eval.seq hp (StructuredCalls.Eval.seq hi he)
  refine ⟨1 + (n + emitCost keep), ?_, last, ?_⟩
  · have hc := emitCost_le keep
    omega
  · convert hrun using 1
    · rfl
    · cases keep <;>
        simp [frame_eq_prefix, List.reverse_append, regs]

theorem pop_record_eval (records : List (List Bool)) (suffix mask accum output : List Bool)
    (t p k d : Bool) :
    StructuredCalls.Eval popTag 1
      (state t p k d (Encoding.encodeList id records ++ suffix) mask accum output)
      (recordReady records suffix mask accum output k d) := by
  cases records with
  | nil => exact popTag_eval t p k d false suffix mask accum output
  | cons item rest =>
      simpa only [Encoding.encodeList, id_eq, List.cons_append, List.append_assoc,
        recordReady] using
        popTag_eval t p k d true
          (Encoding.frame item ++ (Encoding.encodeList id rest ++ suffix)) mask accum output

theorem recordLoop_eval (records : List (List Bool)) (suffix mask accum output : List Bool)
    (keep bit : Bool) :
    ∃ steps ≤ recordCost records, ∃ finalKeep finalBit : Bool,
      StructuredCalls.Eval recordLoop steps
        (recordReady records suffix mask accum output keep bit)
        (state false true finalKeep finalBit suffix (mask.drop records.length)
          ((recordPrefix (select mask records)).reverse ++ accum) output) := by
  induction records generalizing mask accum keep bit with
  | nil =>
      refine ⟨1, by simp [recordCost], keep, bit, ?_⟩
      have h : StructuredCalls.Eval recordLoop 1
          (state false true keep bit suffix mask accum output)
          (state false true keep bit suffix mask accum output) :=
        StructuredCalls.Eval.while_false rfl
      simpa [recordReady, recordPrefix, select] using h
  | cons item rest ih =>
      let chosen := mask.headD false
      let tail := Encoding.encodeList id rest ++ suffix
      let a₁ := if chosen then true :: accum else accum
      let a₂ := if chosen then (Encoding.frame item).reverse ++ a₁ else a₁
      have hm := popMask_eval true true keep bit
        (Encoding.frame item ++ tail) mask accum output
      have he := emit_eval 0 true (!mask.isEmpty) chosen bit
        (Encoding.frame item ++ tail) mask.tail accum output
      obtain ⟨f, hf, middleBit, hframe⟩ :=
        scanFrame_eval item tail mask.tail a₁ output true (!mask.isEmpty) chosen bit
      have hp := pop_record_eval rest suffix mask.tail a₂ output false true chosen middleBit
      have hb : StructuredCalls.Eval recordBody (1 + (emitCost chosen + (f + 1)))
          (recordReady (item :: rest) suffix mask accum output keep bit)
          (recordReady rest suffix mask.tail a₂ output chosen middleBit) :=
        .seq hm (.seq he (.seq hframe hp))
      obtain ⟨n, hn, finalKeep, finalBit, hi⟩ := ih mask.tail a₂ chosen middleBit
      have hrun := StructuredCalls.Eval.while_true
        (test := (0 : Fin 4)) (body := recordBody) rfl hb hi
      refine ⟨(1 + (emitCost chosen + (f + 1))) + n + 1, ?_,
        finalKeep, finalBit, ?_⟩
      · have hc := emitCost_le chosen
        simp only [recordCost, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · convert hrun using 1
        · rfl
        · cases mask with
          | nil =>
              simp [select, chosen, a₁, a₂
                 ]
          | cons b mask =>
              cases b <;> simp [select, chosen, a₁, a₂, recordPrefix,
                List.reverse_cons, List.reverse_append, List.append_assoc]

theorem scanRecords_eval (records : List (List Bool))
    (suffix mask accum output : List Bool) (t p keep bit : Bool) :
    ∃ steps ≤ recordCost records + 1, ∃ finalKeep finalBit : Bool,
      StructuredCalls.Eval scanRecords steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask accum output)
        (state false true finalKeep finalBit suffix (mask.drop records.length)
          ((recordPrefix (select mask records)).reverse ++ accum) output) := by
  obtain ⟨n, hn, finalKeep, finalBit, hi⟩ :=
    recordLoop_eval records suffix mask accum output keep bit
  refine ⟨1 + n, by omega, finalKeep, finalBit, ?_⟩
  exact .seq (pop_record_eval records suffix mask accum output t p keep bit) hi

theorem reverseAccum_eval (keep bit : Bool) (suffix mask word : List Bool) :
    StructuredCalls.Eval reverseAccum (3 * word.length + 3)
      (state false true keep bit suffix mask word [])
      (state false false keep false suffix mask [] word.reverse) := by
  apply StructuredCalls.Eval.call
  have h := StackRoutines.transferProgram_trace (2 : Fin 4) 3 (3 : Fin 4) 1
    (by decide) (by decide) (regs false true keep bit) (stackData suffix mask word [])
  have hh := StackRoutines.halt_after_trace _ h 3 rfl rfl
  convert hh using 1 <;>
    simp [state, State.withPC,
      StackRoutines.transferResult, StackRoutines.transferStacks, readRegs]

theorem resetKeep_eval (keep : Bool) (suffix mask word : List Bool) :
    StructuredCalls.Eval resetKeep 1
      (state false false keep false suffix mask [] word)
      (state false false false false suffix mask [] word) := by
  apply StructuredCalls.Eval.base
  convert StructuredProgram.Eval.atom (.set (2 : Fin 4) false)
    (state false false keep false suffix mask [] word) using 1
  all_goals try with_reducible_and_instances rfl
  simp [Atom.eval, Atom.instr, State.ofCfg, execInstr, state]

theorem command_eval (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    ∃ steps, steps + 1 ≤ runtimeBound records ∧
      StructuredCalls.Eval command steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
        (state false false false false suffix (mask.drop records.length) []
          (Encoding.encodeList id (select mask records))) := by
  obtain ⟨n, hn, finalKeep, finalBit, hs⟩ :=
    scanRecords_eval records suffix mask [] [] t p keep bit
  let selected := Encoding.encodeList id (select mask records)
  have hword : false :: (recordPrefix (select mask records)).reverse = selected.reverse := by
    simp [selected, encode_eq_prefix, List.reverse_append]
  have hp := push_eval 0 false true finalKeep finalBit suffix (mask.drop records.length)
    (recordPrefix (select mask records)).reverse []
  have hr := reverseAccum_eval finalKeep finalBit suffix (mask.drop records.length) selected.reverse
  have hc := resetKeep_eval finalKeep suffix (mask.drop records.length) selected
  have hs' : StructuredCalls.Eval scanRecords n
      (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
      (state false true finalKeep finalBit suffix (mask.drop records.length)
        (recordPrefix (select mask records)).reverse []) := by simpa using hs
  have hp' : StructuredCalls.Eval (atom (.push 2 0)) 1
      (state false true finalKeep finalBit suffix (mask.drop records.length)
        (recordPrefix (select mask records)).reverse [])
      (state false true finalKeep finalBit suffix (mask.drop records.length) selected.reverse []) := by
    simpa [regs, hword] using hp
  have hr' : StructuredCalls.Eval reverseAccum (3 * selected.length + 3)
      (state false true finalKeep finalBit suffix (mask.drop records.length) selected.reverse [])
      (state false false finalKeep false suffix (mask.drop records.length) [] selected) := by
    simpa using hr
  refine ⟨n + (1 + ((3 * selected.length + 3) + 1)), ?_,
    .seq hs' (.seq hp' (.seq hr' hc))⟩
  have he := ProgramEncoding.encodeRecords_length records
  have hselect := selected_encoded_length_le mask records
  change (Encoding.encodeList id records).length =
    2 * (records.map List.length).sum + 2 * records.length + 1 at he
  dsimp [recordCost] at hn
  dsimp [runtimeBound, selected]
  omega

theorem run_correct (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    BitProgram.RunsIn program (runtimeBound records)
      ((state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] []).withPC
        (some program.entry))
      ((state false false false false suffix (mask.drop records.length) []
        (Encoding.encodeList id (select mask records))).withPC none) := by
  obtain ⟨steps, hsteps, hrun⟩ := command_eval records suffix mask t p keep bit
  exact ⟨steps + 1, hsteps, StructuredCalls.compiled_halt_trace hrun 0 3⟩

theorem call_eval (records : List (List Bool)) (suffix mask : List Bool)
    (t p keep bit : Bool) :
    ∃ steps ≤ runtimeBound records,
      StructuredCalls.Eval (.call program) steps
        (state t p keep bit (Encoding.encodeList id records ++ suffix) mask [] [])
        (state false false false false suffix (mask.drop records.length) []
          (Encoding.encodeList id (select mask records))) := by
  obtain ⟨steps, hsteps, htrace⟩ := run_correct records suffix mask t p keep bit
  exact ⟨steps, hsteps, .call program htrace⟩

end SubexponentialSAT.CoreMaskProgram

end OAI.Algorithms
end

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

theorem nat_pop (b v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 0) v p (b :: input) output) =
      some (cfg (some 1) b true input output) := by
  simp [step, cfg, execInstr, readRegs]

theorem nat_present (v : Bool) (input output : List Bool) :
    step natProgram (cfg (some 1) v true input output) =
      some (cfg (some 2) v true input output) := by
  simp [step, cfg, execInstr]

theorem nat_true (input output : List Bool) :
    step natProgram (cfg (some 2) true true input output) =
      some (cfg (some 3) true true input output) := by
  simp [step, cfg, execInstr]

theorem nat_push (input output : List Bool) :
    step natProgram (cfg (some 3) true true input output) =
      some (cfg (some 0) true true input (true :: output)) := by
  simp [step, cfg, execInstr]

theorem nat_false (input output : List Bool) :
    step natProgram (cfg (some 2) false true input output) =
      some (cfg (some 4) false true input output) := by
  simp [step, cfg, execInstr]

theorem nat_halt (v p : Bool) (input output : List Bool) :
    step natProgram (cfg (some 4) v p input output) =
      some (cfg none v p input output) := by
  simp [step, cfg, execInstr]

theorem nat_cycle (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (true :: input) output)
      (cfg (some 0) true true input (true :: output)) :=
  .cons (nat_pop true v p input output)
    (.cons (nat_present true input output)
      (.cons (nat_true input output) (.cons (nat_push input output) (.refl _))))

theorem nat_finish (v p : Bool) (input output : List Bool) :
    Trace natProgram 4 (cfg (some 0) v p (false :: input) output)
      (cfg none false true input output) :=
  .cons (nat_pop false v p input output)
    (.cons (nat_present false input output)
      (.cons (nat_false input output) (.cons (nat_halt false true input output) (.refl _))))

/-- The count is data on stack 1, rather than an input-dependent control state. -/
theorem nat_trace (n : ℕ) (rest output : List Bool) (v p : Bool) :
    Trace natProgram (4 * n + 4)
      (cfg (some 0) v p (Encoding.encodeNat n ++ rest) output)
      (cfg none false true rest (List.replicate n true ++ output)) := by
  induction n generalizing output v p with
  | zero => simpa [Encoding.encodeNat] using nat_finish v p rest output
  | succ n ih =>
      have h := (nat_cycle v p (Encoding.encodeNat n ++ rest) output).trans
        (ih (true :: output) true true)
      have ht : 4 + (4 * n + 4) = 4 * (n + 1) + 4 := by omega
      have hin : Encoding.encodeNat (n + 1) ++ rest =
          true :: (Encoding.encodeNat n ++ rest) := by
        simp [Encoding.encodeNat, List.replicate_succ]
      simpa only [ht, hin, List.replicate_succ', List.append_assoc,
        List.singleton_append] using h

/-! ## In-place removal of one escape frame -/

/-! The compiler turns the preceding actual instruction traces into actual
primitive tape executions. Each overhead below belongs to one fixed program. -/

end SubexponentialSAT.ParserProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_FrontendProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual initialization of the canonical SAT input

The nineteen-label program splits the variable-count header and counts its
unary marks into a binary stack word. The untouched encoded CNF body remains
on stack 0. All growing values live on Boolean stacks, not in finite control.
-/

namespace SubexponentialSAT.FrontendProgram

open SubexponentialSAT.BitProgram

theorem extend_parser_regs (b p : Bool) :
    Function.extend (Fin.castSucc : Fin 2 → Fin 3) (ParserProgram.pair b p)
      (CounterPrograms.counterRegs false false false) = CounterPrograms.counterRegs b p false := by
  funext i
  fin_cases i
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 0
  · exact (Fin.castSucc_injective 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castSucc = (2 : Fin 3) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_parser_stacks (body unary : List Bool) :
    Function.extend (Fin.castAdd 2 : Fin 2 → Fin 4) (ParserProgram.pair body unary)
      (storage [] [] [] []) = storage body unary [] [] := by
  funext i
  fin_cases i
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 0
  · exact (Fin.castAdd_injective 2 2).extend_apply _ _ 1
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (2 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 2 at hv
      omega
    exact Function.extend_apply' _ _ _ hn
  · have hn : ¬ ∃ j : Fin 2, j.castAdd 2 = (3 : Fin 4) := by
      rintro ⟨j, hj⟩
      have hv := congrArg Fin.val hj
      have hl := j.isLt
      change j.val = 3 at hv
      omega
    exact Function.extend_apply' _ _ _ hn

theorem extend_counter_stacks (body unary binary scratch : List Bool) :
    Function.extend (Fin.succ : Fin 3 → Fin 4)
      (CounterPrograms.lengthStacks unary binary scratch) (storage body [] [] []) =
      storage body unary binary scratch := by
  funext i
  fin_cases i
  · have hn : ¬ ∃ j : Fin 3, j.succ = (0 : Fin 4) := by simp
    exact Function.extend_apply' _ _ _ hn
  · exact (Fin.succ_injective 3).extend_apply _ _ 0
  · exact (Fin.succ_injective 3).extend_apply _ _ 1
  · exact (Fin.succ_injective 3).extend_apply _ _ 2

@[simp] theorem embed_parser (pc : Option (Fin 5)) (b p : Bool) (body unary : List Bool) :
    ProgramLinking.embedCfg Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5)
      emptyFrame (ParserProgram.cfg pc b p body unary) =
      cfg (ProgramLinking.relocatePc (Fin.castAdd 14) (some 5) pc) b p body unary [] [] := by
  simp [ProgramLinking.embedCfg, emptyFrame, cfg, ParserProgram.cfg,
    extend_parser_regs, extend_parser_stacks]

@[simp] theorem embed_counter (pc : Option (Fin 14)) (b p : Bool)
    (body unary binary scratch : List Bool) :
    ProgramLinking.embedCfg id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
      (⟨pc, CounterPrograms.counterRegs b p false,
        CounterPrograms.lengthStacks unary binary scratch⟩ : Cfg 3 3 14) =
      cfg (ProgramLinking.relocatePc (Fin.natAdd 5) none pc) b p body unary binary scratch := by
  simp [ProgramLinking.embedCfg, bodyFrame, cfg, extend_counter_stacks]

theorem counter_terminal_eq (output : List Bool) :
    terminal CounterPrograms.lengthProgram output =
      (⟨none, CounterPrograms.counterRegs false false false,
        CounterPrograms.lengthStacks [] output []⟩ : Cfg 3 3 14) := by
  simp [terminal ]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [CounterPrograms.lengthStacks]

theorem initialize_initial (input : List Bool) :
    initial initializeProgram input = cfg (some 0) false false input [] [] [] := by
  simp [initial, cfg]
  constructor
  · funext i
    simp [CounterPrograms.counterRegs]
  · funext i
    fin_cases i <;> simp [storage]

theorem header_trace (n : ℕ) (body : List Bool) :
    Trace initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) := by
  have h := ProgramLinking.relocate_trace ParserProgram.natProgram initializeProgram
    Fin.castSucc (Fin.castAdd 2) (Fin.castAdd 14) (some 5) emptyFrame
    (Fin.castSucc_injective 2) (Fin.castAdd_injective 2 2)
    (ProgramLinking.linkInto_leftCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ)
    (ParserProgram.nat_trace n body [] false false)
  simpa [embed_parser, ProgramLinking.relocatePc, initialize_initial] using h

theorem initializeBound_eq (n : ℕ) : initializeBound n = 8 * n ^ 2 + 14 * n + 7 := by
  unfold initializeBound
  ring

/-- Actual raw-input initialization. The formula body is preserved on stack 0,
the binary count is on stack 2, and both work stacks are empty. -/
theorem initialize_raw (n : ℕ) (body : List Bool) :
    ∃ binary : List Bool, CounterPrograms.value binary = n ∧ binary.length ≤ n ∧
      RunsIn initializeProgram (initializeBound n)
        (initial initializeProgram (Encoding.encodeNat n ++ body))
        (cfg none false false body [] binary []) := by
  obtain ⟨binary, hv, hlen, hc⟩ :=
    CounterPrograms.length_correct_from false true (List.replicate n true)
  simp only [List.length_replicate] at hv hlen hc
  have hrel := ProgramLinking.relocate_runsIn CounterPrograms.lengthProgram initializeProgram
    id Fin.succ (Fin.natAdd 5) none (bodyFrame body)
    Function.injective_id (Fin.succ_injective 3)
    (ProgramLinking.linkInto_rightCode ParserProgram.natProgram CounterPrograms.lengthProgram
      Fin.castSucc (Fin.castAdd 2) id Fin.succ) hc
  have hcounter : RunsIn initializeProgram (n * (8 * n + 10) + 3)
      (cfg (some 5) false true body (List.replicate n true) [] [])
      (cfg none false false body [] binary []) := by
    simpa [CounterPrograms.lengthCfg, counter_terminal_eq, embed_counter,
      ProgramLinking.relocatePc] using hrel
  have hheader : RunsIn initializeProgram (4 * n + 4)
      (initial initializeProgram (Encoding.encodeNat n ++ body))
      (cfg (some 5) false true body (List.replicate n true) [] []) :=
    ⟨_, le_rfl, header_trace n body⟩
  exact ⟨binary, hv, hlen, hheader.trans hcounter⟩

end SubexponentialSAT.FrontendProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_BinaryCompareProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Minimal actual binary comparison, extracted from SubexpGuardProgram.
Only the concrete Boolean borrow operation and fixed comparison machine are retained.
The source map and hashes are recorded in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.BinaryArithmetic

namespace Compare

/-- The final borrow is the strict comparison, even for unequal word lengths. -/
theorem carry_iff (xs ys : List Bool) (c : Bool) :
    carry c xs ys = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys + bitVal c := by
  induction xs generalizing ys c with
  | nil =>
    induction ys generalizing c with
    | nil => cases c <;> simp [carry, bitVal]
    | cons b ys ih =>
      rw [carry, ih]
      cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
  | cons a xs ih =>
    cases ys with
    | nil =>
      rw [carry, ih]
      cases a <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat]
    | cons b ys =>
      rw [carry, ih]
      cases a <;> cases b <;> cases c <;>
        simp [borrowBit, bitVal, BinaryArithmetic.toNat] <;> omega

private theorem update_left (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 0 zs = operandStacks zs ys := by
  funext i
  fin_cases i <;> simp [operandStacks]

private theorem update_right (xs ys zs : List Bool) :
    Function.update (operandStacks xs ys) 1 zs = operandStacks xs zs := by
  funext i
  fin_cases i <;> simp [operandStacks]

theorem roundRegs_borrow (regs : Fin 8 → Bool) (a b : Option Bool) :
    roundRegs regs a b 0 = borrowBit (a.getD false) (b.getD false) (regs 0) := by
  simp only [roundRegs, Function.update_self]
  cases ha : a.getD false <;> cases hb : b.getD false <;> cases hc : regs 0 <;>
    simp [borrowBit]

private theorem round_nil_cons (regs : Fin 8 → Bool) (b : Bool) (ys : List Bool) :
    Trace program 10 (cfg (some 1) regs [] (b :: ys))
      (cfg (some 1) (roundRegs regs none (some b)) [] ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_nil (regs : Fin 8 → Bool) (a : Bool) (xs : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) [])
      (cfg (some 1) (roundRegs regs (some a) none) xs []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

private theorem round_cons_cons (regs : Fin 8 → Bool) (a b : Bool) (xs ys : List Bool) :
    Trace program 10 (cfg (some 1) regs (a :: xs) (b :: ys))
      (cfg (some 1) (roundRegs regs (some a) (some b)) xs ys) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, roundRegs, readRegs, update_left, update_right, Function.update_apply]

/-- A concrete nonterminal round, including its branch instruction. -/
theorem round_trace (regs : Fin 8 → Bool) (xs ys : List Bool)
    (hne : xs ≠ [] ∨ ys ≠ []) :
    Trace program 10 (cfg (some 1) regs xs ys)
      (cfg (some 1) (roundRegs regs xs.head? ys.head?) xs.tail ys.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at hne
    | cons b ys => exact round_nil_cons regs b ys
  | cons a xs =>
    cases ys with
    | nil => exact round_cons_nil regs a xs
    | cons b ys => exact round_cons_cons regs a b xs ys

theorem exit_trace (regs : Fin 8 → Bool) :
    Trace program 5 (cfg (some 1) regs [] []) (cfg none (exitRegs regs) [] []) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, execInstr, cfg,
    read, exitRegs, readRegs, update_left, update_right,
    Function.update_apply]

/-- Exact instruction count for the data-dependent loop. -/
theorem loop_trace (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 5)
        (cfg (some 1) regs xs ys) (cfg none rf [] []) ∧
      rf 0 = carry (regs 0) xs ys := by
  induction xs generalizing ys regs with
  | nil =>
    induction ys generalizing regs with
    | nil =>
      exact ⟨exitRegs regs, by simpa using exit_trace regs, by simp [carry]⟩
    | cons b ys ih =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs none (some b))
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs [] (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
  | cons a xs ih =>
    cases ys with
    | nil =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) none) []
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) [] (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb
    | cons b ys =>
      obtain ⟨rf, hr, hb⟩ := ih (roundRegs regs (some a) (some b)) ys
      refine ⟨rf, ?_, ?_⟩
      · have h := (round_trace regs (a :: xs) (b :: ys) (by simp)).trans hr
        simpa [cfg, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · simpa [carry, roundRegs_borrow] using hb

/-- Complete comparator contract. Leading zero bits and unequal widths are allowed. -/
theorem run (regs : Fin 8 → Bool) (xs ys : List Bool) :
    ∃ rf : Fin 8 → Bool,
      Trace program (10 * max xs.length ys.length + 6)
        (cfg (some program.entry) regs xs ys) (cfg none rf [] []) ∧
      (rf 0 = true ↔ BinaryArithmetic.toNat xs < BinaryArithmetic.toNat ys) := by
  obtain ⟨rf, hr, hb⟩ := loop_trace (Function.update regs 0 false) xs ys
  refine ⟨rf, ?_, ?_⟩
  · have he : Trace program 1 (cfg (some program.entry) regs xs ys)
        (cfg (some 1) (Function.update regs 0 false) xs ys) := by
      exact .cons (by rfl) (.refl _)
    convert he.trans hr using 1
    all_goals try with_reducible_and_instances rfl
    omega
  · rw [hb]
    simpa only [Function.update_self, bitVal_false, Nat.add_zero] using carry_iff xs ys false

end Compare

open StructuredProgram

private theorem extend_restrict {α β γ : Type} (f : α → β) (hf : Function.Injective f)
    (g : β → γ) : Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases hb : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := hb
    exact hf.extend_apply _ _ _
  · exact Function.extend_apply' _ _ _ hb

private theorem embed_restrict {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    StructuredCalls.embedState register stack a (restrictState register stack a) = a := by
  unfold StructuredCalls.embedState restrictState
  change State.mk (Function.extend register (a.regs ∘ register) a.regs)
    (Function.extend stack (a.stacks ∘ stack) a.stacks) = a
  rw [extend_restrict register hr, extend_restrict stack hs]

private theorem pair_eta (f : Fin 2 → List Bool) : Compare.operandStacks (f 0) (f 1) = f := by
  first | done | (funext i; fin_cases i <;> rfl)

/-- A measured comparison call on fixed injective ports, with every other
caller register and stack preserved. -/
theorem compare_call {R S : ℕ} (register : Fin 8 → Fin R) (stack : Fin 2 → Fin S)
    (hr : Function.Injective register) (hs : Function.Injective stack) (a : State R S) :
    ∃ b : State R S,
      StructuredCalls.Eval (.call (ProgramLinking.liftProgram Compare.program register stack))
        (10 * max (a.stacks (stack 0)).length (a.stacks (stack 1)).length + 6) a b ∧
      (b.regs (register 0) = true ↔
        BinaryArithmetic.toNat (a.stacks (stack 0)) <
          BinaryArithmetic.toNat (a.stacks (stack 1))) ∧
      (∀ i, (¬ ∃ j, register j = i) → b.regs i = a.regs i) ∧
      (∀ i, (¬ ∃ j, stack j = i) → b.stacks i = a.stacks i) ∧
      (∀ j, b.stacks (stack j) = []) := by
  obtain ⟨rf, hrun, hcmp⟩ := Compare.run (fun i => a.regs (register i))
    (a.stacks (stack 0)) (a.stacks (stack 1))
  have hstack := pair_eta (fun i => a.stacks (stack i))
  have hempty : Compare.operandStacks [] [] = (fun _ : Fin 2 => []) := by
    simpa using pair_eta (fun _ : Fin 2 => [])
  simp only [Compare.cfg, hstack, hempty] at hrun
  let localOut : State 8 2 := ⟨rf, fun _ => []⟩
  let b := StructuredCalls.embedState register stack a localOut
  refine ⟨b, ?_, ?_, ?_, ?_, ?_⟩
  · have h := StructuredCalls.eval_call_lifted Compare.program register stack a hr hs
      (a := restrictState register stack a) (b := localOut) hrun
    rw [embed_restrict register stack hr hs a] at h
    exact h
  · simpa only [b, StructuredCalls.embedState_register register stack a localOut hr,
      localOut] using hcmp
  · exact fun i hi => StructuredCalls.embedState_register_frame register stack a localOut i hi
  · exact fun i hi => StructuredCalls.embedState_stack_frame register stack a localOut i hi
  · exact fun j => StructuredCalls.embedState_stack register stack a localOut hs j


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.BinaryCompareProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpSunflowerProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Actual finite programs used by sunflower candidate checking

Runtime clause counts and widths remain encoded stack data. The first
primitive counts framed records; it is an actual finite instruction table,
with a trace theorem, rather than a semantic list-length instruction.
-/
namespace SubexponentialSAT.SubexpSunflowerProgram

open BitProgram

namespace CountRecords

theorem start (value present : Bool) (input output : List Bool) :
    Trace program 2 (cfg (some 0) value present input output)
      (cfg (some 2) false present input (false :: output)) := by
  apply Computation.Trace.of_iterate
  simp [Function.iterate_succ_apply, step, program, cfg, execInstr, readRegs,
    ParserProgram.pair]

theorem trace (records : List (List Bool)) (suffix output : List Bool)
    (value present : Bool) :
    Trace program (steps records)
      (cfg (some program.entry) value present (Encoding.encodeList id records ++ suffix) output)
      (cfg none false false suffix (Encoding.encodeNat records.length ++ output)) := by
  have h := (start value present (Encoding.encodeList id records ++ suffix) output).trans
    (loop_trace records suffix (false :: output) false present)
  simpa [steps, Encoding.encodeNat, Nat.add_comm, List.append_assoc] using h

end CountRecords

end SubexponentialSAT.SubexpSunflowerProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityPrimitives
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete record-count and emission primitives extracted from supplied sources.
No sparsification schedule or formula evaluator is imported. Provenance is recorded
in verification/counting-draft/worker04/extraction.json. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives

open BitProgram StructuredCalls BinaryArithmetic

namespace Tuple

theorem copy_eval (src dst : Fin 9) (d : Data)
    (hsd : src ≠ dst) (hst : src ≠ 8) (htd : (8 : Fin 9) ≠ dst)
    (htmp : d.stacks 8 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d (copied src dst d) := by
  have ht := StackRoutines.copyProgram_trace src dst 8 (0 : Fin 13) 1
    hsd hst htd (by decide) d.regs d.stacks htmp
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  apply Eval.call
  simpa [copied, StackRoutines.copyResult, StackRoutines.copyProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem clear_eval (port : Fin 9) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d (cleared port d) := by
  have ht := StackRoutines.clearProgram_trace port (0 : Fin 13) 1 d.regs d.stacks
  have hh := StackRoutines.halt_after_trace _ ht 2 rfl rfl
  apply Eval.call
  simpa [cleared, StackRoutines.clearResult, StackRoutines.clearProgram,
    StructuredProgram.State.withPC, Nat.add_assoc] using hh

theorem workReg_injective : Function.Injective workReg := Fin.castAdd_injective 8 5

theorem pairPort_injective (left right : Fin 9) (h : left ≠ right) :
    Function.Injective (pairPort left right) := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [pairPort]

theorem compare_eval (left right : Fin 9) (h : left ≠ right) (d : Data) :
    ∃ e : Data,
      Eval (compare left right)
        (10 * max (d.stacks left).length (d.stacks right).length + 6) d e ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) ∧
      (∀ i : Fin 9, i ≠ left → i ≠ right → e.stacks i = d.stacks i) ∧
      e.stacks left = [] ∧ e.stacks right = [] := by
  obtain ⟨e, he, ha, hr, hs, hz⟩ := BinaryCompareProgram.compare_call workReg
    (pairPort left right) workReg_injective (pairPort_injective left right h) d
  refine ⟨e, he, ?_, ?_, ?_, hz 0, hz 1⟩
  · apply Bool.eq_iff_iff.mpr
    simpa [workReg, pairPort] using ha
  · intro i hi
    apply hr
    rintro ⟨j, hj⟩
    have hjv := congrArg Fin.val hj
    change j.val = i.val at hjv
    have := j.isLt
    omega
  · intro i hl hr'
    apply hs
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [pairPort] at hj <;> subst i <;> contradiction

end Tuple

namespace Count

open OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives.Tuple
  (Data copied copy copy_eval cleared clear clear_eval)

theorem countReg_injective : Function.Injective countReg := Fin.castAdd_injective 2 11
theorem countStack_injective : Function.Injective countStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [countStack]

theorem count_eval (records : List (List Bool)) (d : Data)
    (hinput : d.stacks 5 = Encoding.encodeList id records) (houtput : d.stacks 7 = []) :
    Eval (.call countProgram) (SubexpSunflowerProgram.CountRecords.steps records)
      d (counted records d) := by
  let b : State 2 2 := ⟨ParserProgram.pair false false,
    ParserProgram.pair [] (Encoding.encodeNat records.length)⟩
  have hstart : (projectState countReg countStack d).withPC
      (some SubexpSunflowerProgram.CountRecords.program.entry) =
      SubexpSunflowerProgram.CountRecords.cfg
        (some SubexpSunflowerProgram.CountRecords.program.entry) (d.regs 0) (d.regs 1)
        (Encoding.encodeList id records) [] := by
    simp only [projectState, StructuredProgram.State.withPC,
      SubexpSunflowerProgram.CountRecords.cfg, Cfg.mk.injEq, true_and]
    constructor <;> funext i <;> fin_cases i <;>
      simp [countReg, countStack, ParserProgram.pair, hinput, houtput]
  have ht : Trace SubexpSunflowerProgram.CountRecords.program
      (SubexpSunflowerProgram.CountRecords.steps records)
      ((projectState countReg countStack d).withPC
        (some SubexpSunflowerProgram.CountRecords.program.entry)) (b.withPC none) := by
    rw [hstart]
    simpa [b, SubexpSunflowerProgram.CountRecords.cfg, StructuredProgram.State.withPC] using
      SubexpSunflowerProgram.CountRecords.trace records [] [] (d.regs 0) (d.regs 1)
  have hb : embedState countReg countStack d b = counted records d := by
    apply embedState_eq_of_ports _ _ _ _ _ countReg_injective countStack_injective
    · intro i; fin_cases i <;> simp [counted, countReg, readRegs, b]
    · intro i hi
      have hi0 : i ≠ 0 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi1 : i ≠ 1 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, readRegs, hi0, hi1]
    · intro i; fin_cases i <;> simp [counted, countStack, b]
    · intro i hi
      have hi5 : i ≠ 5 := by intro h; apply hi; exact ⟨0, h.symm⟩
      have hi7 : i ≠ 7 := by intro h; apply hi; exact ⟨1, h.symm⟩
      simp [counted, hi5, hi7]
  simpa only [hb, countProgram] using eval_call_from_state
    SubexpSunflowerProgram.CountRecords.program countReg countStack d
    countReg_injective countStack_injective ht

theorem reset_eval (d : Data) : Eval reset 3 d (resetState d) :=
  .seq (.base (.atom _ _)) (.seq (.base (.atom _ _)) (.base (.atom _ _)))

theorem binaryReg_injective : Function.Injective binaryReg := Fin.castAdd_injective 3 10
theorem binaryStack_injective : Function.Injective binaryStack := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [binaryStack]

/-- Convert an input-sized unary record count to binary. The cost comes from
the actual header parser and dynamic binary length counter. -/
theorem toBinary_eval (n : ℕ) (d : Data) (h7 : d.stacks 7 = Encoding.encodeNat n)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ FrontendProgram.initializeBound n + 3, ∃ bits : List Bool, ∃ e : Data,
      Eval toBinary t d e ∧ toNat bits = n ∧ bits.length ≤ n ∧
      e.stacks = Function.update (Function.update d.stacks 7 []) 6 bits ∧
      (∀ i : Fin 13, 3 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨bits, hvalue, hlength, t, ht, htrace⟩ := FrontendProgram.initialize_raw n []
  let a := resetState d
  let b : State 3 4 := StructuredProgram.State.ofCfg
    (FrontendProgram.cfg none false false [] [] bits [])
  have hstart : (projectState binaryReg binaryStack a).withPC
      (some FrontendProgram.initializeProgram.entry) =
      initial FrontendProgram.initializeProgram (Encoding.encodeNat n ++ []) := by
    rw [FrontendProgram.initialize_initial]
    simp only [projectState, StructuredProgram.State.withPC, FrontendProgram.cfg,
      Cfg.mk.injEq]
    refine ⟨rfl, ?_, ?_⟩
    · funext i
      fin_cases i <;> simp [a, resetState, binaryReg, CounterPrograms.counterRegs]
    · funext i
      fin_cases i <;> simp [a, resetState, binaryStack, FrontendProgram.storage,
        h7, h5, h6, h8]
  have hl : Trace FrontendProgram.initializeProgram t
      ((projectState binaryReg binaryStack a).withPC
        (some FrontendProgram.initializeProgram.entry)) (b.withPC none) := by
    rw [hstart]
    exact htrace
  have he := eval_call_from_state FrontendProgram.initializeProgram binaryReg binaryStack a
    binaryReg_injective binaryStack_injective hl
  let e := embedState binaryReg binaryStack a b
  have hs (i : Fin 4) : e.stacks (binaryStack i) = b.stacks i :=
    embedState_stack _ _ _ _ binaryStack_injective i
  refine ⟨3 + t, by omega, bits, e, Eval.seq (reset_eval d) he, ?_, hlength, ?_, ?_⟩
  · simpa only [CounterPrograms.value_eq_toNat] using hvalue
  · funext i
    fin_cases i
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · exact embedState_stack_frame _ _ _ _ _ (by decide)
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h5] using hs 1
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 2
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg] using hs 0
    · simpa [binaryStack, b, FrontendProgram.cfg, FrontendProgram.storage,
        StructuredProgram.State.ofCfg, h8] using hs 3
  · intro i hi
    have hfr : e.regs i = a.regs i := by
      apply embedState_register_frame
      rintro ⟨j, hj⟩
      have hjv := congrArg Fin.val hj
      change j.val = i.val at hjv
      have := j.isLt
      omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hi2 : i ≠ 2 := by intro h; subst i; simp at hi
    simpa [a, resetState, hi0, hi1, hi2] using hfr

theorem less_eval (left right : Fin 9) (d : Data)
    (hl : left ≠ 5 ∧ left ≠ 7 ∧ left ≠ 8)
    (hr : right ≠ 5 ∧ right ≠ 7 ∧ right ≠ 8)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 20 * ((d.stacks left).length + (d.stacks right).length + 1), ∃ e : Data,
      Eval (less left right) n d e ∧ e.stacks = d.stacks ∧
      e.regs 0 = decide (toNat (d.stacks left) < toNat (d.stacks right)) ∧
      (∀ i : Fin 13, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := copied left 5 d
  let b := copied right 7 a
  have ha8 : a.stacks 8 = [] := by simpa [a, copied, StackRoutines.copyStacks] using h8
  have har : a.stacks right = d.stacks right := by simp [a, copied, StackRoutines.copyStacks, hr.1]
  have hb5 : b.stacks 5 = d.stacks left := by simp [b, a, copied, StackRoutines.copyStacks, h5]
  have hb7 : b.stacks 7 = d.stacks right := by
    simp [b, a, copied, StackRoutines.copyStacks, hr.1, h7]
  obtain ⟨e, he, hresult, hregs, hstacks, he5, he7⟩ :=
    Tuple.compare_eval 5 7 (by decide) b
  refine ⟨(7 * (d.stacks left).length + 5) + ((7 * (a.stacks right).length + 5) +
    (10 * max (b.stacks 5).length (b.stacks 7).length + 6)), ?_, e, ?_, ?_, ?_, ?_⟩
  · rw [har, hb5, hb7]
    have hmax := max_le
      (Nat.le_add_right (d.stacks left).length (d.stacks right).length)
      (Nat.le_add_left (d.stacks right).length (d.stacks left).length)
    omega
  · exact Eval.seq (copy_eval left 5 d hl.1 hl.2.2 (by decide) h8)
      (Eval.seq (copy_eval right 7 a hr.2.1 hr.2.2 (by decide) ha8) he)
  · funext i
    by_cases hi5 : i = 5
    · subst i; exact he5.trans h5.symm
    by_cases hi7 : i = 7
    · subst i; exact he7.trans h7.symm
    simpa [b, a, copied, StackRoutines.copyStacks, hi5, hi7] using hstacks i hi5 hi7
  · simpa [hb5, hb7] using hresult
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    simpa [b, a, copied, readRegs, hi0, hi1] using hregs i hi

/-- Numeric equality tolerates leading zero padding in the supplied bound.
Both comparisons consume only real copies of the preserved operands. -/
theorem numericEq_eval (expected : Fin 2) (d : Data)
    (h5 : d.stacks 5 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 50 * ((d.stacks 6).length + (d.stacks (expectedPort expected)).length + 1),
      ∃ e : Data, Eval (numericEq expected) n d e ∧ e.stacks = d.stacks ∧
        e.regs 4 = decide (toNat (d.stacks 6) = toNat (d.stacks (expectedPort expected))) ∧
        (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  have hp : expectedPort expected ≠ 5 ∧ expectedPort expected ≠ 7 ∧ expectedPort expected ≠ 8 := by
    fin_cases expected <;> decide
  obtain ⟨n, hn, a, ha, hast, ha0, hareg⟩ := less_eval 6 (expectedPort expected) d
    (by decide) hp h5 h7 h8
  let b := (StructuredProgram.Atom.copy (r := 13) (s := 9) 12 0).eval a
  have hbst : b.stacks = d.stacks := hast
  have hb12 : b.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) := by
    simpa [b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr] using ha0
  obtain ⟨m, hm, c, hc, hcst, hc0, hcreg⟩ := less_eval (expectedPort expected) 6 b hp
    (by decide) (by simpa only [hbst] using h5)
    (by simpa only [hbst] using h7) (by simpa only [hbst] using h8)
  let e := (StructuredProgram.Atom.bnot (r := 13) (s := 9) 4 4).eval
    ((StructuredProgram.Atom.bor (r := 13) (s := 9) 4 12 0).eval c)
  have hc12 : c.regs 12 = decide (toNat (d.stacks 6) < toNat (d.stacks (expectedPort expected))) :=
    (hcreg 12 (by decide)).trans hb12
  have hbool (a b : ℕ) : (!(decide (a < b) || decide (b < a))) = decide (a = b) := by
    apply Bool.eq_iff_iff.mpr
    simp
    omega
  refine ⟨n + (1 + (m + (1 + 1))), ?_, e, ?_, hcst.trans hbst, ?_, ?_⟩
  · rw [hbst] at hm
    omega
  · exact Eval.seq ha (Eval.seq (.base (.atom _ _))
      (Eval.seq hc (Eval.seq (.base (.atom _ _)) (.base (.atom _ _)))))
  · simp [e, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.ofCfg, execInstr,
      hc12, hc0, hbst, hbool]
  · intro i hi hne
    have hi4 : i ≠ 4 := by
      intro h
      subst i
      change 8 ≤ 4 at hi
      omega
    have hci := hcreg i hi
    have hai := hareg i hi
    simpa [e, b, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
      StructuredProgram.State.withPC, StructuredProgram.State.ofCfg, execInstr,
      hi4, hne, hai] using hci

/-- Count the actual records, convert the count, compare it with a supplied
binary word, and clear every temporary. Only the scanned input is consumed. -/
theorem countTest_eval (expected : Fin 2) (records : List (List Bool)) (d : Data)
    (hin : d.stacks 5 = Encoding.encodeList id records)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ n ≤ 200 * ((Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1) ^ 2, ∃ e : Data,
      Eval (countTest expected) n d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
      e.regs 4 = decide (records.length = toNat (d.stacks (expectedPort expected))) ∧
      (∀ i : Fin 13, 8 ≤ i.val → i ≠ 12 → e.regs i = d.regs i) := by
  let a := counted records d
  have ha7 : a.stacks 7 = Encoding.encodeNat records.length := by simp [a, counted]
  have ha5 : a.stacks 5 = [] := by simp [a, counted]
  have ha6 : a.stacks 6 = [] := by simpa [a, counted] using h6
  have ha8 : a.stacks 8 = [] := by simpa [a, counted] using h8
  obtain ⟨n, hn, bits, b, hb, hvalue, hlength, hbst, hbreg⟩ :=
    toBinary_eval records.length a ha7 ha5 ha6 ha8
  have hb5 : b.stacks 5 = [] := by simp [hbst, a, counted]
  have hb6 : b.stacks 6 = bits := by simp [hbst]
  have hb7 : b.stacks 7 = [] := by simp [hbst]
  have hb8 : b.stacks 8 = [] := by simpa [hbst, a, counted] using h8
  have hbexpected : b.stacks (expectedPort expected) = d.stacks (expectedPort expected) := by
    fin_cases expected <;> simp [expectedPort, hbst, a, counted]
  obtain ⟨m, hm, c, hc, hcst, hc4, hcreg⟩ := numericEq_eval expected b hb5 hb7 hb8
  let e := cleared 6 c
  have hm' : m ≤ 50 * (bits.length + (d.stacks (expectedPort expected)).length + 1) := by
    simpa [hb6, hbexpected] using hm
  have hc6 : c.stacks 6 = bits := by simpa [hcst] using hb6
  refine ⟨SubexpSunflowerProgram.CountRecords.steps records +
    (n + (m + (2 * (c.stacks 6).length + 3))), ?_, e,
    Eval.seq (count_eval records d hin h7) (Eval.seq hb (Eval.seq hc (clear_eval 6 c))),
    ?_, ?_, ?_⟩
  · rw [hc6]
    have hcount := SubexpSunflowerProgram.CountRecords.steps_le_encoded records
    have hrecords := Encoding.length_encodeList_lower id records
    have hrecords' : records.length ≤ (Encoding.encodeList id records).length := by omega
    have hquad := Nat.mul_le_mul hrecords' hrecords'
    have hbits : bits.length ≤ (Encoding.encodeList id records).length :=
      hlength.trans hrecords'
    have hsum : bits.length + (d.stacks (expectedPort expected)).length + 1 ≤
        (Encoding.encodeList id records).length +
          (d.stacks (expectedPort expected)).length + 1 := by omega
    have hsumquad := Nat.mul_le_mul hsum hsum
    rw [FrontendProgram.initializeBound_eq] at hn
    let H := (Encoding.encodeList id records).length +
      (d.stacks (expectedPort expected)).length + 1
    have hH : 1 ≤ H := by dsimp [H]; omega
    have hEH : (Encoding.encodeList id records).length ≤ H := by dsimp [H]; omega
    have hRH : records.length ≤ H := hrecords'.trans hEH
    have hBH : bits.length ≤ H := hbits.trans hEH
    have hsq : H ≤ H ^ 2 := by
      rw [pow_two]
      exact Nat.le_mul_of_pos_right _ hH
    have hRsq : records.length ^ 2 ≤ H ^ 2 := Nat.pow_le_pow_left hRH 2
    have hcount' : SubexpSunflowerProgram.CountRecords.steps records ≤ 7 * H ^ 2 := by
      have h7 := Nat.mul_le_mul_left 7 hsq
      omega
    have hn' : n ≤ 32 * H ^ 2 := by
      have h8 := Nat.mul_le_mul_left 8 hRsq
      have h14 := Nat.mul_le_mul_left 14 (hRH.trans hsq)
      have h10 : 10 ≤ 10 * H ^ 2 := by omega
      omega
    have hm'' : m ≤ 50 * H ^ 2 := by
      have hmH : m ≤ 50 * H := hm'.trans (Nat.mul_le_mul_left 50 (by
        dsimp [H]
        exact hsum))
      exact hmH.trans (Nat.mul_le_mul_left 50 hsq)
    have hclear : 2 * bits.length + 3 ≤ 5 * H ^ 2 := by
      have h5 := Nat.mul_le_mul_left 5 hsq
      omega
    change SubexpSunflowerProgram.CountRecords.steps records +
        (n + (m + (2 * bits.length + 3))) ≤ 200 * H ^ 2
    omega
  · funext i
    fin_cases i <;> simp [e, cleared, StackRoutines.clearStacks, hcst, hbst, a, counted, h6, h7]
  · simpa [e, cleared, readRegs, hb6, hbexpected, hvalue] using hc4
  · intro i hi hne
    have hi3 : 3 ≤ i.val := by omega
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hh := (hcreg i hi hne).trans (hbreg i hi3)
    simpa [e, cleared, readRegs, a, counted, hi0, hi1] using hh

end Count

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityPrimitives
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_DisjointReuse_SparsePriorityProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.decidableMemSide _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete components of the sharp clause/core search from Appendix A.
The guard counts actual framed literals and executes the preserving subset tester.
The complete search and its polynomial resource bound are developed separately below. -/


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RecordSearch
open OAI.Algorithms.SubexponentialSAT.RecordPrograms StructuredCalls

theorem loop_run_with_miss_invariant {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : ∀ (bits tail : List Bool) (base : State r s),
      validPayload bits → invariant base →
      ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧
        (test bits = false → invariant next) ∧ effect bits base next ∧
        Eval callback n (state p base false true false tail bits.reverse)
          (state p next false true (test bits) tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base) :
    ∃ (n : ℕ) (next : State r s), n ≤ 1 + budget cost records ∧ (records.any test = false → invariant next) ∧
      Visits test effect records base next ∧
      Eval (loop p callback) n (afterTag p base records suffix)
        (state p next false true (records.any test) (unread test records suffix) []) := by
  induction records generalizing base with
  | nil =>
      refine ⟨1, base, by simp [budget], (fun _ => valid), Visits.nil _, ?_⟩
      apply Eval.while_false
      simp [afterTag]
  | cons bits rest ih =>
      let tail := Encoding.encodeList id rest ++ suffix
      obtain ⟨n, middle, hn, hmiddle, heffect, hcallback⟩ :=
        contract bits tail base (validRecords bits (by simp)) valid
      have hreader : Eval (reader p) (6 * bits.length + 4)
          (afterTag p base (bits :: rest) suffix)
          (state p base false true false tail bits.reverse) := by
        simpa [afterTag, tail] using reader_eval p base bits tail [] true true false
      have hguard : (afterTag p base (bits :: rest) suffix).regs p.tag = true := by
        simp [afterTag]
      cases ht : test bits with
      | true =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (state p middle false true true tail []) := by
            rw [ht]
            apply Eval.ite_true (by simp)
            exact set_tag_eval p middle false true true false tail []
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          have hfinish : Eval (loop p callback) 1
              (state p middle false true true tail [])
              (state p middle false true true tail []) := Eval.while_false (by simp)
          have hrun := Eval.while_true hguard hbody hfinish
          refine ⟨(6 * bits.length + 4 + (n + 2)) + 1 + 1, middle, ?_, (by simp [ht]),
            Visits.hit ht heffect, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht, tail] using hrun
      | false =>
          have hbranch : Eval
              (.ite p.found (atom (.set p.tag false)) (atom (.pop p.source p.tag p.present))) 2
              (state p middle false true (test bits) tail [])
              (afterTag p middle rest suffix) := by
            rw [ht]
            apply Eval.ite_false (by simp)
            exact pop_list_eval p middle rest suffix false true
          have hbody := Eval.seq hreader (Eval.seq hcallback hbranch)
          obtain ⟨m, next, hm, hnext, hhistory, hrest⟩ :=
            ih middle (fun item hi => validRecords item (by simp [hi])) (hmiddle ht)
          have hrun := Eval.while_true hguard hbody hrest
          refine ⟨(6 * bits.length + 4 + (n + 2)) + m + 1, next, ?_, (by simpa [ht] using hnext),
            Visits.miss ht heffect hhistory, ?_⟩
          · simp only [budget]
            omega
          · simpa [loop, body, unread, ht] using hrun

theorem iterate_run_with_miss_invariant {r s : ℕ} (p : Ports r s) (callback : Cmd r s)
    (test : List Bool → Bool) (cost : List Bool → ℕ) (invariant : State r s → Prop)
    (effect : List Bool → State r s → State r s → Prop) (validPayload : List Bool → Prop)
    (contract : ∀ (bits tail : List Bool) (base : State r s),
      validPayload bits → invariant base →
      ∃ (n : ℕ) (next : State r s), n ≤ cost bits ∧
        (test bits = false → invariant next) ∧ effect bits base next ∧
        Eval callback n (state p base false true false tail bits.reverse)
          (state p next false true (test bits) tail []))
    (records : List (List Bool)) (suffix : List Bool) (base : State r s)
    (validRecords : ∀ bits ∈ records, validPayload bits) (valid : invariant base)
    (v pr f : Bool) :
    ∃ (n : ℕ) (next : State r s), n ≤ 3 + budget cost records ∧ (records.any test = false → invariant next) ∧
      Visits test effect records base next ∧
      Eval (iterate p callback) n
        (state p base v pr f (Encoding.encodeList id records ++ suffix) [])
        (state p next false true (records.any test) (unread test records suffix) []) := by
  obtain ⟨n, next, hn, hnext, hhistory, hloop⟩ :=
    loop_run_with_miss_invariant p callback test cost invariant effect validPayload contract
      records suffix base validRecords valid
  refine ⟨1 + (1 + n), next, by omega, hnext, hhistory, ?_⟩
  exact Eval.seq (set_found_eval p base v pr f false _ [])
    (Eval.seq (pop_list_eval p base records suffix v pr) hloop)


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.RecordSearch


namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

theorem length_perm {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Perm ys) :
    (Encoding.encodeList enc xs).length = (Encoding.encodeList enc ys).length := by
  induction h with
  | nil => rfl
  | cons a h ih => simp only [Encoding.length_encodeList_cons, ih]
  | swap a b xs => simp only [Encoding.length_encodeList_cons]; omega
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂

theorem length_reverse {α : Type*} (enc : α → List Bool) (xs : List α) :
    (Encoding.encodeList enc xs.reverse).length = (Encoding.encodeList enc xs).length :=
  length_perm enc (List.reverse_perm xs)

theorem length_le_of_sublist {α : Type*} (enc : α → List Bool)
    {xs ys : List α} (h : xs.Sublist ys) :
    (Encoding.encodeList enc xs).length ≤ (Encoding.encodeList enc ys).length := by
  induction h with
  | slnil => exact Nat.le_refl _
  | cons a h ih =>
      rw [Encoding.length_encodeList_cons]
      omega
  | cons_cons a h ih =>
      rw [Encoding.length_encodeList_cons, Encoding.length_encodeList_cons]
      omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.EncodingLength

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram

open OAI.Algorithms.SubexponentialSAT.BitProgram OAI.Algorithms.SubexponentialSAT.StructuredCalls

theorem masked_sublist {α : Type*} (mask : List Bool) (C : List α) :
    (masked mask C).Sublist C := by
  induction C generalizing mask with
  | nil => exact .slnil
  | cons x xs ih =>
    simp only [masked]
    split
    · exact .cons_cons x (ih mask.tail)
    · exact .cons x (ih mask.tail)

theorem masked_words (mask : List Bool) (C : Clause) :
    masked mask C = CoreMaskProgram.select mask C := by
  induction C generalizing mask with
  | nil => rfl
  | cons x xs ih => simp only [masked, CoreMaskProgram.select]; split <;> simp [ih]

theorem rawCandidate_spec {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, C.length = c ∧ H.Sublist C := by
  obtain ⟨C, hC, hm⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, _, hp⟩ := List.mem_map.mp hm
  obtain ⟨hc, hH⟩ := Prod.mk.inj hp
  exact ⟨C, hC, hc, hH ▸ masked_sublist mask C⟩

namespace Filter

theorem formulaCode_records (F : Formula) :
    formulaCode F = Encoding.encodeList id (records F) := by
  induction F with
  | nil => rfl
  | cons C F ih => simpa [formulaCode, records, Encoding.encodeList] using ih


theorem member_length_le (records : List (List Bool)) (bits : List Bool) (h : bits ∈ records) :
    bits.length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · rw [Encoding.length_encodeList_cons]
      simp only [id_eq]
      omega
    · exact (ih h).trans (by rw [Encoding.length_encodeList_cons]; omega)


end Filter

namespace ThresholdPower

theorem command_eval (exponent : ℕ) (base : List Bool) (regs : PowerPrograms.Regs) :
    ∃ t ≤ PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 3,
      ∃ rf : PowerPrograms.Regs, ∃ word : List Bool,
        Eval (command exponent) t (PowerPrograms.state regs base [] [])
          (PowerPrograms.state rf base [] word) ∧
        BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
        word.length ≤ 1 + exponent * base.length := by
  obtain ⟨ra, ha⟩ := ArithmeticExpressionSupport.pushWord_eval
    (1 : Fin 9) exponent.bits (PowerPrograms.state regs base [] [])
  have hstart : (⟨ra, Function.update (PowerPrograms.state regs base [] []).stacks 1
      (exponent.bits ++ (PowerPrograms.state regs base [] []).stacks 1)⟩ : State 8 9) =
      PowerPrograms.state ra base exponent.bits [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [PowerPrograms.state, PowerPrograms.stackState]
  rw [hstart] at ha
  obtain ⟨d, hv, hl, hd0, _, hd1, hwork, t, ht, htrace⟩ :=
    PowerPrograms.run_value ra base exponent.bits
  have hc := ArithmeticExpressionSupport.clear_eval (1 : Fin 9) d
  have hfinish : (⟨readRegs d.regs 0 1 none, Function.update d.stacks 1 []⟩ : State 8 9) =
      PowerPrograms.state (readRegs d.regs 0 1 none) base [] (d.stacks 2) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [PowerPrograms.stackState, hd0]
    all_goals exact hwork _ (by decide)
  rw [hfinish] at hc
  refine ⟨2 * exponent.bits.length + (t + (2 * (d.stacks 1).length + 3)),
    by omega, readRegs d.regs 0 1 none, d.stacks 2, ha.seq ((Eval.call _ htrace).seq hc), ?_, ?_⟩
  · simpa only [ArithmeticExpressionSupport.bits_value] using hv
  · simpa only [ArithmeticExpressionSupport.bits_value] using hl

end ThresholdPower

namespace Mask

theorem applyMask_eval (C : Clause) (mask : List Bool) (regs : Regs) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 1, ∃ rf : Regs,
      Eval applyMask t (state regs (Encoding.encodeList id C) mask [])
        (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C))) := by
  obtain ⟨t, ht, he⟩ := CoreMaskProgram.call_eval C [] mask (regs 0) (regs 1) (regs 2) (regs 3)
  let d := state regs (Encoding.encodeList id C) mask []
  let b := CoreMaskProgram.state false false false false [] (mask.drop C.length) []
    (Encoding.encodeList id (CoreMaskProgram.select mask C))
  have hs : projectState regPort id d =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
        (Encoding.encodeList id C ++ []) mask [] [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
    · funext i; fin_cases i <;> simp [d, state,
        CoreMaskProgram.stackData]
  have hr : Function.Injective regPort := Fin.castAdd_injective 4 4
  have hl := eval_liftCommand_from_state (.call CoreMaskProgram.program) 0 3 regPort id d
    hr Function.injective_id (hs.symm ▸ he)
  let e := embedState regPort id d b
  have heq : e = state e.regs [] (mask.drop C.length)
      (Encoding.encodeList id (masked mask C)) := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    apply (Function.injective_id.extend_apply b.stacks d.stacks i).trans
    fin_cases i <;> simp [b, CoreMaskProgram.state, CoreMaskProgram.stackData, masked_words]
  exact ⟨t + 1, Nat.add_le_add_right ht 1, e.regs, heq ▸ hl⟩

theorem command_eval (C : Clause) (mask : List Bool) (regs : Regs) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 4 * mask.length + 4,
      ∃ rf : Regs, Eval (command mask) t (state regs (Encoding.encodeList id C) [] [])
        (state rf [] [] (Encoding.encodeList id (masked mask C))) := by
  obtain ⟨ra, ha⟩ := ArithmeticExpressionSupport.pushWord_eval
    (1 : Fin 4) mask (state regs (Encoding.encodeList id C) [] [])
  have ha' : Eval (ArithmeticExpressionSupport.pushWord 1 mask) (2 * mask.length)
      (state regs (Encoding.encodeList id C) [] []) (state ra (Encoding.encodeList id C) mask []) := by
    convert ha using 1
    all_goals try with_reducible_and_instances rfl
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [state]
  obtain ⟨t, ht, rf, he⟩ := applyMask_eval C mask ra
  have hc := ArithmeticExpressionSupport.clear_eval (1 : Fin 4)
    (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C)))
  have hc' : Eval (ArithmeticExpressionSupport.clearCmd 1)
      (2 * (mask.drop C.length).length + 3)
      (state rf [] (mask.drop C.length) (Encoding.encodeList id (masked mask C)))
      (state (readRegs rf 0 1 none) [] [] (Encoding.encodeList id (masked mask C))) := by
    convert hc using 1
    · simp [state]
    · apply congrArg₂ StructuredProgram.State.mk rfl
      funext i
      fin_cases i <;> simp [state]
  refine ⟨2 * mask.length + (t + (2 * (mask.drop C.length).length + 3)), ?_,
    readRegs rf 0 1 none, ha'.seq (he.seq hc')⟩
  simp only [List.length_drop]
  omega

end Mask

namespace Selector

theorem mem_passes (k c h : ℕ) (mask : List Bool) :
    (c, h, mask) ∈ passes k ↔ 2 ≤ c ∧ c ≤ k ∧ 1 ≤ h ∧ h < c ∧ mask.length = k := by
  simp only [passes, List.mem_flatMap, List.mem_range, List.mem_map, mem_masks]
  constructor
  · rintro ⟨i, hi, j, hj, m, hm, he⟩
    cases he
    exact ⟨by omega, by omega, by omega, by omega, hm⟩
  · rintro ⟨hc, hck, hh, hhc, hm⟩
    refine ⟨c - 2, by omega, c - 1 - h, by omega, mask, hm, ?_⟩
    simp only [Prod.mk.injEq]
    exact ⟨by omega, by omega, True.intro⟩

theorem passes_pairwise (k : ℕ) :
    (passes k).Pairwise (fun p q => p.1 ≤ q.1 ∧ (p.1 = q.1 → q.2.1 ≤ p.2.1)) := by
  rw [passes, List.pairwise_flatMap]
  constructor
  · intro i hi
    rw [List.pairwise_flatMap]
    constructor
    · intro j hj
      rw [List.pairwise_map]
      exact List.pairwise_of_forall (by intros; exact ⟨Nat.le_refl _, fun _ => Nat.le_refl _⟩)
    · apply List.pairwise_lt_range.imp
      intro j j' hjj' p hp q hq
      obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
      obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hq
      exact ⟨Nat.le_refl _, by intro; dsimp; omega⟩
  · apply List.pairwise_lt_range.imp
    intro i i' hii' p hp q hq
    obtain ⟨j, hj, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hp
    obtain ⟨j', hj', hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨m', hm', rfl⟩ := List.mem_map.mp hq
    exact ⟨by dsimp; omega, by dsimp; omega⟩

/-- Every strictly preferable width/core-size phase occurs before a winning phase,
independently of mask and clause ties within that phase. -/
theorem higher_priority_mem_before {k : ℕ} {before after : List (ℕ × ℕ × List Bool)}
    {winner candidate : ℕ × ℕ × List Bool}
    (hsplit : passes k = before ++ winner :: after) (hmem : candidate ∈ passes k)
    (hbetter : candidate.1 < winner.1 ∨
      candidate.1 = winner.1 ∧ winner.2.1 < candidate.2.1) :
    candidate ∈ before := by
  have horder := passes_pairwise k
  rw [hsplit, List.pairwise_append] at horder
  rw [hsplit, List.mem_append, List.mem_cons] at hmem
  rcases hmem with hb | he | ha
  · exact hb
  · subst candidate
    omega
  · have hle := (List.pairwise_cons.mp horder.2.1).1 candidate ha
    rcases hbetter with hwidth | ⟨heq, hcore⟩
    · omega
    · have hc := hle.2 heq.symm
      omega


private theorem embed_stacks_eq {r s R S : ℕ} (register : Fin r → Fin R)
    (stack : Fin s → Fin S) (d : State R S) (b : State r s)
    (hs : Function.Injective stack) (out : Fin S → List Bool)
    (hports : ∀ j, b.stacks j = out (stack j))
    (hframe : ∀ i, (¬ ∃ j, stack j = i) → d.stacks i = out i) :
    (embedState register stack d b).stacks = out := by
  funext i
  by_cases hi : ∃ j, stack j = i
  · obtain ⟨j, rfl⟩ := hi
    exact (embedState_stack register stack d b hs j).trans (hports j)
  · exact (embedState_stack_frame register stack d b i hi).trans (hframe i hi)

theorem copy_eval (source target : Fin 24) (d : Data)
    (hs : source ≠ target) (hs8 : source ≠ 8) (ht8 : (8 : Fin 24) ≠ target)
    (h8 : d.stacks 8 = []) (ht : d.stacks target = []) :
    Eval (copy source target) (7 * (d.stacks source).length + 5) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks target (d.stacks source)⟩ := by
  have h := ListRegisterProgram.copy_run source target 8 (0 : Fin 24) 1
    hs hs8 ht8 (by decide) d.regs d.stacks h8
  apply Eval.call
  simpa [ListRegisterProgram.Run, StructuredProgram.State.withPC,
    StackRoutines.copyStacks, ht] using h

theorem transfer_eval (source target : Fin 24) (d : Data) (h : source ≠ target) :
    Eval (transfer source target) (3 * (d.stacks source).length + 3) d
      ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks source target d.stacks⟩ := by
  apply Eval.call
  exact ListRegisterProgram.transfer_run source target (0 : Fin 24) 1 h (by decide)
    d.regs d.stacks

theorem clear_eval (port : Fin 24) (d : Data) :
    Eval (clear port) (2 * (d.stacks port).length + 3) d
      ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩ := by
  apply Eval.call
  exact ListRegisterProgram.clear_run port (0 : Fin 24) 1 d.regs d.stacks

/-- Loading a fixed literal word touches only the low eight registers. -/
theorem load_eval (port : Fin 24) (word : List Bool) (d : Data) :
    ∃ e : Data, Eval (load port word) (2 * word.length + 1) d e ∧
      e.stacks = Function.update d.stacks port (word ++ d.stacks port) ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) id d
  obtain ⟨rf, he⟩ := ArithmeticExpressionSupport.pushWord_eval port word a
  let b : State 8 24 := ⟨rf, Function.update a.stacks port (word ++ a.stacks port)⟩
  let e := embedState (Fin.castAdd 16) id d b
  refine ⟨e, eval_liftCommand_from_state _ port port (Fin.castAdd 16) id d
    (Fin.castAdd_injective 8 16) Function.injective_id he, ?_, ?_⟩
  · funext i
    exact (embedState_stack _ _ _ _ Function.injective_id i)
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem maskStack_injective : Function.Injective maskStack := by decide

theorem maskCall_eval (mask : List Bool) (C : Clause) (d : Data)
    (h10 : d.stacks 10 = Encoding.encodeList id C) (h11 : d.stacks 11 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) :
    ∃ t ≤ CoreMaskProgram.runtimeBound C + 4 * mask.length + 5, ∃ e : Data,
      Eval (maskCall mask) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 10 []) 9
        (Encoding.encodeList id (masked mask C)) ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) maskStack d
  have ha : a = Mask.state a.regs (Encoding.encodeList id C) [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;> simp [maskStack, h10, h11, h8, h9]
  obtain ⟨t, ht, rf, he⟩ := Mask.command_eval C mask a.regs
  rw [← ha] at he
  let b := Mask.state rf [] [] (Encoding.encodeList id (masked mask C))
  let e := embedState (Fin.castAdd 16) maskStack d b
  refine ⟨t + 1, by omega, e, eval_liftCommand_from_state _ 0 3
    (Fin.castAdd 16) maskStack d (Fin.castAdd_injective 8 16) maskStack_injective he, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ maskStack_injective
    · intro j
      fin_cases j <;> simp [b, Mask.state, maskStack, h11, h8]
    · intro i hi
      have hi10 : i ≠ 10 := fun h => hi ⟨0, h.symm⟩
      have hi9 : i ≠ 9 := fun h => hi ⟨3, h.symm⟩
      simp [hi10, hi9]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem sizeStack_injective : Function.Injective sizeStack := by decide

theorem sizeCall_eval (C : Clause) (d : Data)
    (h5 : d.stacks 5 = Encoding.encodeList id C)
    (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = []) (h8 : d.stacks 8 = []) :
    ∃ t ≤ 200 * ((Encoding.encodeList id C).length + (d.stacks 20).length + 1) ^ 2 + 1,
      ∃ e : Data, Eval sizeCall t d e ∧ e.stacks = Function.update d.stacks 5 [] ∧
        e.regs 4 = decide (C.length = BinaryArithmetic.toNat (d.stacks 20)) ∧
        (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 11) sizeStack d
  obtain ⟨t, ht, b, he, hb, hv, _⟩ :=
    SparsePriorityPrimitives.Count.countTest_eval 0 C a h5 h6 h7 h8
  let e := embedState (Fin.castAdd 11) sizeStack d b
  refine ⟨t + 1, by simpa [a, projectState, sizeStack,
    SparsePriorityPrimitives.Count.expectedPort] using Nat.add_le_add_right ht 1,
    e, eval_liftCommand_from_state _ 5 5 (Fin.castAdd 11) sizeStack d
      (Fin.castAdd_injective 13 11) sizeStack_injective he, ?_, ?_, ?_⟩
  · apply embed_stacks_eq _ _ _ _ sizeStack_injective
    · intro j
      rw [hb]
      fin_cases j <;> simp [a, projectState, sizeStack]
    · intro i hi
      have hi5 : i ≠ 5 := fun h => hi ⟨5, h.symm⟩
      simp [hi5]
  · exact (embedState_register _ _ _ _ (Fin.castAdd_injective 13 11) 4).trans hv
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem powerStack_injective : Function.Injective powerStack := by decide

theorem powerCall_eval (exponent : ℕ) (base : List Bool) (d : Data)
    (h19 : d.stacks 19 = base) (h10 : d.stacks 10 = []) (h17 : d.stacks 17 = [])
    (hwork : ∀ i : Fin 6, d.stacks (Fin.castAdd 18 i) = []) :
    ∃ t ≤ PowerPrograms.runtimeBound base exponent.bits + 4 * exponent.bits.length + 4,
      ∃ word : List Bool, ∃ e : Data,
        Eval (powerCall exponent) t d e ∧ e.stacks = Function.update d.stacks 17 word ∧
        BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
        word.length ≤ 1 + exponent * base.length ∧
        (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  let a := projectState (Fin.castAdd 16) powerStack d
  have ha : a = PowerPrograms.state a.regs base [] [] := by
    apply congrArg₂ StructuredProgram.State.mk rfl
    funext i
    fin_cases i <;>
      simp [powerStack, PowerPrograms.stackState,
        h19, h10, h17]
    all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5
  obtain ⟨t, ht, rf, word, he, hv, hl⟩ := ThresholdPower.command_eval exponent base a.regs
  rw [← ha] at he
  let b := PowerPrograms.state rf base [] word
  let e := embedState (Fin.castAdd 16) powerStack d b
  refine ⟨t + 1, by omega, word, e, eval_liftCommand_from_state _ 0 2
    (Fin.castAdd 16) powerStack d (Fin.castAdd_injective 8 16) powerStack_injective he,
    ?_, hv, hl, ?_⟩
  · apply embed_stacks_eq _ _ _ _ powerStack_injective
    · intro j
      fin_cases j <;> simp [b, PowerPrograms.state, PowerPrograms.stackState,
        powerStack, h19, h10]
      all_goals first | exact hwork 0 | exact hwork 1 | exact hwork 2 | exact hwork 3 | exact hwork 4 | exact hwork 5
    · intro i hi
      have hi17 : i ≠ 17 := fun h => hi ⟨2, h.symm⟩
      simp [hi17]
  · intro i hi
    apply embedState_register_frame
    rintro ⟨j, hj⟩
    have hh := congrArg Fin.val hj
    change j.val = i.val at hh
    have := j.isLt
    omega

theorem prepareCandidate_eval (C : Clause) (mask : List Bool) (d : Data)
    (h15 : d.stacks 15 = (Filter.clauseCode C).reverse)
    (h5 : d.stacks 5 = []) (h6 : d.stacks 6 = []) (h7 : d.stacks 7 = [])
    (h8 : d.stacks 8 = []) (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = [])
    (h11 : d.stacks 11 = []) :
    ∃ t ≤ prepareCandidateBound C mask (d.stacks 20), ∃ e : Data,
      Eval (prepareCandidate mask) t d e ∧
      e.stacks = Function.update (Function.update d.stacks 15 []) 9
        (Filter.clauseCode (masked mask C)) ∧
      e.regs 4 = decide ((masked mask C).length = BinaryArithmetic.toNat (d.stacks 20)) ∧
      (∀ i : Fin 24, 13 ≤ i.val → e.regs i = d.regs i) := by
  let a : Data := ⟨readRegs d.regs 0 1 none, StackRoutines.transferStacks 15 10 d.stacks⟩
  have ha := transfer_eval 15 10 d (by decide)
  have has : a.stacks = Function.update (Function.update d.stacks 15 []) 10
      (Filter.clauseCode C) := by
    funext i
    simp [a, StackRoutines.transferStacks, h15, h10]
  have ha10 : a.stacks 10 = Filter.clauseCode C := by simp [has]
  have ha11 : a.stacks 11 = [] := by simp [has, h11]
  have ha8 : a.stacks 8 = [] := by simp [has, h8]
  have ha9 : a.stacks 9 = [] := by simp [has, h9]
  obtain ⟨t, ht, b, hb, hbs, hbr⟩ := maskCall_eval mask C a ha10 ha11 ha8 ha9
  have hbstate : b.stacks = Function.update (Function.update d.stacks 15 []) 9
      (Filter.clauseCode (masked mask C)) := by
    rw [hbs, has]
    funext i
    by_cases hi10 : i = 10
    · subst i; simp [h10]
    · simp [Function.update_apply, hi10, Filter.clauseCode]
  have hb9 : b.stacks 9 = Filter.clauseCode (masked mask C) := by simp [hbstate]
  have hb8 : b.stacks 8 = [] := by simp [hbstate, h8]
  have hb5 : b.stacks 5 = [] := by simp [hbstate, h5]
  let c : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 5 (b.stacks 9)⟩
  have hc := copy_eval 9 5 b (by decide) (by decide) (by decide) hb8 hb5
  have hc5 : c.stacks 5 = Filter.clauseCode (masked mask C) := by simp [c, hb9]
  have hc6 : c.stacks 6 = [] := by simp [c, hbstate, h6]
  have hc7 : c.stacks 7 = [] := by simp [c, hbstate, h7]
  have hc8 : c.stacks 8 = [] := by simp [c, hbstate, h8]
  have hc20 : c.stacks 20 = d.stacks 20 := by simp [c, hbstate]
  obtain ⟨u, hu, e, he, hes, hev, her⟩ := sizeCall_eval (masked mask C) c hc5 hc6 hc7 hc8
  refine ⟨3 * (d.stacks 15).length + 3 + (t + (7 * (b.stacks 9).length + 5 + u)),
    ?_, e, ha.seq (hb.seq (hc.seq he)), ?_, ?_, ?_⟩
  · rw [hc20] at hu
    simp only [h15, List.length_reverse, hb9]
    unfold prepareCandidateBound
    simp only [Filter.clauseCode] at hu ⊢
    omega
  · rw [hes]
    funext i
    by_cases hi5 : i = 5
    · subst i; simp [h5]
    · simp [c, hbstate, hi5]
  · simpa only [hc20] using hev
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i (by omega)
    have hei := her i hi
    simpa [a, c, readRegs, hi0, hi1, hbi] using hei
theorem retainCandidate_eval (d : Data) :
    ∃ t ≤ 2 * ((d.stacks 9).length + (d.stacks 12).length) + 8, ∃ e : Data,
      Eval retainCandidate t d e ∧
      e.stacks = (if d.regs 4 then d.stacks else
        Function.update (Function.update d.stacks 9 []) 12 []) ∧
      e.regs 23 = d.regs 4 ∧
      (∀ i : Fin 24, 16 ≤ i.val → i ≠ 23 → e.regs i = d.regs i) := by
  let a : Data := ⟨Function.update d.regs 23 (d.regs 4), d.stacks⟩
  have ha : Eval (atom (.copy 23 4)) 1 d a := .base (.atom _ _)
  cases hb : d.regs 4 with
  | false =>
    let b : Data := ⟨readRegs a.regs 0 1 none, Function.update a.stacks 9 []⟩
    let e : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 12 []⟩
    have hclear := (clear_eval 9 a).seq (clear_eval 12 b)
    have hbranch := Eval.ite_false (yes := (.base .skip : Code))
      (test := (23 : Fin 24)) (by simp [a, hb]) hclear
    refine ⟨1 + ((2 * (a.stacks 9).length + 3 + (2 * (b.stacks 12).length + 3)) + 1),
      ?_, e, ha.seq hbranch, ?_, ?_, ?_⟩
    · simp [a, b]
      omega
    · simp [e, b, a]
    · simp [e, b, a, readRegs, hb]
    · intro i hi hi23
      have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
      have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
      simp [e, b, a, readRegs, hi0, hi1, hi23]
  | true =>
    refine ⟨2, by omega, a, ha.seq (.ite_true (by simp [a, hb]) (.base (.skip a))), ?_, ?_, ?_⟩
    · simp [a]
    · simp [a, hb]
    · intro i _ hi
      simp [a, hi]

theorem resetCandidateFlags_eval (d : Data) :
    Eval resetCandidateFlags 2 d
      ⟨Function.update (Function.update d.regs 21 false) 22 true, d.stacks⟩ :=
  .seq (.base (.atom _ _)) (.base (.atom _ _))
theorem testedCandidate_eval (F : Formula) (C : Clause)
    (mask width size threshold : List Bool) (d : Data)
    (h15 : d.stacks 15 = (Filter.clauseCode C).reverse)
    (h16 : d.stacks 16 = width) (h17 : d.stacks 17 = threshold)
    (h18 : d.stacks 18 = Filter.formulaCode F) (h20 : d.stacks 20 = size)
    (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = [])
    (h9 : d.stacks 9 = []) (h10 : d.stacks 10 = []) (h11 : d.stacks 11 = [])
    (h12 : d.stacks 12 = []) :
    ∃ t ≤ candidateBound F C mask width size threshold, ∃ e : Data,
      Eval (testedCandidate mask) t d e ∧
      e.stacks = Function.update
        (Function.update (Function.update d.stacks 15 []) 9
          (if accepted F C mask width size threshold then
            Filter.clauseCode (masked mask C) else [])) 12
        (if accepted F C mask width size threshold then
          Filter.formulaCode (selectedFamily F (masked mask C) width) else []) ∧
      e.regs 23 = accepted F C mask width size threshold ∧
      e.regs 21 = false ∧ e.regs 22 = true := by
  obtain ⟨t, ht, a, ha, has, hav, _⟩ := prepareCandidate_eval C mask d h15
    (hwork 5) (hwork 6) (hwork 7) (hwork 8) h9 h10 h11
  rw [h20] at ht hav
  have ha9 : a.stacks 9 = Filter.clauseCode (masked mask C) := by simp [has]
  have ha10 : a.stacks 10 = [] := by simp [has, h10]
  have ha11 : a.stacks 11 = [] := by simp [has, h11]
  have ha12 : a.stacks 12 = [] := by simp [has, h12]
  have ha16 : a.stacks 16 = width := by simp [has, h16]
  have ha17 : a.stacks 17 = threshold := by simp [has, h17]
  have ha18 : a.stacks 18 = Filter.formulaCode F := by simp [has, h18]
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    have hi9 : Fin.castAdd 15 i ≠ (9 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 9 at hh; have := i.isLt; omega
    have hi15 : Fin.castAdd 15 i ≠ (15 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 15 at hh; have := i.isLt; omega
    simpa [has, hi9, hi15] using hwork i
  by_cases hsize : (masked mask C).length = BinaryArithmetic.toNat size
  · have ha4 : a.regs 4 = true := by simpa [hsize] using hav
    obtain ⟨u, hu, b, hb, hbs, hb4, _⟩ := checkCandidate_eval F (masked mask C) width a
      ha9 ha16 ha18 haw ha10 ha11 ha12
    rw [ha17] at hu hb4
    have hb9 : b.stacks 9 = Filter.clauseCode (masked mask C) := by simp [hbs, ha9]
    have hb12 : b.stacks 12 = Filter.formulaCode (selectedFamily F (masked mask C) width) := by
      simp [hbs]
    obtain ⟨v, hv, c, hc, hcs, hc23, _⟩ := retainCandidate_eval b
    let e : Data := ⟨Function.update (Function.update c.regs 21 false) 22 true, c.stacks⟩
    have he := resetCandidateFlags_eval c
    have haccept : b.regs 4 = accepted F C mask width size threshold := by
      simpa [accepted, hsize] using hb4
    refine ⟨t + ((u + v + 1) + 2), ?_, e,
      ha.seq ((Eval.ite_true ha4 (hb.seq hc)).seq he), ?_, ?_, ?_, ?_⟩
    · rw [hb9, hb12] at hv
      unfold candidateBound
      omega
    · change c.stacks = _
      rw [hcs, haccept, hbs, has]
      funext i
      cases hh : accepted F C mask width size threshold <;>
        simp [Function.update_apply]
      split_ifs <;> rfl
    · simp [e, hc23, haccept]
    · simp [e]
    · simp [e]
  · have ha4 : a.regs 4 = false := by simpa [hsize] using hav
    let b : Data := ⟨readRegs a.regs 0 1 none, Function.update a.stacks 9 []⟩
    let c : Data := ⟨Function.update b.regs 23 false, b.stacks⟩
    let e : Data := ⟨Function.update (Function.update c.regs 21 false) 22 true, c.stacks⟩
    have hb := clear_eval 9 a
    have hc : Eval (atom (.set 23 false)) 1 b c := .base (.atom _ _)
    have he := resetCandidateFlags_eval c
    refine ⟨t + ((2 * (a.stacks 9).length + 3 + 1 + 1) + 2), ?_, e,
      ha.seq ((Eval.ite_false ha4 (hb.seq hc)).seq he), ?_, ?_, ?_, ?_⟩
    · rw [ha9]
      unfold candidateBound
      omega
    · simpa [e, c, b, has, accepted, hsize] using h12
    · simp [e, c, accepted, hsize]
    · simp [e]
    · simp [e]

theorem widthFamily_eq (F : Formula) (width : List Bool) :
    widthFamily F width = (F.filter fun C => decide (C.length = BinaryArithmetic.toNat width)).reverse := by
  simp only [widthFamily, Filter.result, ExecCNF.subset, Bool.and_true]

theorem mem_widthFamily (F : Formula) (C : Clause) (width : List Bool) :
    C ∈ widthFamily F width ↔ C ∈ F ∧ C.length = BinaryArithmetic.toNat width := by
  simp [widthFamily_eq]

/-- The two streaming reversals cancel. No family is duplicated in the output. -/
theorem selectedFamily_widthFamily (F : Formula) (H : Clause) (width : List Bool) :
    selectedFamily (widthFamily F width) H width =
      selectedRaw F (BinaryArithmetic.toNat width) H := by
  simp only [selectedFamily, Filter.result, widthFamily_eq, List.filter_reverse,
    List.reverse_reverse, selectedRaw, List.filter_filter]
  congr 1
  funext C
  cases decide (C.length = BinaryArithmetic.toNat width) <;> cases ExecCNF.subset H C <;> rfl
theorem parameterInit_eval (exponent : ℕ) (size base family : List Bool) (d : Data)
    (h19 : d.stacks 19 = base) (h18 : d.stacks 18 = family)
    (h20 : d.stacks 20 = []) (h10 : d.stacks 10 = []) (h17 : d.stacks 17 = [])
    (h14 : d.stacks 14 = []) (hwork : ∀ i : Fin 9, d.stacks (Fin.castAdd 15 i) = []) :
    ∃ t ≤ parameterInitBound exponent size base family, ∃ word : List Bool, ∃ e : Data,
      Eval (parameterInit exponent size) t d e ∧
      e.stacks = Function.update (Function.update (Function.update d.stacks 20 size) 17 word) 14 family ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ exponent ∧
      word.length ≤ 1 + exponent * base.length ∧
      (∀ i : Fin 24, 8 ≤ i.val → e.regs i = d.regs i) := by
  obtain ⟨a, ha, has, har⟩ := load_eval 20 size d
  simp only [h20, List.append_nil] at has
  have ha19 : a.stacks 19 = base := by simp [has, h19]
  have ha10 : a.stacks 10 = [] := by simp [has, h10]
  have ha17 : a.stacks 17 = [] := by simp [has, h17]
  have haw (i : Fin 6) : a.stacks (Fin.castAdd 18 i) = [] := by
    have hi20 : Fin.castAdd 18 i ≠ (20 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 20 at hh; have := i.isLt; omega
    have hcast : Fin.castAdd 15 (Fin.castAdd 3 i) = Fin.castAdd 18 i := by
      apply Fin.ext
      rfl
    simpa only [has, Function.update_apply, hi20, ite_false, hcast] using
      hwork (Fin.castAdd 3 i)
  obtain ⟨t, ht, word, b, hb, hbs, hv, hl, hbr⟩ := powerCall_eval exponent base a ha19 ha10 ha17 haw
  have hb8 : b.stacks 8 = [] := by simpa [hbs, has] using hwork 8
  have hb14 : b.stacks 14 = [] := by simp [hbs, has, h14]
  have hb18 : b.stacks 18 = family := by simp [hbs, has, h18]
  let e : Data := ⟨readRegs b.regs 0 1 none, Function.update b.stacks 14 (b.stacks 18)⟩
  have he := copy_eval 18 14 b (by decide) (by decide) (by decide) hb8 hb14
  refine ⟨2 * size.length + 1 + (t + (7 * (b.stacks 18).length + 5)), ?_, word, e,
    ha.seq (hb.seq he), ?_, hv, hl, ?_⟩
  · rw [hb18]
    unfold parameterInitBound
    omega
  · simp [e, hbs, has, hb18]
  · intro i hi
    have hi0 : i ≠ 0 := by intro h; subst i; simp at hi
    have hi1 : i ≠ 1 := by intro h; subst i; simp at hi
    have hbi := hbr i hi
    have hai := har i hi
    simp [e, readRegs, hi0, hi1, hbi, hai]
theorem clearMany_eval (ports : List (Fin 24)) (bound : ℕ) (d : Data)
    (hbound : ∀ port ∈ ports, (d.stacks port).length ≤ bound) :
    ∃ t ≤ ports.length * (2 * bound + 3), ∃ e : Data,
      Eval (clearMany ports) t d e ∧ e.stacks = eraseWords ports d.stacks ∧
      (∀ i : Fin 24, i ≠ 0 → i ≠ 1 → e.regs i = d.regs i) := by
  induction ports generalizing d with
  | nil => exact ⟨0, by simp, d, .base (.skip d), by funext i; simp [eraseWords], fun _ _ _ => rfl⟩
  | cons port rest ih =>
    let a : Data := ⟨readRegs d.regs 0 1 none, Function.update d.stacks port []⟩
    have ha := clear_eval port d
    have hab (p : Fin 24) (hp : p ∈ rest) : (a.stacks p).length ≤ bound := by
      by_cases heq : p = port
      · subst p; simp [a]
      · simpa [a, heq] using hbound p (by simp [hp])
    obtain ⟨t, ht, e, he, hes, her⟩ := ih a hab
    refine ⟨2 * (d.stacks port).length + 3 + t, ?_, e, ha.seq he, ?_, ?_⟩
    · have hp := hbound port (by simp)
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega
    · rw [hes]
      funext i
      by_cases heq : i = port
      · subst i; simp [eraseWords, a]
      · by_cases hi : i ∈ rest <;> simp [eraseWords, a, hi, heq]
    · intro i hi0 hi1
      simpa [a, readRegs, hi0, hi1] using her i hi0 hi1

theorem unread_length_le (test : List Bool → Bool) (records : List (List Bool)) :
    (RecordPrograms.unread test records []).length ≤ (Encoding.encodeList id records).length := by
  induction records with
  | nil => simp [RecordPrograms.unread]
  | cons bits rest ih =>
    rw [Encoding.length_encodeList_cons]
    simp only [RecordPrograms.unread, List.append_nil]
    split <;> omega

/-- Failed callbacks restore the empty output banks. A successful callback
retains its actual output, and no further callback is required by the iterator. -/
theorem scan_callback_contract (F : Formula) (mask width size threshold : List Bool)
    (bits tail : List Bool) (base : Data)
    (hbits : ∃ C ∈ F, bits = Filter.clauseCode C)
    (hbase : ScanReady F width size threshold base) :
    ∃ t next, t ≤ scanCost F mask width size threshold bits ∧
      (scanTest F mask width size threshold bits = false → ScanReady F width size threshold next) ∧
      ScanEffect F mask width size threshold bits base next ∧
      Eval (candidate mask) t
        (RecordPrograms.state ports base false true false tail bits.reverse)
        (RecordPrograms.state ports next false true (scanTest F mask width size threshold bits) tail []) := by
  obtain ⟨C, hCF, rfl⟩ := hbits
  let d := RecordPrograms.state ports base false true false tail (Filter.clauseCode C).reverse
  have hwork (i : Fin 9) : d.stacks (Fin.castAdd 15 i) = [] := by
    have hi14 : Fin.castAdd 15 i ≠ (14 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 14 at hh; have := i.isLt; omega
    have hi15 : Fin.castAdd 15 i ≠ (15 : Fin 24) := by
      intro h; have hh := congrArg Fin.val h; change i.val = 15 at hh; have := i.isLt; omega
    have hcast : Fin.castAdd 11 (Fin.castAdd 4 i) = Fin.castAdd 15 i := by
      apply Fin.ext
      rfl
    simpa [d, RecordPrograms.state, ports, hi14, hi15, hcast] using
      hbase.scratch (Fin.castAdd 4 i)
  obtain ⟨t, ht, e, he, hes, he23, he21, he22⟩ := testedCandidate_eval F C mask width size threshold d
    (by simp [d, RecordPrograms.state, ports])
    (by simpa [d, RecordPrograms.state, ports] using hbase.width_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.threshold_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.family_word)
    (by simpa [d, RecordPrograms.state, ports] using hbase.size_word) hwork
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 9)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 10)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 11)
    (by simpa [d, RecordPrograms.state, ports] using hbase.scratch 12)
  let next : Data := ⟨e.regs, Function.update (Function.update e.stacks 14 (base.stacks 14))
    15 (base.stacks 15)⟩
  have hnext : next.stacks = Function.update (Function.update base.stacks 9
      (if accepted F C mask width size threshold then Filter.clauseCode (masked mask C) else [])) 12
      (if accepted F C mask width size threshold then
        Filter.formulaCode (selectedFamily F (masked mask C) width) else []) := by
    funext i
    simp only [next, hes, d, RecordPrograms.state, ports, Function.update_apply]
    split_ifs <;> simp_all
  have htest : scanTest F mask width size threshold (Filter.clauseCode C) =
      accepted F C mask width size threshold := by simp [scanTest]
  refine ⟨t, next, by simpa [scanCost] using ht, ?_, ⟨C, hCF, rfl, hnext⟩, ?_⟩
  · intro hfalse
    rw [htest] at hfalse
    have hs : next.stacks = base.stacks := by
      rw [hnext, hfalse]
      simp only [Bool.false_eq_true, ite_false]
      funext i
      by_cases hi9 : i = 9
      · subst i; simpa using (hbase.scratch 9).symm
      by_cases hi12 : i = 12
      · subst i; simpa using (hbase.scratch 12).symm
      simp [hi9, hi12]
    exact ⟨by simpa only [hs] using hbase.width_word,
      by simpa only [hs] using hbase.size_word,
      by simpa only [hs] using hbase.threshold_word,
      by simpa only [hs] using hbase.family_word,
      by simpa only [hs] using hbase.scratch⟩
  · have hstate : RecordPrograms.state ports next false true
        (scanTest F mask width size threshold (Filter.clauseCode C)) tail [] = e := by
      apply congrArg₂ StructuredProgram.State.mk
      · funext i
        by_cases hi21 : i = 21
        · subst i; simp [ports, he21]
        by_cases hi22 : i = 22
        · subst i; simp [ports, he22]
        by_cases hi23 : i = 23
        · subst i; simp [ports, htest, he23]
        simp [ports, next, hi21, hi22, hi23]
      · funext i
        simp only [RecordPrograms.state, ports, hnext, hes, d, Function.update_apply]
        split_ifs <;> simp_all
    simpa only [candidate, hstate] using he

theorem scan_eval (F : Formula) (mask width size threshold : List Bool) (base : Data)
    (hbase : ScanReady F width size threshold base) (v p f : Bool) :
    ∃ t next, t ≤ 3 + RecordPrograms.budget (scanCost F mask width size threshold) (Filter.records F) ∧
      ((Filter.records F).any (scanTest F mask width size threshold) = false →
        ScanReady F width size threshold next) ∧
      RecordPrograms.Visits (scanTest F mask width size threshold)
        (ScanEffect F mask width size threshold) (Filter.records F) base next ∧
      Eval (RecordPrograms.iterate ports (candidate mask)) t
        (RecordPrograms.state ports base v p f (Filter.formulaCode F) [])
        (RecordPrograms.state ports next false true
          ((Filter.records F).any (scanTest F mask width size threshold))
          (RecordPrograms.unread (scanTest F mask width size threshold) (Filter.records F) []) []) := by
  have hvalid : ∀ bits ∈ Filter.records F, ∃ C ∈ F, bits = Filter.clauseCode C := by
    intro bits hbits
    obtain ⟨C, hCF, rfl⟩ := List.mem_map.mp hbits
    exact ⟨C, hCF, rfl⟩
  simpa only [← Filter.formulaCode_records, List.append_nil] using
    RecordSearch.iterate_run_with_miss_invariant ports (candidate mask)
      (scanTest F mask width size threshold) (scanCost F mask width size threshold)
      (ScanReady F width size threshold) (ScanEffect F mask width size threshold)
      (fun bits => ∃ C ∈ F, bits = Filter.clauseCode C)
      (scan_callback_contract F mask width size threshold)
      (Filter.records F) [] base hvalid hbase v p f

theorem ScanEffect.frame {F : Formula} {mask width size threshold bits : List Bool}
    {before after : Data} (h : ScanEffect F mask width size threshold bits before after)
    (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : after.stacks i = before.stacks i := by
  obtain ⟨C, _, _, hs⟩ := h.shape
  simp [hs, hi9, hi12]

theorem scan_visits_frame {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : after.stacks i = before.stacks i := by
  induction h with
  | nil base => rfl
  | hit _ he => exact he.frame i hi9 hi12
  | miss _ he _ ih => exact ih.trans (he.frame i hi9 hi12)

theorem scan_visits_hit {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (hfound : records.any (scanTest F mask width size threshold) = true) :
    ∃ C ∈ F, accepted F C mask width size threshold = true ∧
      after.stacks 9 = Filter.clauseCode (masked mask C) ∧
      after.stacks 12 = Filter.formulaCode (selectedFamily F (masked mask C) width) := by
  induction h with
  | nil base => simp at hfound
  | hit ht he =>
    obtain ⟨C, hCF, rfl, hs⟩ := he.shape
    have htrue : accepted F C mask width size threshold = true := by simpa [scanTest] using ht
    exact ⟨C, hCF, htrue, by simp [hs, htrue], by simp [hs, htrue]⟩
  | miss ht _ _ ih => exact ih (by simpa [List.any_cons, ht] using hfound)

theorem scan_visits_miss {F : Formula} {mask width size threshold : List Bool}
    {records : List (List Bool)} {before after : Data}
    (h : RecordPrograms.Visits (scanTest F mask width size threshold)
      (ScanEffect F mask width size threshold) records before after)
    (hfound : records.any (scanTest F mask width size threshold) = false)
    (h9 : before.stacks 9 = []) (h12 : before.stacks 12 = []) :
    after.stacks = before.stacks := by
  induction h with
  | nil base => rfl
  | hit ht _ => simp [List.any_cons, ht] at hfound
  | @miss bits rest base middle next ht he _ ih =>
    obtain ⟨C, _, rfl, hs⟩ := he.shape
    have hfalse : accepted F C mask width size threshold = false := by simpa [scanTest] using ht
    have heq : _ = _ := hs
    rw [hfalse] at heq
    simp only [Bool.false_eq_true, ite_false] at heq
    have h9update : Function.update base.stacks 9 [] = base.stacks := by
      rw [← h9, Function.update_eq_self]
    have h12update : Function.update base.stacks 12 [] = base.stacks := by
      rw [← h12, Function.update_eq_self]
    rw [h9update, h12update] at heq
    exact (ih (by simpa [List.any_cons, ht] using hfound)
      (by simpa only [heq] using h9) (by simpa only [heq] using h12)).trans heq

theorem scan_any_eq (F : Formula) (mask width size threshold : List Bool) :
    (Filter.records F).any (scanTest F mask width size threshold) =
      F.any (fun C => accepted F C mask width size threshold) := by
  simp [Filter.records, List.any_map, Function.comp_def, scanTest]

theorem clauseCode_masked_length_le (mask : List Bool) (C : Clause) :
    (Filter.clauseCode (masked mask C)).length ≤ (Filter.clauseCode C).length :=
  EncodingLength.length_le_of_sublist id (masked_sublist mask C)

theorem formulaCode_selectedFamily_length_le (F : Formula) (H : Clause) (width : List Bool) :
    (Filter.formulaCode (selectedFamily F H width)).length ≤ (Filter.formulaCode F).length := by
  unfold selectedFamily Filter.formulaCode
  rw [EncodingLength.length_reverse]
  exact EncodingLength.length_le_of_sublist Filter.clauseCode List.filter_sublist

theorem clauseCode_member_length_le (F : Formula) (C : Clause) (h : C ∈ F) :
    (Filter.clauseCode C).length ≤ (Filter.formulaCode F).length := by
  have hh := Filter.member_length_le (Filter.records F) (Filter.clauseCode C)
    (List.mem_map.mpr ⟨C, h, rfl⟩)
  simpa only [← Filter.formulaCode_records] using hh

theorem candidateBound_le (F : Formula) (C : Clause) (mask width size threshold : List Bool)
    (hC : C ∈ F) :
    candidateBound F C mask width size threshold ≤ 2000 * scanVolume F mask width size threshold ^ 3 := by
  let L := scanVolume F mask width size threshold
  have hCsize := clauseCode_member_length_le F C hC
  have hHsize := clauseCode_masked_length_le mask C
  have hSsize := formulaCode_selectedFamily_length_le F (masked mask C) width
  have hL : 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hH : (Filter.clauseCode (masked mask C)).length + size.length + 1 ≤ L := by
    dsimp [L, scanVolume]; omega
  have hF : (Filter.clauseCode (masked mask C)).length + (Filter.formulaCode F).length +
      width.length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hS : (Filter.formulaCode (selectedFamily F (masked mask C) width)).length +
      threshold.length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hHpow := Nat.pow_le_pow_left hH 2
  have hFpow := Nat.pow_le_pow_left hF 3
  have hSpow := Nat.pow_le_pow_left hS 2
  have hsq : L ^ 2 ≤ L ^ 3 := pow_le_pow_right₀ hL (by decide)
  have hlin : L ≤ L ^ 3 := Nat.le_self_pow (by decide) L
  have hsmall : (Filter.formulaCode F).length + mask.length + 1 ≤ L := by
    dsimp [L, scanVolume]; omega
  unfold candidateBound prepareCandidateBound checkCandidateBound CoreMaskProgram.runtimeBound
  change _ ≤ 2000 * L ^ 3
  dsimp only [Filter.clauseCode] at *
  omega

theorem scan_budget_le (F : Formula) (mask width size threshold : List Bool) :
    3 + RecordPrograms.budget (scanCost F mask width size threshold) (Filter.records F) ≤
      3000 * scanVolume F mask width size threshold ^ 4 := by
  let L := scanVolume F mask width size threshold
  have hcost (bits : List Bool) (hbits : bits ∈ Filter.records F) :
      scanCost F mask width size threshold bits ≤ 0 * bits.length + 2000 * L ^ 3 := by
    obtain ⟨C, hCF, rfl⟩ := List.mem_map.mp hbits
    simpa only [scanCost, Filter.decodeClause_clauseCode, Nat.zero_mul, Nat.zero_add] using
      candidateBound_le F C mask width size threshold hCF
  have hb := RecordPrograms.program_budget_le_input
    (scanCost F mask width size threshold) (Filter.records F) 0 (2000 * L ^ 3) hcost
  have hcode : ProgramEncoding.encodeRecords (Filter.records F) = Filter.formulaCode F := by
    exact (Filter.formulaCode_records F).symm
  rw [hcode] at hb
  simp only [Nat.zero_add] at hb
  have hL : 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hlen : (Filter.formulaCode F).length + 1 ≤ L := by dsimp [L, scanVolume]; omega
  have hmul := Nat.mul_le_mul_left (2000 * L ^ 3 + 17) hlen
  have hlin : L ≤ L ^ 4 := Nat.le_self_pow (by decide) L
  have heq : (2000 * L ^ 3 + 17) * L = 2000 * L ^ 4 + 17 * L := by ring
  rw [heq] at hmul
  change _ ≤ 3000 * L ^ 4
  omega

theorem phase_eval (F : Formula) (base : List Bool) (c h : ℕ) (mask : List Bool)
    (d : Data) (hd : Boundary F base d) :
    ∃ word : List Bool, ∃ t ≤ phaseBound F base c h mask, ∃ e : Data,
      Eval (phase c h mask) t d e ∧
      BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ (c - h) ∧
      word.length ≤ 1 + (c - h) * base.length ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = (widthFamily F c.bits).any
        (fun C => accepted (widthFamily F c.bits) C mask c.bits h.bits word) ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → ∃ C ∈ widthFamily F c.bits,
        accepted (widthFamily F c.bits) C mask c.bits h.bits word = true ∧
        e.stacks 9 = Filter.clauseCode (masked mask C) ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c (masked mask C))) := by
  let Fc := widthFamily F c.bits
  have hw (i : Fin 9) : d.stacks (Fin.castAdd 15 i) = [] := by
    apply hd.scratch
    · intro heq; have hh := congrArg Fin.val heq; change i.val = 13 at hh; have := i.isLt; omega
    · intro heq; have hh := congrArg Fin.val heq; change i.val = 19 at hh; have := i.isLt; omega
  obtain ⟨u, hu, a, ha, has, _⟩ := familyInit_eval F c.bits d hd.formula_word hw
    (hd.scratch 9 (by decide) (by decide)) (hd.scratch 10 (by decide) (by decide))
    (hd.scratch 11 (by decide) (by decide)) (hd.scratch 12 (by decide) (by decide))
    (hd.scratch 16 (by decide) (by decide)) (hd.scratch 18 (by decide) (by decide))
  have haw (i : Fin 9) : a.stacks (Fin.castAdd 15 i) = [] := by
    rw [has, update_high_apply_low _ 18 _ i (by decide),
      update_high_apply_low _ 16 _ i (by decide)]
    exact hw i
  obtain ⟨v, hv, word, b, hb, hbs, hval, hlen, _⟩ := parameterInit_eval (c - h) h.bits base
    (Filter.formulaCode Fc) a
    (by simp [has, hd.parameter_word]) (by simp [has, Fc])
    (by simpa [has] using hd.scratch 20 (by decide) (by decide))
    (by simpa [has] using hd.scratch 10 (by decide) (by decide))
    (by simpa [has] using hd.scratch 17 (by decide) (by decide))
    (by simpa [has] using hd.scratch 14 (by decide) (by decide)) haw
  have hready : ScanReady Fc c.bits h.bits word b := by
    constructor
    · simp [hbs, has]
    · simp [hbs]
    · simp [hbs]
    · simp [hbs, has, Fc]
    · intro i
      have hi14 : Fin.castAdd 11 i ≠ (14 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 14 at hh; have := i.isLt; omega
      have hi17 : Fin.castAdd 11 i ≠ (17 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 17 at hh; have := i.isLt; omega
      have hi20 : Fin.castAdd 11 i ≠ (20 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 20 at hh; have := i.isLt; omega
      have hi18 : Fin.castAdd 11 i ≠ (18 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 18 at hh; have := i.isLt; omega
      have hi16 : Fin.castAdd 11 i ≠ (16 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 16 at hh; have := i.isLt; omega
      have hi13 : Fin.castAdd 11 i ≠ (13 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 13 at hh; have := i.isLt; omega
      have hi19 : Fin.castAdd 11 i ≠ (19 : Fin 24) := by
        intro he; have hh := congrArg Fin.val he; change i.val = 19 at hh; have := i.isLt; omega
      simpa [hbs, has, hi14, hi17, hi20, hi18, hi16] using hd.scratch _ hi13 hi19
  obtain ⟨w, next, hwtime, hmiss, hvisits, hscan⟩ := scan_eval Fc mask c.bits h.bits word b
    hready (b.regs 21) (b.regs 22) (b.regs 23)
  have hstart : RecordPrograms.state ports b (b.regs 21) (b.regs 22) (b.regs 23)
      (Filter.formulaCode Fc) [] = b := by
    apply RecordPrograms.state_eq_self
    · rfl
    · rfl
    · rfl
    · simp [ports, hbs]
    · simpa [ports, hbs, has] using hd.scratch 15 (by decide) (by decide)
  rw [hstart] at hscan
  let test := scanTest Fc mask c.bits h.bits word
  let found := (Filter.records Fc).any test
  let z := RecordPrograms.state ports next false true found
    (RecordPrograms.unread test (Filter.records Fc) []) []
  change Eval (RecordPrograms.iterate ports (candidate mask)) w b z at hscan
  have hframe := scan_visits_frame hvisits
  let L := phaseVolume F base c h mask
  have hvolume : scanVolume Fc mask c.bits h.bits word ≤ L := by
    dsimp [scanVolume, L, phaseVolume, Fc]
    omega
  have hwbound : w ≤ 3000 * L ^ 4 :=
    hwtime.trans ((scan_budget_le Fc mask c.bits h.bits word).trans
      (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left hvolume 4)))
  have hzbound (i : Fin 24) (hi : i ∈ ([14, 18, 16, 20, 17] : List (Fin 24))) :
      (z.stacks i).length ≤ L := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl
    · have hh := unread_length_le test (Filter.records Fc)
      rw [← Filter.formulaCode_records] at hh
      change (RecordPrograms.unread test (Filter.records Fc) []).length ≤ L
      dsimp [L, phaseVolume, Fc] at *
      omega
    all_goals simp only [z, RecordPrograms.state, ports, Function.update_apply]
    all_goals rw [hframe _ (by decide) (by decide)]
    all_goals simp only [hbs, has, Function.update_apply]
    all_goals norm_num
    all_goals dsimp [L, phaseVolume, Fc] at *; omega
  obtain ⟨x, hx, e, he, hes, her⟩ := clearMany_eval [14, 18, 16, 20, 17] L z hzbound
  have hef (i : Fin 24) (hi9 : i ≠ 9) (hi12 : i ≠ 12) : e.stacks i = d.stacks i := by
    rw [hes]
    by_cases hi : i ∈ ([14, 18, 16, 20, 17] : List (Fin 24))
    · simp only [eraseWords, hi, ite_true, if_true]
      symm
      apply hd.scratch
      · intro h; subst i; simp at hi
      · intro h; subst i; simp at hi
    · have hi14 : i ≠ 14 := by intro h; subst i; simp at hi
      have hi18 : i ≠ 18 := by intro h; subst i; simp at hi
      have hi16 : i ≠ 16 := by intro h; subst i; simp at hi
      have hi20 : i ≠ 20 := by intro h; subst i; simp at hi
      have hi17 : i ≠ 17 := by intro h; subst i; simp at hi
      by_cases hi15 : i = 15
      · subst i
        simpa [eraseWords, z, RecordPrograms.state, ports] using
          (hd.scratch 15 (by decide) (by decide)).symm
      · simp only [eraseWords, hi, ite_false, z, RecordPrograms.state, ports,
          Function.update_apply, hi14, hi15, ite_false]
        rw [hframe i hi9 hi12]
        simp [hbs, has, hi14, hi18, hi16, hi20, hi17]
  have he9 : e.stacks 9 = next.stacks 9 := by simp [hes, eraseWords, z, RecordPrograms.state, ports]
  have he12 : e.stacks 12 = next.stacks 12 := by simp [hes, eraseWords, z, RecordPrograms.state, ports]
  have he23 : e.regs 23 = found := by
    simpa [z, RecordPrograms.state, ports] using her 23 (by decide) (by decide)
  refine ⟨word, u + (v + (w + x)), ?_, e, ha.seq (hb.seq (hscan.seq he)),
    hval, hlen, hef, ?_, ?_, ?_⟩
  · simp only [List.length_cons, List.length_nil] at hx
    unfold phaseBound
    dsimp [Fc] at hv
    dsimp [L] at hwbound hx
    omega
  · exact he23.trans (scan_any_eq Fc mask c.bits h.bits word)
  · intro hfalse
    have hn := scan_visits_miss hvisits (he23.symm.trans hfalse)
      (hready.scratch 9) (hready.scratch 12)
    funext i
    by_cases hi9 : i = 9
    · subst i; rw [he9, hn]; simp [hbs, has]
    by_cases hi12 : i = 12
    · subst i; rw [he12, hn]; simp [hbs, has]
    exact hef i hi9 hi12
  · intro htrue
    obtain ⟨C, hCF, hacc, h9, h12⟩ := scan_visits_hit hvisits (he23.symm.trans htrue)
    refine ⟨C, hCF, hacc, he9.trans h9, ?_⟩
    simpa only [ArithmeticExpressionSupport.bits_value] using
      he12.trans (h12.trans (congrArg Filter.formulaCode (selectedFamily_widthFamily F (masked mask C) c.bits)))

theorem accepted_eq_passCandidate (F : Formula) (base word : List Bool) (c h : ℕ)
    (mask : List Bool) (hword : BinaryArithmetic.toNat word = BinaryArithmetic.toNat base ^ (c - h))
    (C : Clause) :
    accepted (widthFamily F c.bits) C mask c.bits h.bits word =
      passCandidate F (BinaryArithmetic.toNat base) (c, h, mask) C := by
  have hcount := congrArg List.length (selectedFamily_widthFamily F (masked mask C) c.bits)
  simp only [selectedFamily, List.length_reverse, ArithmeticExpressionSupport.bits_value] at hcount
  simp only [accepted, ArithmeticExpressionSupport.bits_value, hword, hcount, passCandidate]

theorem phase_eval_natural (F : Formula) (base : List Bool) (p : ℕ × ℕ × List Bool)
    (d : Data) (hd : Boundary F base d) :
    ∃ t ≤ phaseBound F base p.1 p.2.1 p.2.2, ∃ e : Data,
      Eval (phase p.1 p.2.1 p.2.2) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = passFound F (BinaryArithmetic.toNat base) p ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → ∃ C ∈ widthFamily F p.1.bits,
        passCandidate F (BinaryArithmetic.toNat base) p C = true ∧
        e.stacks 9 = Filter.clauseCode (masked p.2.2 C) ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F p.1 (masked p.2.2 C))) := by
  obtain ⟨word, t, ht, e, he, hval, _, hframe, hfound, hmiss, hhit⟩ :=
    phase_eval F base p.1 p.2.1 p.2.2 d hd
  have hh (C : Clause) := accepted_eq_passCandidate F base word p.1 p.2.1 p.2.2 hval C
  refine ⟨t, ht, e, he, hframe, ?_, hmiss, ?_⟩
  · simpa only [hh, passFound] using hfound
  · intro htrue
    obtain ⟨C, hC, hacc, hs9, hs12⟩ := hhit htrue
    exact ⟨C, hC, (hh C).symm.trans hacc, hs9, hs12⟩

theorem chain_stop (commands : List Code) (d : Data) (hfound : d.regs 23 = true) :
    ∃ t ≤ 1, Eval (chain commands) t d d := by
  cases commands with
  | nil => exact ⟨0, by decide, .base (.skip d)⟩
  | cons head tail => exact ⟨1, by decide, .ite_true hfound (.base (.skip d))⟩

theorem chain_eval (F : Formula) (base : List Bool) (ps : List (ℕ × ℕ × List Bool))
    (d : Data) (hd : Boundary F base d) (hfalse : d.regs 23 = false) :
    ∃ t ≤ chainBudget F base ps, ∃ e : Data,
      Eval (chain (ps.map fun p => phase p.1 p.2.1 p.2.2)) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      e.regs 23 = ps.any (passFound F (BinaryArithmetic.toNat base)) ∧
      (e.regs 23 = false → e.stacks = d.stacks) ∧
      (e.regs 23 = true → SearchHit F (BinaryArithmetic.toNat base) ps e) := by
  induction ps generalizing d with
  | nil =>
    refine ⟨0, by simp [chainBudget], d, .base (.skip d), fun _ _ _ => rfl, ?_,
      fun _ => rfl, ?_⟩
    · simpa using hfalse
    · intro hh; simp [hfalse] at hh
  | cons p ps ih =>
    obtain ⟨u, hu, a, ha, haframe, hafound, hamiss, hahit⟩ := phase_eval_natural F base p d hd
    cases hh : a.regs 23 with
    | false =>
      have has := hamiss hh
      have haBoundary : Boundary F base a := by
        constructor
        · simpa only [has] using hd.formula_word
        · simpa only [has] using hd.parameter_word
        · simpa only [has] using hd.scratch
      obtain ⟨v, hv, e, he, heframe, hefound, hemiss, hehit⟩ := ih a haBoundary hh
      refine ⟨u + v + 1, ?_, e, Eval.ite_false hfalse (ha.seq he), ?_, ?_, ?_, ?_⟩
      · simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons] at *
        omega
      · intro i hi9 hi12
        exact (heframe i hi9 hi12).trans (haframe i hi9 hi12)
      · simp only [List.any_cons, ← hafound, hh, Bool.false_or]
        exact hefound
      · intro hf
        exact (hemiss hf).trans has
      · intro ht
        obtain ⟨before, chosen, after, C, hsplit, hfailed, hC, hacc, h9, h12⟩ := hehit ht
        refine ⟨p :: before, chosen, after, C, ?_, ?_, hC, hacc, h9, h12⟩
        · simp only [List.cons_append, hsplit]
        · intro q hq
          rcases List.mem_cons.mp hq with heq | hrest
          · subst q; exact hafound.symm.trans hh
          · exact hfailed q hrest
    | true =>
      obtain ⟨v, hv, he⟩ := chain_stop (ps.map fun p => phase p.1 p.2.1 p.2.2) a hh
      obtain ⟨C, hC, hacc, h9, h12⟩ := hahit hh
      refine ⟨u + v + 1, ?_, a, Eval.ite_false hfalse (ha.seq he), haframe, ?_, ?_, ?_⟩
      · simp only [chainBudget, List.map_cons, List.sum_cons, List.length_cons]
        omega
      · simp [List.any_cons, ← hafound, hh]
      · intro hf; simp [hh] at hf
      · intro _
        exact ⟨[], p, ps, C, rfl, by simp, hC, hacc, h9, h12⟩

theorem rawCandidate_witness {α : Type*} (k : ℕ) (F : List (List α)) (c : ℕ) (H : List α)
    (h : (c, H) ∈ rawCandidates k F) :
    ∃ C ∈ F, ∃ mask, mask.length = k ∧ C.length = c ∧ masked mask C = H := by
  obtain ⟨C, hCF, hC⟩ := List.mem_flatMap.mp h
  obtain ⟨mask, hm, heq⟩ := List.mem_map.mp hC
  obtain ⟨hc, hH⟩ := Prod.mk.inj heq
  exact ⟨C, hCF, mask, (mem_masks mask k).mp hm, hc, hH⟩

theorem rawCandidate_failure (k : ℕ) (F : Formula) (M c : ℕ) (H : Clause)
    (hraw : (c, H) ∈ rawCandidates k F)
    (hfail : ∀ mask, mask.length = k → passFound F M (c, H.length, mask) = false) :
    (selectedRaw F c H).length < M ^ (c - H.length) := by
  obtain ⟨C, hCF, mask, hm, hc, hH⟩ := rawCandidate_witness k F c H hraw
  have hmem : C ∈ widthFamily F c.bits := by
    rw [mem_widthFamily]
    simpa only [ArithmeticExpressionSupport.bits_value] using And.intro hCF hc
  have hn := List.any_eq_false.mp (hfail mask hm) C hmem
  simpa [passCandidate, hH, Nat.not_le] using hn

theorem SearchHit.priority (k : ℕ) (F : Formula) (M : ℕ) (e : Data)
    (hwidth : ∀ C ∈ F, C.length ≤ k) (hit : SearchHit F M (passes k) e) :
    ∃ c H, RawPriority k F M c H ∧ e.stacks 9 = Filter.clauseCode H ∧
      e.stacks 12 = Filter.formulaCode (selectedRaw F c H) := by
  obtain ⟨before, ⟨c, h, mask⟩, after, C, hsplit, hfailed, hC, hacc, h9, h12⟩ := hit
  have hp : (c, h, mask) ∈ passes k := by rw [hsplit]; simp
  obtain ⟨hc2, hck, hhpos, hhproper, hmask⟩ := (mem_passes k c h mask).mp hp
  have hCF : C ∈ F ∧ C.length = c := by
    simpa only [mem_widthFamily, ArithmeticExpressionSupport.bits_value] using hC
  have hparts : (masked mask C).length = h ∧
      M ^ (c - h) ≤ (selectedRaw F c (masked mask C)).length := by
    simpa only [passCandidate, Bool.and_eq_true, decide_eq_true_eq] using hacc
  refine ⟨c, masked mask C, ?_, h9, h12⟩
  constructor
  · apply List.mem_flatMap.mpr
    refine ⟨C, hCF.1, List.mem_map.mpr ⟨mask, (mem_masks mask k).mpr hmask, ?_⟩⟩
    simp [hCF.2]
  · omega
  · omega
  · simpa only [hparts.1] using hparts.2
  · intro d core hraw hpos hproper hdc
    have hdwidth : d ≤ k := by
      obtain ⟨D, hD, hlen, _⟩ := rawCandidate_spec k F d core hraw
      rw [← hlen]
      exact hwidth D hD
    apply rawCandidate_failure k F M d core hraw
    intro other hother
    have hpm : (d, core.length, other) ∈ passes k :=
      (mem_passes k d core.length other).mpr ⟨by omega, hdwidth, hpos, hproper, hother⟩
    exact hfailed _ (higher_priority_mem_before hsplit hpm (Or.inl hdc))
  · intro core hraw hlarge hproper
    apply rawCandidate_failure k F M c core hraw
    intro other hother
    have hpm : (c, core.length, other) ∈ passes k :=
      (mem_passes k c core.length other).mpr ⟨hc2, hck, by omega, hproper, hother⟩
    exact hfailed _ (higher_priority_mem_before hsplit hpm (Or.inr ⟨rfl, by change h < core.length; omega⟩))

theorem passes_failure (k : ℕ) (F : Formula) (M : ℕ)
    (hwidth : ∀ C ∈ F, C.length ≤ k)
    (hfail : (passes k).any (passFound F M) = false)
    (c : ℕ) (H : Clause) (hraw : (c, H) ∈ rawCandidates k F)
    (hpos : 0 < H.length) (hproper : H.length < c) :
    (selectedRaw F c H).length < M ^ (c - H.length) := by
  have hcwidth : c ≤ k := by
    obtain ⟨C, hC, hc, _⟩ := rawCandidate_spec k F c H hraw
    rw [← hc]
    exact hwidth C hC
  apply rawCandidate_failure k F M c H hraw
  intro mask hmask
  have hm : (c, H.length, mask) ∈ passes k :=
    (mem_passes k c H.length mask).mpr ⟨by omega, hcwidth, hpos, hproper, hmask⟩
  simpa only [Bool.not_eq_true] using List.any_eq_false.mp hfail _ hm

theorem command_eval_oai (k : ℕ) (F : Formula) (base : List Bool) (d : Data)
    (hd : Boundary F base d) (hwidth : ∀ C ∈ F, C.length ≤ k) :
    ∃ t ≤ 1 + chainBudget F base (passes k), ∃ e : Data,
      Eval (command k) t d e ∧
      (∀ i : Fin 24, i ≠ 9 → i ≠ 12 → e.stacks i = d.stacks i) ∧
      (e.regs 23 = false → e.stacks = d.stacks ∧
        ∀ c H, (c, H) ∈ rawCandidates k F → 0 < H.length → H.length < c →
          (selectedRaw F c H).length < BinaryArithmetic.toNat base ^ (c - H.length)) ∧
      (e.regs 23 = true → ∃ c H, RawPriority k F (BinaryArithmetic.toNat base) c H ∧
        e.stacks 9 = Filter.clauseCode H ∧
        e.stacks 12 = Filter.formulaCode (selectedRaw F c H)) := by
  let a : Data := ⟨Function.update d.regs 23 false, d.stacks⟩
  have ha : Eval (atom (.set 23 false)) 1 d a := .base (.atom _ _)
  obtain ⟨t, ht, e, he, hframe, hfound, hmiss, hhit⟩ := chain_eval F base (passes k) a
      ⟨hd.formula_word, hd.parameter_word, hd.scratch⟩ (by simp [a])
  refine ⟨1 + t, by omega, e, ha.seq he, hframe, ?_, ?_⟩
  · intro hf
    refine ⟨hmiss hf, ?_⟩
    exact passes_failure k F (BinaryArithmetic.toNat base) hwidth (hfound.symm.trans hf)
  · intro hf
    exact (hhit hf).priority k F (BinaryArithmetic.toNat base) e hwidth

end Selector

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.DisjointReuse.SparsePriorityProgram.Selector.command_eval_oai
