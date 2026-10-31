-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:49:54.946573+00:00
-- url     : https://prove2.me/submissions/9783b94e-36f0-4d37-adac-d62dcaac4781

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S081
import Definitions.Def_OAIQ081S153

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

end SubexponentialSAT.CoreMaskProgram

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpIncidenceSlotProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical local-slot query

The three preserved inputs are the encoded scope family and unary factor and
vertex indices. A real mask pass selects the preceding factors, and the checked
incidence scan counts them. No slot map or selected prefix is supplied as input.
-/

namespace SubexponentialSAT.SubexpIncidenceSlotProgram

open BitProgram StructuredCalls

theorem encode_map (scopes : List (List ℕ)) :
    Encoding.encodeList id (scopes.map scopeBytes) = scopeBits scopes := by
  induction scopes with
  | nil => rfl
  | cons C Cs ih =>
      simpa [scopeBits, Encoding.encodeList] using
        congrArg (fun tail => true :: (Encoding.frame (scopeBytes C) ++ tail)) ih

theorem select_prefix (records : List (List Bool)) (e : ℕ) :
    CoreMaskProgram.select (unary e) records = records.take e := by
  induction records generalizing e with
  | nil => simp [CoreMaskProgram.select]
  | cons x xs ih =>
      cases e with
      | zero => simpa [CoreMaskProgram.select, unary] using ih 0
      | succ e => simp [CoreMaskProgram.select, unary, List.replicate_succ, ih]

theorem copy_eval (src dst : Fin 13) (a : Data)
    (hsd : src ≠ dst) (hs : src ≠ 8) (hd : (8 : Fin 13) ≠ dst) (ht : a.stacks 8 = []) :
    Eval (copy src dst) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst 8 0 1 hsd hs hd (by decide) a.regs a.stacks ht)

theorem push_eval (dst : Fin 13) (bit : Bool) (a : Data) :
    Eval (push dst bit) 2 a (pushed dst bit a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) bit) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [push, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

theorem prepare_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval prepare (7 * (scopeBits scopes).length + 7 * e + 10)
      (idle regs scopes e v []) (seeded rf scopes e v) := by
  let a := idle regs scopes e v []
  let b := copied 0 4 a
  let c := copied 1 5 b
  have h1 := copy_eval 0 4 a (by decide) (by decide) (by decide) rfl
  have h2 := copy_eval 1 5 b (by decide) (by decide) (by decide) rfl
  have hc : c = seeded c.regs scopes e v := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;> simp [ b, copied, a, idle, data, StackRoutines.copyStacks]
  refine ⟨c.regs, ?_⟩
  have h := h1.seq h2
  change Eval prepare _ a c at h
  rw [hc] at h
  have hlen0 : (a.stacks 0).length = (scopeBits scopes).length := rfl
  have hlen1 : (b.stacks 1).length = e := by
    change (List.replicate e true).length = e
    exact List.length_replicate
  have hcost : (7 * (scopeBits scopes).length + 5) + (7 * e + 5) =
      7 * (scopeBits scopes).length + 7 * e + 10 := by omega
  simpa only [hlen0, hlen1, hcost] using h

theorem maskReg_injective : Function.Injective maskReg := Fin.castAdd_injective _ _
theorem maskPort_injective : Function.Injective maskPort := by decide

theorem mask_project (regs : Fin 10 → Bool) (source index vertex : List Bool) :
    projectState maskReg maskPort
      (data regs source index vertex [] source index [] [] [] [] [] [] []) =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3) source index [] [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  · first | done | (first | done | (funext i; fin_cases i <;> rfl))

theorem mask_embed (regs : Fin 10 → Bool) (source index vertex output : List Bool) :
    embedState maskReg maskPort
      (data regs source index vertex [] source index [] [] [] [] [] [] [])
      (CoreMaskProgram.state false false false false [] [] [] output) =
      data (maskResultRegs regs) source index vertex [] [] [] [] output [] [] [] [] [] := by
  apply embedState_eq_of_ports maskReg maskPort _ _ _ maskReg_injective maskPort_injective
  · intro i
    change Function.extend maskReg (fun _ => false) regs (maskReg i) = _
    rw [maskReg_injective.extend_apply]
    fin_cases i <;> rfl
  · intro i hi
    change Function.extend maskReg (fun _ => false) regs i = regs i
    exact Function.extend_apply' _ _ _ hi
  · intro i; fin_cases i <;> rfl
  · intro i hi
    have h4 : i ≠ 4 := fun h => hi ⟨0, h.symm⟩
    have h5 : i ≠ 5 := fun h => hi ⟨1, h.symm⟩
    have h6 : i ≠ 6 := fun h => hi ⟨2, h.symm⟩
    have h7 : i ≠ 7 := fun h => hi ⟨3, h.symm⟩
    simp only [ ite_eq_right h4, ite_eq_right h5, ite_eq_right h6, ite_eq_right h7]

theorem select_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ)
    (he : e ≤ scopes.length) :
    ∃ n rf, n ≤ 10 * (scopeBits scopes).length + 10 ∧
      Eval selectPrefix n (seeded regs scopes e v) (selected rf scopes e v) := by
  let a := seeded regs scopes e v
  let b := CoreMaskProgram.state false false false false [] [] [] (scopeBits (scopes.take e))
  have hp : projectState maskReg maskPort a =
      CoreMaskProgram.state (regs 0) (regs 1) (regs 2) (regs 3)
        (Encoding.encodeList id (scopes.map scopeBytes) ++ []) (unary e) [] [] := by
    simpa only [a, seeded, data, encode_map, List.append_nil] using
      mask_project regs (scopeBits scopes) (unary e) (unary v)
  obtain ⟨n, hn, hr⟩ := CoreMaskProgram.run_correct (scopes.map scopeBytes) [] (unary e)
    (regs 0) (regs 1) (regs 2) (regs 3)
  have hb : CoreMaskProgram.state false false false false []
      ((unary e).drop (scopes.map scopeBytes).length) []
      (Encoding.encodeList id (CoreMaskProgram.select (unary e) (scopes.map scopeBytes))) = b := by
    simp [b, select_prefix, ← List.map_take, encode_map, unary, List.drop_replicate,
      Nat.sub_eq_zero_of_le he]
  rw [hb, ← hp] at hr
  have h := eval_call_from_state CoreMaskProgram.program maskReg maskPort a
    maskReg_injective maskPort_injective hr
  have hc : embedState maskReg maskPort a b =
      selected (maskResultRegs regs) scopes e v :=
    mask_embed regs (scopeBits scopes) (unary e) (unary v) (scopeBits (scopes.take e))
  refine ⟨n, maskResultRegs regs, ?_, ?_⟩
  · simpa [CoreMaskProgram.runtimeBound, encode_map] using hn
  · change Eval selectPrefix n a (embedState maskReg maskPort a b) at h
    rw [hc] at h
    exact h

theorem query_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval makeQuery (7 * v + 7) (selected regs scopes e v) (ready rf scopes e v) := by
  let a := selected regs scopes e v
  let b := copied 2 6 a
  let c := pushed 6 false b
  have h1 := copy_eval 2 6 a (by decide) (by decide) (by decide) rfl
  have h2 := push_eval 6 false b
  have hc : c = ready c.regs scopes e v := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    fin_cases i <;>
      simp [ b, copied, a, selected, data, StackRoutines.copyStacks,
        Encoding.encodeNat, List.reverse_append]
  have h := h1.seq h2
  change Eval makeQuery _ a c at h
  rw [hc] at h
  have hlen : (a.stacks 2).length = v := by
    change (List.replicate v true).length = v
    exact List.length_replicate
  have hcost : (7 * v + 5) + 2 = 7 * v + 7 := by omega
  exact ⟨c.regs, by simpa only [hlen, hcost] using h⟩

theorem scanPort_injective : Function.Injective scanPort := by decide

theorem scan_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ n rf, n ≤ 4 + SubexpIncidencePlanScan.scanBudget v 0 (scopes.take e) ∧
      Eval scan n (ready regs scopes e v) (scanned rf scopes e v) := by
  let a := ready regs scopes e v
  obtain ⟨n, rf, hr, _, _, _, hn⟩ :=
    SubexpIncidencePlanScan.command_eval (scopes.take e) regs v 0 0 [] []
  have hp : projectState id scanPort a =
      SubexpIncidencePlanScan.data regs v 0 (scopeBits (scopes.take e) ++ []) [] [] 0 := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · funext i; fin_cases i <;> simp [ scanPort, a, ready, data
        ]
  change Eval SubexpIncidencePlanScan.command n
    (SubexpIncidencePlanScan.data regs v 0 (scopeBits (scopes.take e) ++ []) [] [] 0) _ at hr
  rw [← hp] at hr
  have h := eval_liftCommand_from_state SubexpIncidencePlanScan.command 6 9 id scanPort a
    Function.injective_id scanPort_injective hr
  have hc : embedState id scanPort a
      (SubexpIncidencePlanScan.data rf v (0 + (scopes.take e).length) []
        (SubexpIncidencePlanScan.indexPrefix
          (Subexp.IncidencePlanSpec.incidenceFrom v 0 (scopes.take e)).reverse ++ []) []
        (0 + degree scopes e v)) = scanned rf scopes e v := by
    apply embedState_eq_of_ports id scanPort a _ _ Function.injective_id scanPort_injective
    · intro i; rfl
    · intro i hi; exact False.elim (hi ⟨i, rfl⟩)
    · intro i; fin_cases i <;> simp [scanPort, scanned, data,
        SubexpIncidencePlanScan.data, degree, indices]
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨9, h.symm⟩
      have h7 : i ≠ 7 := fun h => hi ⟨6, h.symm⟩
      have h10 : i ≠ 10 := fun h => hi ⟨5, h.symm⟩
      have h11 : i ≠ 11 := fun h => hi ⟨7, h.symm⟩
      simp only [scanned, a, ready, data, ite_eq_right h3, ite_eq_right h7, ite_eq_right h10, ite_eq_right h11]
  refine ⟨n + 1, rf, by omega, ?_⟩
  rw [← hc]
  exact h

theorem finish_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ) :
    ∃ rf, Eval finish
      (2 + (2 * (v + 1 + (scopes.take e).length + (indices scopes e v).length) + 9))
      (scanned regs scopes e v) (idle rf scopes e v (unary (degree scopes e v + 1))) := by
  let a := scanned regs scopes e v
  let b := pushed 3 true a
  let c := WorkspaceCleanupProgram.finish 0 1 cleanupPorts b
  have h1 := push_eval 3 true a
  have h2 := WorkspaceCleanupProgram.command_eval 0 1 cleanupPorts (by decide) b
  have hc : c = idle c.regs scopes e v (unary (degree scopes e v + 1)) := by
    apply congrArg (StructuredProgram.State.mk c.regs)
    funext i
    change (WorkspaceCleanupProgram.finish 0 1 cleanupPorts b).stacks i = _
    rw [WorkspaceCleanupProgram.finish_stack]
    fin_cases i <;> simp [cleanupPorts,
      b, pushed, a, scanned, data, List.replicate_succ]
  have h := h1.seq h2
  change Eval finish _ a c at h
  rw [hc] at h
  refine ⟨c.regs, ?_⟩
  have hcost : WorkspaceCleanupProgram.cost cleanupPorts b =
      2 * (v + 1 + (scopes.take e).length + (indices scopes e v).length) + 9 := by
    simp [WorkspaceCleanupProgram.cost, cleanupPorts, b, pushed, a, scanned, data,
      Nat.add_assoc]
  simpa only [hcost] using h

theorem program_run (regs : Fin 10 → Bool) (scopes : List (List ℕ)) (e v : ℕ)
    (he : e ≤ scopes.length) :
    ∃ rf, RunsIn program (budget scopes e v)
      ((idle regs scopes e v []).withPC (some program.entry))
      ((idle rf scopes e v (unary (degree scopes e v + 1))).withPC none) := by
  obtain ⟨r1, h1⟩ := prepare_eval regs scopes e v
  obtain ⟨n2, r2, hn2, h2⟩ := select_eval r1 scopes e v he
  obtain ⟨r3, h3⟩ := query_eval r2 scopes e v
  obtain ⟨n4, r4, hn4, h4⟩ := scan_eval r3 scopes e v
  obtain ⟨r5, h5⟩ := finish_eval r4 scopes e v
  have h := h1.seq (h2.seq (h3.seq (h4.seq h5)))
  refine ⟨r5, _, ?_, compiled_halt_trace h 0 3⟩
  dsimp [budget]
  omega

end SubexponentialSAT.SubexpIncidenceSlotProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Physical high-incidence selection from supplied explicit scopes

The input is a framed list of scopes with original natural-number identifiers.
Every query invokes the audited source-preserving record/membership scan. The
cutoff is a supplied unary integer in this module; no arithmetic or translation
from clauses to scopes is silently performed. The fixed program appends the
strict comparison bit and advances the original-coordinate counter.
-/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem countPorts_injective : Function.Injective countPorts := Fin.castAdd_injective _ _

theorem count_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) :
    ∃ n rf, n ≤ SubexpIncidenceSlotProgram.budget scopes scopes.length v ∧
      Eval count n (state regs scopes v cut mask fuel)
        ⟨rf, Function.update (state regs scopes v cut mask fuel).stacks 3
          (unary (degree scopes v + 1))⟩ := by
  let a := state regs scopes v cut mask fuel
  have hp : projectState id countPorts a =
      SubexpIncidenceSlotProgram.idle regs scopes scopes.length v [] := by
    apply congrArg₂ StructuredProgram.State.mk
    · rfl
    · first | done | (first | done | (funext i; fin_cases i <;> rfl))
  obtain ⟨rf, n, hn, ht⟩ := SubexpIncidenceSlotProgram.program_run regs scopes
    scopes.length v le_rfl
  have hd : SubexpIncidenceSlotProgram.degree scopes scopes.length v = degree scopes v := by
    simp [SubexpIncidenceSlotProgram.degree, degree,
      Subexp.IncidencePlanSpec.degree, Subexp.IncidencePlanSpec.incidentIndices]
  let b := SubexpIncidenceSlotProgram.idle rf scopes scopes.length v
    (unary (degree scopes v + 1))
  rw [hd] at ht
  rw [← hp] at ht
  have he := eval_call_from_state SubexpIncidenceSlotProgram.program id countPorts a
    Function.injective_id countPorts_injective ht
  have hb : embedState id countPorts a b =
      (⟨rf, Function.update a.stacks 3 (unary (degree scopes v + 1))⟩ : Data) := by
    apply embedState_eq_of_ports id countPorts a _ b
      Function.injective_id countPorts_injective
    · intro i; rfl
    · intro i hi; exact (hi ⟨i, rfl⟩).elim
    · intro i; fin_cases i <;> rfl
    · intro i hi
      have h3 : i ≠ 3 := fun h => hi ⟨3, h.symm⟩
      simp [h3]
  change Eval count n a (embedState id countPorts a b) at he
  rw [hb] at he
  exact ⟨n, rf, hn, he⟩

theorem copy_eval (src dst tmp : Fin 16) (a : Data)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst) (ht : a.stacks tmp = []) :
    Eval (copy src dst tmp) (7 * (a.stacks src).length + 5) a (copied src dst a) :=
  .call _ (ListRegisterProgram.copy_run src dst tmp 0 1 hsd hst htd (by decide)
    a.regs a.stacks ht)

theorem compareRegs_injective : Function.Injective compareRegs := Fin.castAdd_injective _ _
theorem comparePorts_injective : Function.Injective comparePorts := by decide

theorem compare_eval (a : Data) :
    ∃ n b, Eval compare n a b ∧
      n ≤ 4 * min (a.stacks 3).length (a.stacks 4).length + 6 ∧
      b.regs 3 = decide ((a.stacks 3).length ≤ (a.stacks 4).length) ∧
      (b.stacks 3).length ≤ (a.stacks 3).length ∧
      (b.stacks 4).length ≤ (a.stacks 4).length ∧
      (∀ i : Fin 16, i ≠ 3 → i ≠ 4 → b.stacks i = a.stacks i) := by
  obtain ⟨n, hn, c, ht, hpc, hf⟩ := Subexp.UnaryCompare.runs
    (a.regs ∘ compareRegs) (a.stacks 3) (a.stacks 4)
  let d : State 4 2 := ⟨c.regs, c.stacks⟩
  have hc : d.withPC none = c := by cases c; simp_all [d, StructuredProgram.State.withPC]
  have hp : Subexp.UnaryCompare.start (a.regs ∘ compareRegs) (a.stacks 3) (a.stacks 4) =
      (projectState compareRegs comparePorts a).withPC
        (some Subexp.UnaryCompare.program.entry) := by
    change Cfg.mk _ _ _ = Cfg.mk _ _ _
    congr 1
    first | done | (first | done | (funext i; fin_cases i <;> rfl))
  rw [hp, ← hc] at ht
  let b := embedState compareRegs comparePorts a d
  have he := eval_call_from_state Subexp.UnaryCompare.program compareRegs comparePorts a
    compareRegs_injective comparePorts_injective ht
  have hs (i : Fin 2) : b.stacks (comparePorts i) = c.stacks i :=
    embedState_stack _ _ _ _ comparePorts_injective i
  refine ⟨n, b, he, hn, ?_, ?_, ?_, ?_⟩
  · exact (embedState_register _ _ _ _ compareRegs_injective 3).trans hf
  · have hl := Subexp.UnaryCompare.trace_length_le ht 0
    change (c.stacks 0).length ≤ (a.stacks 3).length at hl
    have hs0 := hs 0
    change b.stacks 3 = c.stacks 0 at hs0
    simpa only [← hs0] using hl
  · have hl := Subexp.UnaryCompare.trace_length_le ht 1
    change (c.stacks 1).length ≤ (a.stacks 4).length at hl
    have hs1 := hs 1
    change b.stacks 4 = c.stacks 1 at hs1
    simpa only [← hs1] using hl
  · intro i h3 h4
    apply embedState_stack_frame
    rintro ⟨j, hj⟩
    fin_cases j <;> simp [comparePorts] at hj <;> simp_all

theorem pushTrue_eval (dst : Fin 16) (a : Data) :
    Eval (pushTrue dst) 2 a (pushedTrue dst a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 10) true) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push dst (0 : Fin 10)) _))
  simpa [pushTrue, pushedTrue, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

theorem emitHigh_eval (a : Data) : Eval emitHigh 2 a (emittedHigh a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.bnot (3 : Fin 10) 3) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (14 : Fin 16) (3 : Fin 10)) _))
  simpa [emitHigh, emittedHigh, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

theorem query_eval (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (v cut : ℕ) (mask fuel : List Bool) :
    ∃ n rf, n ≤ queryBudget scopes v cut ∧
      Eval query n (state regs scopes v cut mask fuel)
        (state rf scopes (v + 1) cut (decide (cut < degree scopes v) :: mask) fuel) := by
  let a := state regs scopes v cut mask fuel
  obtain ⟨nc, rc, hnc, hec⟩ := count_eval regs scopes v cut mask fuel
  let b : Data := ⟨rc, Function.update a.stacks 3 (unary (degree scopes v + 1))⟩
  let c := copied 13 4 b
  have hecopy := copy_eval 13 4 8 b (by decide) (by decide) (by decide) (by rfl)
  obtain ⟨nt, d, het, hnt, hflag, h3, h4, hframe⟩ := compare_eval c
  have hc3 : c.stacks 3 = unary (degree scopes v + 1) := by
    simp [c, copied, StackRoutines.copyStacks, b]
  have hc4 : c.stacks 4 = unary (cut + 1) := by
    simp [c, copied, StackRoutines.copyStacks, b, a, state]
  have hcframe (i : Fin 16) (hi3 : i ≠ 3) (hi4 : i ≠ 4) : c.stacks i = a.stacks i := by
    simp [c, copied, StackRoutines.copyStacks, b, hi3, hi4]
  have hhigh : (!d.regs 3) = decide (cut < degree scopes v) := by
    rw [hflag, hc3, hc4]
    simp only [unary, List.length_replicate, ← decide_not]
    simp only [Nat.not_le, Nat.add_lt_add_iff_right]
  let e := emittedHigh d
  let f := WorkspaceCleanupProgram.finish 0 1 [3, 4] e
  let g := pushedTrue 2 f
  have hclean := WorkspaceCleanupProgram.command_eval (0 : Fin 10) 1
    ([3, 4] : List (Fin 16)) (by decide) e
  have hg : g = state g.regs scopes (v + 1) cut
      (decide (cut < degree scopes v) :: mask) fuel := by
    apply congrArg (StructuredProgram.State.mk g.regs)
    funext i
    have hf3 : f.stacks 3 = [] := by simp [f]
    have hf4 : f.stacks 4 = [] := by simp [f]
    have hdframe (j : Fin 16) (hj3 : j ≠ 3) (hj4 : j ≠ 4) :=
      (hframe j hj3 hj4).trans (hcframe j hj3 hj4)
    fin_cases i <;>
      simp [ f, e, emittedHigh, hhigh, hdframe,
        a, state, List.replicate_succ]
  have he := hec.seq (hecopy.seq (het.seq ((emitHigh_eval d).seq
    (hclean.seq (pushTrue_eval 2 f)))))
  change Eval query _ a g at he
  rw [hg] at he
  refine ⟨_, g.regs, ?_, he⟩
  have hcopylen : (b.stacks 13).length = cut + 1 := by simp [b, a, state]
  have hnt' : nt ≤ 4 * (cut + 1) + 6 := by
    rw [hc3, hc4, List.length_replicate, List.length_replicate] at hnt
    exact hnt.trans (by omega)
  have h3' : (d.stacks 3).length ≤ degree scopes v + 1 := by simpa [hc3] using h3
  have h4' : (d.stacks 4).length ≤ cut + 1 := by simpa [hc4] using h4
  have hcleanCost : WorkspaceCleanupProgram.cost ([3, 4] : List (Fin 16)) e ≤
      2 * (degree scopes v + 1 + (cut + 1)) + 6 := by
    simp only [WorkspaceCleanupProgram.cost, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, List.length_cons, List.length_nil]
    dsimp [e, emittedHigh]
    simp only [Function.update_of_ne (show (3 : Fin 16) ≠ 14 by decide),
      Function.update_of_ne (show (4 : Fin 16) ≠ 14 by decide)]
    omega
  rw [hcopylen]
  dsimp [queryBudget]
  omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramScan
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Full original-coordinate scan using a runtime unary loop counter. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
attribute [local irreducible] query count compare
  SubexpIncidenceSlotProgram.scopeBits Subexp.IncidencePlanSpec.degree

theorem state_fuel_other (regs regs' : Fin 10 → Bool) (scopes : List (List ℕ))
    (i cut : ℕ) (mask fuel fuel' : List Bool) (j : Fin 16) (hj : j ≠ 15) :
    (state regs scopes i cut mask fuel).stacks j =
      (state regs' scopes i cut mask fuel').stacks j := by
  fin_cases j <;> first | exact (hj rfl).elim |
    simp only [state, Matrix.cons_val_succ', Matrix.cons_val_zero']

theorem state_fuel (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (i cut : ℕ) (mask fuel : List Bool) :
    (state regs scopes i cut mask fuel).stacks 15 = fuel := by
  change (state regs scopes i cut mask fuel).stacks ⟨15, by decide⟩ = fuel
  simp only [state, Matrix.cons_val_succ', Matrix.cons_val_zero']

theorem scanInvariant_stable (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool) :
    UnaryForPrograms.FrameStable scanPorts (scanInvariant scopes cut mask) := by
  intro i a b heq hi
  obtain ⟨regs, fuel, ha⟩ := hi
  refine ⟨b.regs, b.stacks 15, ?_⟩
  apply CounterForPrograms.data_ext (a := b)
    (b := state b.regs scopes i cut (highPrefix scopes cut i ++ mask) (b.stacks 15)) rfl
  funext j
  by_cases hj : j = 15
  · subst j
    exact (state_fuel _ _ _ _ _ _).symm
  · have h := heq j hj
    rw [ha] at h
    exact h.symm.trans (state_fuel_other regs b.regs scopes i cut
      (highPrefix scopes cut i ++ mask) fuel (b.stacks 15) j hj)

theorem query_bodySpec (scopes : List (List ℕ)) (cut : ℕ) (mask : List Bool) :
    UnaryForPrograms.BodySpec scanPorts query (scanInvariant scopes cut mask)
      (fun i => queryBudget scopes i cut) := by
  intro i d hi
  obtain ⟨regs, fuel, hd⟩ := hi
  obtain ⟨n, rf, hn, he⟩ := query_eval regs scopes i cut
    (highPrefix scopes cut i ++ mask) fuel
  refine ⟨n, state rf scopes (i+1) cut
    (decide (cut < degree scopes i) :: (highPrefix scopes cut i ++ mask)) fuel,
    hn, ?_, ?_, rf, fuel, rfl⟩
  · rw [hd]
    exact he
  · rw [hd]
    change (state rf scopes (i+1) cut
      (decide (cut < degree scopes i) :: (highPrefix scopes cut i ++ mask)) fuel).stacks 15 =
      (state regs scopes i cut (highPrefix scopes cut i ++ mask) fuel).stacks 15
    rw [state_fuel, state_fuel]

theorem scan_eval_oai (regs : Fin 10 → Bool) (scopes : List (List ℕ))
    (n cut : ℕ) (mask : List Bool) :
    ∃ time rf, time ≤ scanBudget scopes n cut ∧
      Eval scan time (state regs scopes 0 cut mask (unary n))
        (state rf scopes n cut (highPrefix scopes cut n ++ mask) []) := by
  let a := state regs scopes 0 cut mask (unary n)
  obtain ⟨time, b, he, hb, hf, ht⟩ := UnaryForPrograms.for_correct scanPorts query
    (scanInvariant scopes cut mask) (fun i => queryBudget scopes i cut)
    (scanInvariant_stable scopes cut mask) (query_bodySpec scopes cut mask) a
    ⟨regs, unary n, rfl⟩
  have hlen : (a.stacks scanPorts.counter).length = n := by simp [a, state, scanPorts]
  rw [hlen] at hb ht
  obtain ⟨rf, fuel, hbeq⟩ := hb
  have hfu : fuel = [] := by simpa [hbeq, state, scanPorts] using hf
  subst fuel
  exact ⟨time, rf, ht, by simpa only [scan, hbeq] using he⟩


end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.scan_eval_oai
