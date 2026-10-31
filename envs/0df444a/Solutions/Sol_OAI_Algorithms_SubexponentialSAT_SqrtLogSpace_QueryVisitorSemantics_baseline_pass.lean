-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T11:51:59.808444+00:00
-- url     : https://prove2.me/submissions/c5066a5d-06cf-417b-9693-f2724c5d00f2

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S191
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryExecution_replay_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics_baseline_head

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramLogic
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Measured verification rules for fixed bit programs

Every execution judgment below contains actual transitions of one fixed step
function. Loop iterations may be controlled by unbounded data; neither the
transition function nor its finite control changes with the iteration count.
No judgment assigns a cost to an unimplemented mathematical function.
-/

namespace SubexponentialSAT.ProgramLogic

open SubexponentialSAT.Computation
open scoped BigOperators

section Traces

variable {Cfg : Type} {step : Cfg → Option Cfg}

/-- A frame observation preserved by each actual step is preserved by the run. -/
theorem frame_trace {Frame : Type} (frame : Cfg → Frame)
    (preserve : ∀ a b, step a = some b → frame b = frame a)
    {steps : ℕ} {a b : Cfg} (h : Trace step steps a b) : frame b = frame a := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (preserve _ _ hs)

end Traces

section BitPrograms

open SubexponentialSAT.BitProgram

variable {r s l : ℕ}

theorem execInstr_register_frame (instr : Instr r s l) (c : Cfg r s l) (k : Fin r)
    (hk : k ∉ registerWrites instr) : (execInstr instr c).regs k = c.regs k := by
  cases instr <;> simp_all [registerWrites, execInstr, readRegs]

theorem step_register_frame (p : Program r s l) {a b : Cfg r s l} (k : Fin r)
    (safe : ∀ label, a.pc = some label → k ∉ registerWrites (p.code label))
    (hs : step p a = some b) : b.regs k = a.regs k := by
  cases hp : a.pc with
  | none => simp [step, hp] at hs
  | some label =>
      have heq : execInstr (p.code label) a = b := by simpa [step, hp] using hs
      subst b
      exact execInstr_register_frame _ _ _ (safe label hp)

end BitPrograms

end SubexponentialSAT.ProgramLogic

end OAI.Algorithms
end

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

open BitProgram

theorem readRegs_frame {r : ℕ} (regs : Fin r → Bool) (value present j : Fin r)
    (top : Option Bool) (hv : j ≠ value) (hp : j ≠ present) :
    readRegs regs value present top j = regs j := by
  simp [readRegs, hv, hp]

end SubexponentialSAT.StackRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandRegisterFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Register frames derived from the actual finite instruction tables and
structured command syntax. These footprints describe code, not an assumed
semantic behavior of a callback. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames

open OAI BitProgram ProgramLogic

theorem trace_register_frame {r s l : ℕ} (p : Program r s l)
    {steps : ℕ} {a b : Cfg r s l} (ht : Trace p steps a b)
    (i : Fin r) (hi : i ∉ programWrites p) : b.regs i = a.regs i := by
  apply ProgramLogic.frame_trace (fun c : Cfg r s l => c.regs i) ?_ ht
  intro a b hs
  exact step_register_frame p i (fun label _ => (not_mem_programWrites p i).mp hi label) hs

theorem base_eval_register_frame {r s : ℕ} {c : StructuredProgram.Cmd r s}
    {steps : ℕ} {a b : StructuredProgram.State r s}
    (ht : StructuredProgram.Eval c steps a b) (i : Fin r)
    (hi : i ∉ baseWrites c) : b.regs i = a.regs i := by
  induction ht with
  | skip => rfl
  | atom atom a => exact execInstr_register_frame (atom.instr (0 : Fin 1)) (a.withPC none) i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ baseWrites first ∧ i ∉ baseWrites second := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ baseWrites yes ∧ i ∉ baseWrites no := by
        simpa only [baseWrites, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Every actual execution preserves each register outside the static writes. -/
theorem eval_register_frame {r s : ℕ} {c : StructuredCalls.Cmd r s}
    {steps : ℕ} {a b : StructuredCalls.State r s}
    (ht : StructuredCalls.Eval c steps a b) (i : Fin r)
    (hi : i ∉ writes c) : b.regs i = a.regs i := by
  induction ht with
  | base he => exact base_eval_register_frame he i hi
  | call p ht => exact trace_register_frame p ht i hi
  | @seq first second _ _ _ _ _ hf hs ihf ihs =>
      have hi' : i ∉ writes first ∧ i ∉ writes second := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact (ihs hi'.2).trans (ihf hi'.1)
  | @ite_true test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.1
  | @ite_false test yes no n a b ht he ih =>
      have hi' : i ∉ writes yes ∧ i ∉ writes no := by
        simpa only [writes, Finset.mem_union, not_or] using hi
      exact ih hi'.2
  | while_false => rfl
  | while_true _ _ _ ihb ihw => exact (ihw hi).trans (ihb hi)

/-- Relocation changes every destination by precisely the declared register map. -/
theorem relocate_writes {r s l R S L : ℕ}
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (label : Fin l → Fin L)
    (returnPc : Option (Fin L)) (instr : Instr r s l) :
    registerWrites (ProgramLinking.relocateInstr register stack label returnPc instr) =
      (registerWrites instr).image register := by
  cases instr <;> cases returnPc <;> simp [ProgramLinking.relocateInstr, registerWrites]

theorem not_mem_liftProgram {r s l R S : ℕ} (p : Program r s l)
    (register : Fin r → Fin R) (stack : Fin s → Fin S) (i : Fin R)
    (hi : ¬ ∃ j, register j = i) :
    i ∉ programWrites (ProgramLinking.liftProgram p register stack) := by
  rw [not_mem_programWrites]
  intro label
  simp only [relocate_writes, Finset.mem_image, not_exists]
  intro j hj
  exact hi ⟨j, hj.2⟩


/-- These primitive loops can only write their explicit value/presence registers. -/
theorem not_mem_clearProgram {r s : ℕ} (src : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.clearProgram src value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

theorem not_mem_copyProgram {r s : ℕ} (src dst tmp : Fin s) (value present i : Fin r)
    (hv : i ≠ value) (hp : i ≠ present) :
    i ∉ programWrites (StackRoutines.copyProgram src dst tmp value present) := by
  rw [not_mem_programWrites]
  intro label
  fin_cases label <;> simp [registerWrites, hv, hp]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandRegisterFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-!
# Fixed-control interpreter for streaming signature tuples

The input-dependent depth is represented by an encoded stack of suspended
frames. `probe` tests one candidate against earlier assignments. A rejected
candidate advances at its current depth; only a fresh signature descends.
Thus this control table never traverses raw assignment tuples.

The subroutines are concrete finite commands, and all execution theorems use
their actual measured evaluations. Instantiating their frame, signature, and
counter invariants remains a separate native-program obligation.
-/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram

open BitProgram StructuredCalls

/-- Resume consumes one suspended frame and exactly restores its payload. -/
theorem popFrame_trace (word frames : List Bool) (v present : Bool) :
    Trace ParserProgram.frameProgram (6 * word.length + 4)
      (ParserProgram.cfg (some 0) v present (Encoding.frame word.reverse ++ frames) [])
      (ParserProgram.cfg none false true frames word) := by
  simpa using ParserProgram.frame_trace word.reverse frames [] v present

theorem copyWord_eval (src dst tmp : Fin 896)
    (hsd : src ≠ dst) (hst : src ≠ tmp) (htd : tmp ≠ dst)
    (a : State 40 896) (he : a.stacks tmp = []) :
    Eval (copyWord src dst tmp) (7 * (a.stacks src).length + 5) a
      (copyState src dst a) := by
  have ht := StackRoutines.copyProgram_trace src dst (tmp) (0 : Fin 40) 1
    hsd hst htd (by decide) a.regs a.stacks he
  have hh := StackRoutines.halt_after_trace _ ht 7 rfl rfl
  exact .call _ (by simpa [copyState, StackRoutines.copyResult,
    StructuredProgram.State.withPC, StackRoutines.copyProgram, Nat.add_assoc] using hh)

private theorem extend_restrict_eq {A B C : Type*} (f : A → B) (g : B → C) :
    Function.extend f (g ∘ f) g = g := by
  classical
  funext b
  by_cases h : ∃ a, f a = b
  · obtain ⟨a, rfl⟩ := h
    exact Function.FactorsThrough.extend_apply (fun _ _ he => congrArg g he) g a
  · exact Function.extend_apply' _ _ _ h

private theorem word_embed_self (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) :
    embedState frameRegisters (wordPorts src dst h) a
      (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)) = a := by
  apply CounterForPrograms.data_ext
  · have hr : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).regs =
        a.regs ∘ frameRegisters := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend frameRegisters _ a.regs = a.regs
    rw [hr, extend_restrict_eq]
  · have hs : (frameState (a.regs 0) (a.regs 1) (a.stacks src) (a.stacks dst)).stacks =
        a.stacks ∘ wordPorts src dst h := by
      first | done | (funext i; fin_cases i <;> rfl)
    change Function.extend (wordPorts src dst h) _ a.stacks = a.stacks
    rw [hs, extend_restrict_eq]

theorem popWord_eval (src dst : Fin 896) (h : src ≠ dst) (a : State 40 896)
    (word tail : List Bool) (hs : a.stacks src = Encoding.frame word.reverse ++ tail)
    (hd : a.stacks dst = []) :
    Eval (popWordCommand src dst h) (6 * word.length + 4) a
      (popWordState src dst h a word tail) := by
  have ht := eval_call_lifted ParserProgram.frameProgram frameRegisters (wordPorts src dst h) a
    frameRegisters.injective (wordPorts src dst h).injective
    (a := frameState (a.regs 0) (a.regs 1) (Encoding.frame word.reverse ++ tail) [])
    (b := frameState false true tail word)
    (popFrame_trace word tail (a.regs 0) (a.regs 1))
  rw [← hs, ← hd, word_embed_self] at ht
  exact ht

theorem popWordState_src (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks src = tail :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 0

theorem popWordState_dst (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool) :
    (popWordState src dst h a word tail).stacks dst = word :=
  embedState_stack _ _ _ _ (wordPorts src dst h).injective 1

theorem popWordState_outside (src dst : Fin 896) (h : src ≠ dst)
    (a : State 40 896) (word tail : List Bool)
    (i : Fin 896) (his : i ≠ src) (hid : i ≠ dst) :
    (popWordState src dst h a word tail).stacks i = a.stacks i := by
  apply embedState_stack_frame
  rintro ⟨j, hj⟩
  fin_cases j
  · exact his hj.symm
  · exact hid hj.symm

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleVisitor
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The representative tuple is already a polynomial-length stack of escaped
frames, deepest head first. These fixed commands copy that stack, extract one
actual representative, and decrement its unary physical head address. They do
not enumerate assignments or construct a Cartesian product. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor

open OAI BitProgram StructuredCalls
open SignatureTupleProgram

theorem readHead_eval (a : Data) (word tail address : List Bool)
    (hframes : a.stacks 840 = Encoding.frame word.reverse ++ tail)
    (hword : a.stacks 838 = []) (haddress : a.stacks 843 = true :: address) :
    Eval readHead (6 * word.length + 5) a (headState a word tail address) := by
  have hp := popWord_eval 840 838 (by decide) a word tail hframes hword
  let b := popWordState 840 838 (by decide) a word tail
  have hb : b.stacks 843 = true :: address := by
    rw [popWordState_outside _ _ _ _ _ _ _ (by decide) (by decide)]
    exact haddress
  have he : Eval (.base (.atom (.pop 843 0 1))) 1 b (headState a word tail address) := by
    convert Eval.base (StructuredProgram.Eval.atom (.pop 843 0 1) b) using 1
    all_goals try with_reducible_and_instances rfl
    apply SubexpScanPrimitives.state_ext
    · change readRegs b.regs 0 1 (some true) = readRegs b.regs 0 1 (b.stacks 843).head?
      rw [hb]
      rfl
    · change Function.update b.stacks 843 address = Function.update b.stacks 843 (b.stacks 843).tail
      rw [hb]
      rfl
  simpa only [readHead, headState,
    show 6 * word.length + 4 + 1 = 6 * word.length + 5 by omega] using hp.seq he

theorem headState_words (a : Data) (word tail address : List Bool) :
    (headState a word tail address).stacks 838 = word ∧
      (headState a word tail address).stacks 840 = tail ∧
      (headState a word tail address).stacks 843 = address := by
  simp only [headState, Function.update_of_ne (by decide : (838 : Fin 896) ≠ 843),
    Function.update_of_ne (by decide : (840 : Fin 896) ≠ 843), Function.update_self]
  exact ⟨popWordState_dst _ _ _ _ _ _, popWordState_src _ _ _ _ _ _, True.intro⟩

theorem headState_frame (a : Data) (word tail address : List Bool) (i : Fin 896)
    (h838 : i ≠ 838) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (headState a word tail address).stacks i = a.stacks i := by
  simp only [headState, Function.update_of_ne h843]
  exact popWordState_outside _ _ _ _ _ _ _ h840 h838

/-- The address counts unprocessed heads above the fixed node offset. Reading
one frame decrements exactly once, even if that representative has zero bits. -/
theorem readHead_frames (a : Data) (word : List Bool) (rest : List (List Bool))
    (base : ℕ)
    (hframes : a.stacks 840 = suspendedFrames (word :: rest))
    (hword : a.stacks 838 = [])
    (haddress : a.stacks 843 = List.replicate (base + (word :: rest).length) true) :
    Eval readHead (6 * word.length + 5) a
      (headState a word (suspendedFrames rest) (List.replicate (base + rest.length) true)) := by
  apply readHead_eval
  · simpa only [suspendedFrames, List.flatMap_cons] using hframes
  · exact hword
  · simpa only [List.length_cons, Nat.add_succ, List.replicate_succ] using haddress

private theorem clear_eval (dst : Fin 896) (a : Data) :
    Eval (.call (StackRoutines.clearProgram dst 0 1)) (2 * (a.stacks dst).length + 3)
      a ⟨readRegs a.regs 0 1 none,StackRoutines.clearStacks dst a.stacks⟩ :=
  Eval.call _ (ListRegisterProgram.clear_run dst (0 : Fin 40) 1 a.regs a.stacks)

theorem overwrite_eval (src dst : Fin 896) (hsd : src ≠ dst)
    (hst : src ≠ 841) (htd : (841 : Fin 896) ≠ dst)
    (a : Data) (htmp : a.stacks 841 = []) :
    Eval (overwrite src dst) (2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8)
      a (overwriteState src dst a) := by
  have hc := clear_eval dst a
  have ht : (StackRoutines.clearStacks dst a.stacks) 841 = [] := by
    simp [StackRoutines.clearStacks, htd, htmp]
  have hp := copyWord_eval src dst 841 hsd hst htd
    ⟨readRegs a.regs 0 1 none, StackRoutines.clearStacks dst a.stacks⟩ ht
  have hs : (StackRoutines.clearStacks dst a.stacks) src = a.stacks src := by
    simp [StackRoutines.clearStacks,hsd]
  simpa only [overwrite, overwriteState, hs, show 2 * (a.stacks dst).length + 3 +
    (7 * (a.stacks src).length + 5) =
    2 * (a.stacks dst).length + 7 * (a.stacks src).length + 8 by omega] using hc.seq hp

theorem overwriteState_stacks (src dst : Fin 896) (hsd : src ≠ dst) (a : Data) :
    (overwriteState src dst a).stacks = Function.update a.stacks dst (a.stacks src) := by
  funext i
  by_cases hi : i = dst
  · subst i
    simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hsd]
  · simp [overwriteState,copyState,StackRoutines.copyStacks,StackRoutines.clearStacks,hi]

theorem testFrames_eval (a : Data) : Eval testFrames 1 a (tested a) :=
  Eval.base (StructuredProgram.Eval.atom (.peek 840 0 1) a)

theorem finishHead_eval (a : Data) :
    Eval finishHead (2 * (a.stacks 838).length + 4) a (finished a) := by
  have h := (clear_eval 838 a).seq (testFrames_eval _)
  simpa only [finishHead, finished, show 2 * (a.stacks 838).length + 3 + 1 =
    2 * (a.stacks 838).length + 4 by omega] using h

theorem finished_stacks (a : Data) :
    (finished a).stacks = Function.update a.stacks 838 [] := rfl

theorem overwriteState_frame (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (i : Fin 896) (hi : i ≠ dst) :
    (overwriteState src dst a).stacks i = a.stacks i := by
  rw [overwriteState_stacks src dst hsd,Function.update_of_ne hi]

theorem restart_eval (a : Data) (htmp : a.stacks 841 = []) :
    Eval restart (restartCost a) a (restartState a) := by
  have h1 := overwrite_eval 837 840 (by decide) (by decide) (by decide) a htmp
  have h841 : (overwriteState 837 840 a).stacks 841 = [] :=
    (overwriteState_frame _ _ (by decide) _ _ (by decide)).trans htmp
  have h2 := overwrite_eval 845 843 (by decide) (by decide) (by decide)
    (overwriteState 837 840 a) h841
  have h843 := overwriteState_frame 837 840 (by decide) a 843 (by decide)
  have h845 := overwriteState_frame 837 840 (by decide) a 845 (by decide)
  have ht := h1.seq h2
  simpa only [restart, restartState, h843,h845,restartCost,show
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length + 8 +
      (2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 8) =
    2 * (a.stacks 840).length + 7 * (a.stacks 837).length +
      2 * (a.stacks 843).length + 7 * (a.stacks 845).length + 16 by omega] using ht

theorem restartState_frame (a : Data) (i : Fin 896) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (restartState a).stacks i = a.stacks i := by
  rw [restartState,overwriteState_frame _ _ (by decide) _ _ h843,
    overwriteState_frame _ _ (by decide) _ _ h840]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryExecution
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Composition of the concrete streamed query. The traversal resource lemma
keeps the per-head execution time separate from its prefix storage bound;
neither the number of assignments nor their running time is used as space. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution

open OAI BitProgram StructuredCalls
open QueryTupleVisitor SignatureTupleProgram

theorem cursor_word_length {base B : ℕ} {word : List Bool}
    {rest : List (List Bool)} {a : Data}
    (hc : FrameCursor base (word::rest) a)
    (ha : ∀ i, (a.stacks i).length ≤ B) : word.length ≤ B := by
  have h := ha 840
  rw [hc.frames] at h
  simp only [suspendedFrames, List.flatMap_cons, List.length_append,
    Encoding.length_frame, List.length_reverse] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryExecution
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleState
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.Packing.nonemptyUniversal
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The attained-tuple traversal retains the actual query inputs and the
meaning of its current pair accumulator. These predicates contain word
identities and algebraic facts, with no execution or algorithm-service fields. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState

open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing
open LeafProgram MomentsProgram LayoutProgram Subexp.ConstructivePacking MulticolorTypes
open TruncatedRingProgram SubexpSetupStorage

namespace QueryMasterFrame

theorem trans {a b c : Data} (hab : QueryMasterFrame a b) (hbc : QueryMasterFrame b c) :
    QueryMasterFrame a c := ⟨fun i hi => (hbc.word i hi).trans (hab.word i hi)⟩

end QueryMasterFrame

namespace QueryReady

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ} {a b : Data}
    (h : QueryReady q node H high E U P a) (hf : QueryMasterFrame a b) :
    QueryReady q node H high E U P b := by
  refine {
    lifting := h.lifting
    generatedTheta := h.generatedTheta
    sourceMinus := h.sourceMinus
    ambient := (hf.word 128 (by decide)).trans h.ambient
    theta := (hf.word 78 (by decide)).trans h.theta
    modulus := (hf.word 194 (by decide)).trans h.modulus
    table := (hf.word 201 (by decide)).trans h.table
    width := (hf.word 202 (by decide)).trans h.width
    scalarZero := (hf.word 203 (by decide)).trans h.scalarZero
    degree := (hf.word 204 (by decide)).trans h.degree
    one := (hf.word 207 (by decide)).trans h.one
    minus := (hf.word 211 (by decide)).trans h.minus
    precision := (hf.word 212 (by decide)).trans h.precision
    order := (hf.word 243 (by decide)).trans h.order
    zero := (hf.word 280 (by decide)).trans h.zero
    code := (hf.word 281 (by decide)).trans h.code
    clauses := (hf.word 700 (by decide)).trans h.clauses
    rows := (hf.word 701 (by decide)).trans h.rows
    rowCount := (hf.word 704 (by decide)).trans h.rowCount
    markedIndex := (hf.word 705 (by decide)).trans h.markedIndex
    markedFlag := (hf.word 706 (by decide)).trans h.markedFlag
    indexModulus := (congrArg BinaryArithmetic.toNat (hf.word 707 (by decide))).trans h.indexModulus
    indexWidth := (congrArg List.length (hf.word 708 (by decide))).trans h.indexWidth
    highMask := (hf.word 702 (by decide)).trans h.highMask
    highBits := (hf.word 703 (by decide)).trans h.highBits
    outer := (hf.word 858 (by decide)).trans h.outer
    inner := (hf.word 857 (by decide)).trans h.inner
    outerFree := h.outerFree
    innerSubset := h.innerSubset
    colors := (hf.word 130 (by decide)).trans h.colors
    nodes := (hf.word 131 (by decide)).trans h.nodes
    typeWidth := (hf.word 132 (by decide)).trans h.typeWidth
    positive := (hf.word 710 (by decide)).trans h.positive
    negative := (hf.word 711 (by decide)).trans h.negative
    sourceWidth := (hf.word 140 (by decide)).trans h.sourceWidth
    power := (hf.word 712 (by decide)).trans h.power
    powerNegative := h.powerNegative
    radius := (hf.word 138 (by decide)).trans h.radius
    offset := (hf.word 139 (by decide)).trans h.offset
    metadata := (hf.word 135 (by decide)).trans h.metadata
    plans := (hf.word 136 (by decide)).trans h.plans
    inverses := (hf.word 713 (by decide)).trans h.inverses
    negatives := (hf.word 714 (by decide)).trans h.negatives
    differences := (hf.word 715 (by decide)).trans h.differences
    ringWidth := (hf.word 717 (by decide)).trans h.ringWidth
    rowWidth := (hf.word 716 (by decide)).trans h.rowWidth
    inverseDenominator := (hf.word 728 (by decide)).trans h.inverseDenominator
    cacheCaps := ?_
    ambientCap := ?_
    oneCap := ?_ }
  · intro p hp
    have hm : p.1.castAdd 128∈masterPorts := by
      simp only [LeafNodeCacheProgram.directCopies,List.mem_cons,
        List.not_mem_nil,or_false] at hp
      rcases hp with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals decide
    rw [hf.word _ hm]
    exact h.cacheCaps p hp
  · rw [hf.word 128 (by decide)]
    exact h.ambientCap
  · rw [hf.word 207 (by decide)]
    exact h.oneCap

end QueryReady

namespace DenseWord

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d} {port : Fin 896}
    {value : Dense (q.p.model.O q.p.t) q.p.t q.J} {a b : Data}
    (h : DenseWord q port value a) (hf : b.stacks port=a.stacks port) :
    DenseWord q port value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end DenseWord

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

/-- Both paid replay initializers preserve every retained query input. -/
theorem replay_masterFrame (a : Data) :
    QueryMasterFrame a (QueryTupleVisitor.tested (QueryTupleVisitor.restartState a)) := by
  constructor
  intro i hi
  have hs : i≠840 ∧ i≠843 := by
    simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact QueryTupleVisitor.restartState_frame a i hs.1 hs.2

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleState
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Static register frames for the concrete tuple visitor. The frame follows
from the actual instructions and embeddings, including the ambient overlay.
The retained tuple-controller flags require no save stack. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames

open OAI BitProgram StructuredCalls
open CommandRegisterFrames QueryTupleVisitor

private theorem not_mem_union_iff {R : Type} [DecidableEq R]
    {i : R} {left right : Finset R} :
    i ∉ left ∪ right ↔ i ∉ left ∧ i ∉ right := by
  simp only [Finset.mem_union, not_or]

private theorem high_ne (i : Fin 40) (hi : 16 ≤ i.val)
    (j : Fin 40) (hj : j.val < 16) : i ≠ j := by
  intro h
  subst i
  omega

private theorem copy_not_mem_writes (src dst tmp : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes (SignatureTupleProgram.copyWord src dst tmp) :=
  not_mem_copyProgram src dst tmp 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide))

theorem overwrite_not_mem_writes (src dst : Fin 896)
    (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes (overwrite src dst) :=
  not_mem_union_iff.mpr ⟨not_mem_clearProgram dst 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)),
    copy_not_mem_writes src dst 841 i hi⟩

theorem restart_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes restart :=
  not_mem_union_iff.mpr ⟨overwrite_not_mem_writes 837 840 i hi,
    overwrite_not_mem_writes 845 843 i hi⟩

theorem readHead_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes readHead := by
  have hp : i ∉ writes (SignatureTupleProgram.popWordCommand 840 838 (by decide)) := by
    apply not_mem_liftProgram
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    omega
  have h0 := high_ne i hi 0 (by decide)
  have h1 := high_ne i hi 1 (by decide)
  simpa [readHead, writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites, h0, h1] using hp

private theorem testFrames_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes testFrames := by
  simp [testFrames, writes, baseWrites, StructuredProgram.Atom.instr,
    ProgramLogic.registerWrites, high_ne i hi 0 (by decide), high_ne i hi 1 (by decide)]

theorem finishHead_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) :
    i ∉ writes finishHead :=
  not_mem_union_iff.mpr ⟨not_mem_clearProgram 838 0 1 i
    (high_ne i hi 0 (by decide)) (high_ne i hi 1 (by decide)),
    testFrames_not_mem_writes i hi⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorCorrect
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Correctness of the fixed concrete two-pass visitor. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
open OAI BitProgram StructuredCalls

open OAI.Algorithms.SubexponentialSAT.SqrtLog SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SubexpSetupStorage

theorem headState_masterFrame (a : Data) (word tail address : List Bool) :
    QueryMasterFrame a (headState a word tail address) := by
  constructor
  intro i hi
  have hs : i≠838 ∧ i≠840 ∧ i≠843 := by
    simp only [masterPorts, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide
  exact headState_frame a word tail address i hs.1 hs.2.1 hs.2.2

theorem finishHead_masterFrame (a : Data) : QueryMasterFrame a (finished a) := by
  constructor
  intro i hi
  have hne : i≠838 := by
    intro he
    subst i
    exact (by decide : (838 : Fin 896)∉masterPorts) hi
  rw [finished_stacks,Function.update_of_ne hne]

/-- Parsing a retained representative frame restores the same word bound.
The decoded word and the remaining address are portions of actual stored
words, so their numerical values never become a storage charge. -/
theorem readHead_state_bound {base B : ℕ} {word : List Bool}
    {rest : List (List Bool)} {a : Data}
    (hc : FrameCursor base (word::rest) a) (ha : WordBound B a) :
    WordBound B (headState a word (suspendedFrames rest)
      (List.replicate (base+rest.length) true)) := by
  have hword := QueryExecution.cursor_word_length hc ha
  have hrest : (suspendedFrames rest).length≤B := by
    have hh:=ha 840
    rw [hc.frames] at hh
    simp only [SignatureTupleProgram.suspendedFrames,List.flatMap_cons,List.length_append] at hh
    exact (Nat.le_add_left _ _).trans hh
  have haddress : base+rest.length≤B := by
    have hh:=ha 843
    rw [hc.address] at hh
    simp only [List.length_replicate,List.length_cons] at hh
    omega
  intro i
  by_cases h838 : i=838
  · subst i
    rw [(headState_words ..).1]
    exact hword
  by_cases h840 : i=840
  · subst i
    rw [(headState_words ..).2.1]
    exact hrest
  by_cases h843 : i=843
  · subst i
    rw [(headState_words ..).2.2,List.length_replicate]
    exact haddress
  rw [headState_frame _ _ _ _ i h838 h840 h843]
  exact ha i

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleSource
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Shared actual produced input data for the tuple controller and visitor.
The record contains source words, native readiness and paid cache semantics;
it contains no evaluator, resource contract, or successful execution premise. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SignatureTupleProgram SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage


/-- The query snapshot contains every actual loader master. -/
theorem source_master_queryMaster (i : Fin 768) (hi : i∈SignatureHeadLoader.masters) :
    SignatureHeadLoader.lowStacks i∈QueryTupleState.masterPorts := by
  simp only [SignatureHeadLoader.masters, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

theorem source_frame_of_queryFrame (base : LeafHeadSetupProgram.Data)
    (a b : State 40 896)
    (ha : SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hf : QueryTupleState.QueryMasterFrame a b) :
    SignatureHeadLoader.MasterFrame base
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks b) := by
  constructor
  intro i hi
  exact (hf.word (SignatureHeadLoader.lowStacks i) (source_master_queryMaster i hi)).trans
    (ha.stored i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleSource
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete execution of the two representative passes. The saved frame
stack is traversed in place, and every semantic dictionary is the one written
by the actual arithmetic command. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open SubexpSetupStorage LeafHeadSetupProgram
open SubexpLiftRing SubexpQuarticRing MomentsProgram TruncatedRingProgram
open QueryTupleState QueryTupleVisitor SignatureTupleProgram SignatureTupleSource

/-- The whole first pass runs only the concrete addressed loader and overlay.
The list indexes the already emitted polynomial frame stack; no executable
assignment list or callback service occurs in this statement. -/
theorem baseline_pass_oai {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P B : ℕ}
    {a : Data} {pairValue : Truncated (q.p.model.O q.p.t) q.J}
    {tupleValue : Dense (q.p.model.O q.p.t) q.p.t q.J}
    (s : ProducedSource) (base : ℕ) (words : List (List Bool))
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q pairValue a)
    (hv : DenseWord q 852 tupleValue a) (ha : WordBound B a)
    (hs : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hreps : a.stacks 837=suspendedFrames words)
    (haddress : a.stacks 845=unary (base+words.length))
    (hcurrent : a.stacks 838=[]) (hscratch : a.stacks 841=[])
    (hbase : (a.stacks 869).length=s.input.n)
    (hshape : ∀ pre word rest,words=pre++word::rest →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+rest.length)).length)
    (hcap : SignatureHeadLoader.retainedOutputBound s.input.n s.input.N s.input.D
      s.input.columnLength s.bound ≤ B) :
    ∃ steps b, Eval (QueryExecution.replay QueryVisitorProgram.baselineHead) steps a b ∧
      QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
      DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧ WordBound B b ∧
      FrameCursor base [] b ∧ b.stacks 841=[] ∧
      b.stacks 869=QueryRepresentativeFold.run (mask s) base words (a.stacks 869) ∧
      (b.stacks 869).length=s.input.n ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
      steps+1 ≤ 18*B+8*(words.map List.length).sum+(baselineCost s B+10)*words.length+19 ∧
      QueryExecution.PrefixBound (QueryExecution.replay QueryVisitorProgram.baselineHead)
        (steps+1) a (max (896*B+baselineCost s B) (914*B+18)) := by
  let target:=QueryRepresentativeFold.run (mask s) base words (a.stacks 869)
  let I : List (List Bool) → Data → Prop := fun rest b =>
    QueryReady q node H high E U P b ∧ PairAccumulatorMeaning q pairValue b ∧
    DenseWord q 852 tupleValue b ∧ QueryMasterFrame a b ∧
    (∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i) ∧
    (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
    b.stacks 841=[] ∧ (b.stacks 869).length=s.input.n ∧
    QueryRepresentativeFold.run (mask s) base rest (b.stacks 869)=target ∧
    ∀ pre word tail,rest=pre++word::tail →
      word.length=(selectedHeads s.input.n s.input.rows s.input.low (base+tail.length)).length
  have step : ∀ word rest c,FrameCursor base (word::rest) c → I (word::rest) c →
      WordBound B c → ∃ steps b,
      Eval QueryVisitorProgram.baselineHead steps
        (headState c word (suspendedFrames rest) (unary (base+rest.length))) b ∧
      steps ≤ baselineCost s B ∧ b.stacks 838=word ∧ b.stacks 840=suspendedFrames rest ∧
      b.stacks 843=unary (base+rest.length) ∧ I rest (finished b) ∧ WordBound B b ∧
      QueryExecution.PrefixBound QueryVisitorProgram.baselineHead steps
        (headState c word (suspendedFrames rest) (unary (base+rest.length)))
        (896*B+baselineCost s B) := by
    intro word rest c hcursor hI hc
    rcases hI with ⟨hqr,hqm,hqv,hqf,hreg,hports,htmp,hlen,hvalue,hshapes⟩
    let parsed:=headState c word (suspendedFrames rest) (unary (base+rest.length))
    have hpf : QueryMasterFrame c parsed:=QueryVisitorProgram.headState_masterFrame ..
    have hparsed:=QueryVisitorProgram.readHead_state_bound hcursor hc
    have hwords:=headState_words c word (suspendedFrames rest) (unary (base+rest.length))
    have hparseFrame (i : Fin 896) (h838 : i≠838) (h840 : i≠840) (h843 : i≠843) :
        parsed.stacks i=c.stacks i :=
      headState_frame c word (suspendedFrames rest) (unary (base+rest.length)) i h838 h840 h843
    have hnative:=source_frame_of_queryFrame s.masters a parsed hs (hqf.trans hpf)
    obtain ⟨nt,b,he,hbr,hbm,hbv,hbf,hbb,hbaseline,hblen,hbframe,hbregs,ht,hprefix⟩ :=
      baseline_head s (base+rest.length) (hqr.frame hpf)
        (hqm.frame (hparseFrame 851 (by decide) (by decide) (by decide)))
        (hqv.frame (hparseFrame 852 (by decide) (by decide) (by decide))) hparsed hnative
        hwords.2.2 ((hparseFrame 841 (by decide) (by decide) (by decide)).trans htmp)
        (by rw [hwords.1]; exact hshapes [] word rest rfl)
        (by rw [hparseFrame 869 (by decide) (by decide) (by decide)]; exact hlen) hcap
    have hfinish:=QueryVisitorProgram.finishHead_masterFrame b
    have hfinished (i : Fin 896) (hi : i≠838) : (finished b).stacks i=b.stacks i := by
      rw [finished_stacks,Function.update_of_ne hi]
    refine ⟨nt,b,he,ht,?_,?_,?_,?_,hbb,hprefix⟩
    · exact (hbframe 838 (by decide) (by decide)).trans hwords.1
    · exact (hbframe 840 (by decide) (by decide)).trans hwords.2.1
    · exact (hbframe 843 (by decide) (by decide)).trans hwords.2.2
    · refine ⟨hbr.frame hfinish,hbm.frame (hfinished 851 (by decide)),
        hbv.frame (hfinished 852 (by decide)),hqf.trans (hpf.trans (hbf.trans hfinish)),
        ?_,?_,?_,?_,?_,?_⟩
      · intro i hi
        have hpreg:=CommandRegisterFrames.eval_register_frame
          (readHead_frames c word rest base hcursor.frames hcursor.current hcursor.address) i
          (QueryVisitorFrames.readHead_not_mem_writes i hi)
        have hfreg:=CommandRegisterFrames.eval_register_frame (finishHead_eval b) i
          (QueryVisitorFrames.finishHead_not_mem_writes i hi)
        exact hfreg.trans ((hbregs i hi).trans (hpreg.trans (hreg i hi)))
      · intro i hi
        have hn : i≠838 ∧ i≠840 ∧ i≠843 ∧ 768 ≤ i.val ∧
            i∉([846,847,859,869,872,873,874,875,876,877] : List (Fin 896)) := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl|rfl|rfl|rfl
          all_goals decide
        exact (hfinished i hn.1).trans ((hbframe i hn.2.2.2.1 hn.2.2.2.2).trans
          ((hparseFrame i hn.1 hn.2.1 hn.2.2.1).trans (hports i hi)))
      · exact (hfinished 841 (by decide)).trans ((hbframe 841 (by decide) (by decide)).trans
          ((hparseFrame 841 (by decide) (by decide) (by decide)).trans htmp))
      · simpa only [hfinished 869 (by decide)] using hblen
      · rw [hfinished 869 (by decide),hbaseline,hwords.1,
          hparseFrame 869 (by decide) (by decide) (by decide)]
        exact hvalue
      · intro pre next tail htail
        apply hshapes (word::pre) next tail
        simp only [List.cons_append,htail]
  have hstartFrame:=replay_masterFrame a
  have hstart (i : Fin 896) (h840 : i≠840) (h843 : i≠843) :
      (tested (restartState a)).stacks i=a.stacks i := restartState_frame a i h840 h843
  have hI : I words (tested (restartState a)) := by
    refine ⟨hr.frame hstartFrame,hm.frame (hstart 851 (by decide) (by decide)),
      hv.frame (hstart 852 (by decide) (by decide)),hstartFrame,?_,?_,?_,?_,?_,hshape⟩
    · intro i hi
      have hn0 : i≠0 := by intro hh; subst i; simp at hi
      have hn1 : i≠1 := by intro hh; subst i; simp at hi
      have hh:=CommandRegisterFrames.eval_register_frame (restart_eval a hscratch) i
        (QueryVisitorFrames.restart_not_mem_writes i hi)
      exact (StackRoutines.readRegs_frame _ _ _ _ _ hn0 hn1).trans hh
    · intro i hi
      have hn : i≠840 ∧ i≠843 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl|rfl|rfl|rfl
        all_goals decide
      exact hstart i hn.1 hn.2
    · exact (hstart 841 (by decide) (by decide)).trans hscratch
    · simpa only [hstart 869 (by decide) (by decide)] using hbase
    · rw [hstart 869 (by decide) (by decide)]
  obtain ⟨steps,b,he,hcursor,hI,hb,ht,hprefix⟩ :=
    QueryExecution.replay_resources QueryVisitorProgram.baselineHead base (baselineCost s B) B
      (896*B+baselineCost s B) I step words a hreps haddress hcurrent hscratch hI ha
  rcases hI with ⟨hbr,hbm,hbv,hbf,hregs,hports,htmp,hlen,hvalue,_⟩
  exact ⟨steps,b,he,hbr,hbm,hbv,hbf,hb,hcursor,htmp,hvalue,hlen,hports,hregs,ht,hprefix⟩


open scoped BigOperators

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorSemantics.baseline_pass_oai
