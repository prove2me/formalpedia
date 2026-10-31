-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T13:04:21.025401+00:00
-- url     : https://prove2.me/submissions/e0e4133d-060a-4288-82d4-64bea208af5f

import Mathlib
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S190
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleState_finish
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryTupleState_initialize_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_ascend_leaf
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete_setup_rel_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_positive_run_resources
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_setup_masterFrame
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_SignatureTupleRun_zero_run
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_StructuredSpace_local_stack_bound

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ProgramStateFrames
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Reusable data projection and framing for genuine finite subroutine calls.
The projection/embedding functions specify states; executable code uses only
the fixed instruction-port relocation already proved by ProgramLinking. -/

namespace SubexponentialSAT.StructuredCalls

open SubexponentialSAT.BitProgram

/-- Different finite execution derivations of the same structured command
must have the same final data. The existing source port supplies a concrete
compiled machine, and determinism is inherited from its actual transition. -/
theorem Eval.final_unique {r s : ℕ} (port : Fin s) {c : Cmd r s}
    {n m : ℕ} {a b d : State r s} (h : Eval c n a b) (g : Eval c m a d) : b = d := by
  have hb := compiled_halt_trace h port port
  have hd := compiled_halt_trace g port port
  have heq := Computation.RunsIn.terminal_unique
    (show RunsIn (compiled c port port) (n + 1)
      (a.withPC (some (compiled c port port).entry)) (b.withPC none) from
      ⟨n + 1, le_rfl, hb⟩)
    (show RunsIn (compiled c port port) (m + 1)
      (a.withPC (some (compiled c port port).entry)) (d.withPC none) from
      ⟨m + 1, le_rfl, hd⟩)
    (by simp [step, StructuredProgram.State.withPC])
    (by simp [step, StructuredProgram.State.withPC])
  exact congrArg StructuredProgram.State.ofCfg heq

end SubexponentialSAT.StructuredCalls

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


theorem not_mem_liftCommand {r s R S : ℕ} (c : StructuredCalls.Cmd r s)
    (input output : Fin s) (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (i : Fin R) (hi : ¬ ∃ j, register j = i) :
    i ∉ writes (StructuredCalls.liftCommand c input output register stack) :=
  not_mem_liftProgram _ register stack i hi

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StreamResources
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeJoint _root_.OAI.Algorithms.SubexponentialSAT.MulticolorTypes.instFintypeSide _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Uniform storage rules for concrete streaming loops. A local runtime bound
is used only for one invocation whose entire initial storage is uniformly
bounded; neither bound depends on the number of loop iterations. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources

open BitProgram

/-- Summing the port bounds counts every simultaneously live buffer. -/
theorem dataBits_le_mul {r s l bound : ℕ} (c : Cfg r s l)
    (h : ∀ i, (c.stacks i).length ≤ bound) : dataBits c ≤ s * bound := by
  simpa [dataBits, stackBits] using Finset.sum_le_card_nsmul Finset.univ
    (fun i => (c.stacks i).length) bound (fun i _ => h i)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StreamResources
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

theorem Iteration.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Iteration p q n a b) : Eval (body p q) n a b := by
  cases h with
  | leaf hl hv ha => exact .ite_true hl (.seq hv ha)
  | fresh hl hp hb hf hd =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_true hf hd)))
  | duplicate hl hp hb hf hn =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_true hb (Eval.ite_false hf hn)))
  | exhausted hl hp hb ha =>
      simpa only [body, Nat.add_assoc, Nat.reduceAdd] using
        Eval.ite_false (yes := .seq q.visit q.ascend) hl
          (Eval.seq hp (Eval.ite_false hb ha))

theorem Traversal.eval {r s : ℕ} {p : Ports r} {q : Routines r s}
    {n : ℕ} {a b : State r s} (h : Traversal p q n a b) : Eval (loop p q) n a b := by
  induction h with
  | done ha => exact .while_false ha
  | step ha hi _ ih => exact .while_true ha hi.eval ih

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

theorem tested_empty (a : Data) (h : a.stacks 840 = []) : (tested a).regs 1 = false := by
  simp [tested,readRegs,h]

/-- Repeated passes retain the same word bound: overwrite replaces one word,
rather than appending to a growing visit history. -/
theorem overwriteState_bound (src dst : Fin 896) (hsd : src ≠ dst)
    (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((overwriteState src dst a).stacks i).length ≤ B := by
  intro i
  rw [overwriteState_stacks src dst hsd]
  by_cases hi : i = dst
  · subst i
    rw [Function.update_self]
    exact hb src
  · rw [Function.update_of_ne hi]
    exact hb i

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

theorem restartState_words (a : Data) :
    (restartState a).stacks 840 = a.stacks 837 ∧
      (restartState a).stacks 843 = a.stacks 845 := by
  have h1 := overwriteState_stacks 837 840 (by decide) a
  have h2 := overwriteState_stacks 845 843 (by decide) (overwriteState 837 840 a)
  change (overwriteState 845 843 (overwriteState 837 840 a)).stacks 840 = a.stacks 837 ∧
    (overwriteState 845 843 (overwriteState 837 840 a)).stacks 843 = a.stacks 845
  rw [h2,h1]
  simp

theorem restartState_frame (a : Data) (i : Fin 896) (h840 : i ≠ 840) (h843 : i ≠ 843) :
    (restartState a).stacks i = a.stacks i := by
  rw [restartState,overwriteState_frame _ _ (by decide) _ _ h843,
    overwriteState_frame _ _ (by decide) _ _ h840]

theorem restartState_bound (a : Data) (B : ℕ) (hb : ∀ i, (a.stacks i).length ≤ B) :
    ∀ i, ((restartState a).stacks i).length ≤ B :=
  overwriteState_bound 845 843 (by decide) _ B
    (overwriteState_bound 837 840 (by decide) a B hb)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleVisitor
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryTupleInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete initialization of one attained-signature tuple product. The
multiplicative identity is built by the native cache routine, and every stale
output and borrowed word is cleared by an actual command. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit

open OAI BitProgram StructuredCalls SubexpSetupStorage
open SqrtLog SqrtLog.LeafProgram


open CommandRegisterFrames

/-- Caller flags above the sixteen-register cache bank survive every actual
prefix, including all guarded calls and clearing steps. -/
theorem command_not_mem_writes (i : Fin 40) (hi : 16 ≤ i.val) : i ∉ writes command := by
  have hout : ¬ ∃ j, FactorAssignmentProgram.localRegister j = i := by
    rintro ⟨j, hj⟩
    have hv := congrArg Fin.val hj
    change j.val = i.val at hv
    have := j.isLt
    omega
  have h0 : i ≠ 0 := by intro h; subst i; omega
  have h1 : i ≠ 1 := by intro h; subst i; omega
  have hclear (ports : List (Fin 896)) : i ∉ writes (clearBank ports) :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have hsetup : i ∉ writes FactorAssignmentProgram.setup :=
    not_mem_liftCommand _ _ _ _ _ i hout
  have union_not_mem {s t : Finset (Fin 40)} (hs : i ∉ s) (ht : i ∉ t) : i ∉ s ∪ t := by
    simpa only [Finset.mem_union, not_or] using And.intro hs ht
  have hoverwrite (src dst : Fin 896) : i ∉ writes (QueryTupleVisitor.overwrite src dst) :=
    union_not_mem (not_mem_clearProgram dst 0 1 i h0 h1)
      (not_mem_copyProgram src dst 841 0 1 i h0 h1)
  exact union_not_mem (hclear entryPorts)
    (union_not_mem hsetup (union_not_mem (hoverwrite 69 852)
      (union_not_mem (hoverwrite 703 869) (hclear lowPorts))))

theorem command_register_frame {steps : ℕ} {a b : Data}
    (he : Eval command steps a b) (i : Fin 40) (hi : 16 ≤ i.val) : b.regs i = a.regs i :=
  eval_register_frame he i (command_not_mem_writes i hi)

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryTupleInit
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

theorem PrefixBound.mono {command : Code} {steps B D : ℕ} {a : Data}
    (h : PrefixBound command steps a B) (hBD : B ≤ D) :
    PrefixBound command steps a D :=
  ⟨fun q z hq hz i => (h.bound q z hq hz i).trans hBD⟩

theorem prefix_local (command : Code) (steps B : ℕ) (a : Data)
    (ha : ∀ i, (a.stacks i).length ≤ B) :
    PrefixBound command steps a (896*B+steps) := by
  constructor
  exact StructuredSpace.local_stack_bound (compiled command 838 838)
    (StreamResources.dataBits_le_mul _ ha)

/-- Zero heads execute the real copy/test/halt path and invoke no head work.
In particular the repeated-pair base address649 is retained on this edge case. -/
theorem replay_nil (work : Code) (a : Data)
    (hreps : a.stacks 837=[]) (hscratch : a.stacks 841=[]) :
    Eval (replay work) (restartCost a+2) a (tested (restartState a)) ∧
      (tested (restartState a)).stacks 649=a.stacks 649 := by
  have hr := restart_eval a hscratch
  have ht := testFrames_eval (restartState a)
  have hf : (restartState a).stacks 840=[] := (restartState_words a).1.trans hreps
  have hl : Eval (headLoop work) 1 (tested (restartState a)) (tested (restartState a)) :=
    Eval.while_false (tested_empty _ hf)
  refine ⟨?_,restartState_frame a 649 (by decide) (by decide)⟩
  simpa only [replay, show restartCost a+(1+1)=restartCost a+2 by omega] using
    hr.seq (ht.seq hl)

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

namespace PairAccumulatorMeaning

theorem frame {r Q n d : ℕ} {q : Factor.Spec r Q n d}
    {value : Truncated (q.p.model.O q.p.t) q.J} {a b : Data}
    (h : PairAccumulatorMeaning q value a) (hf : b.stacks 851=a.stacks 851) :
    PairAccumulatorMeaning q value b := by
  obtain ⟨entries,he,hg,hv⟩ := h.entries
  exact ⟨entries,hf.trans he,hg,hv⟩

end PairAccumulatorMeaning

/-- Actual cache initialization changes no retained query input. -/
theorem initialized_masterFrame {a b : Data} {n width d u J : ℕ}
    {one : RingProgram.Code (Word width) d}
    (h : QueryTupleInit.Initialized a b (n:=n) one u J) : QueryMasterFrame a b := by
  constructor
  intro i hi
  apply h.frame i
  simp only [masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals decide

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

private theorem emptyReplayCost (a : Data) (B : ℕ) (ha : WordBound B a) :
    restartCost a+2≤18*B+18 := by
  have h1:=ha 840
  have h2:=ha 837
  have h3:=ha 843
  have h4:=ha 845
  unfold restartCost
  omega

private theorem emptyReplay_registers (a : Data) (h : a.stacks 841=[]) (i : Fin 40)
    (hi : 16≤ i.val) : (tested (restartState a)).regs i=a.regs i := by
  have h0 : i≠0 := by intro he; subst i; simp at hi
  have h1 : i≠1 := by intro he; subst i; simp at hi
  have hr := CommandRegisterFrames.eval_register_frame (restart_eval a h) i
    (QueryVisitorFrames.restart_not_mem_writes i hi)
  exact (StackRoutines.readRegs_frame _ _ _ _ _ h0 h1).trans hr

/-- With no emitted heads the fixed visitor still constructs and contributes
the ring unit. Both real replay paths and the real normalization tail execute;
there is no empty-formula Boolean shortcut. -/
theorem visitor_empty {r Q n d : ℕ} {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)}
    {P B : ℕ} {a : Data} {value : Truncated (q.p.model.O q.p.t) q.J}
    (hr : QueryReady q node H high E U P a) (hm : PairAccumulatorMeaning q value a)
    (ha : WordBound B a) (hPB : 4*P+6≤B) (hreps : a.stacks 837=[])
    (hcap : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2)≤B) :
    ∃ steps b, Eval visitor steps a b ∧ QueryReady q node H high E U P b ∧
      PairAccumulatorMeaning q (value+Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J)) b ∧
      WordBound B b ∧ QueryMasterFrame a b ∧
      (∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i) ∧
      (∀ i,16≤ i.val → b.regs i=a.regs i) ∧
      (∀ i∈SignatureTupleProgram.currentHeadPorts,b.stacks i=[]) ∧
      b.stacks 649=a.stacks 649 ∧
      steps+1≤QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1) ∧
      QueryExecution.PrefixBound visitor (steps+1) a
        (896*B+QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1)) := by
  obtain ⟨nt,a1,ht,hr1,hm1,hi,hb1,hcost1,entries,he,hg,hv⟩ :=
    QueryTupleState.initialize_run hr hm ha hPB
  have hreps1 : a1.stacks 837=[] := (hi.frame 837 (by decide)).trans hreps
  have hpass1 := QueryExecution.replay_nil baselineHead a1 hreps1 hi.scratch
  let a2 := tested (restartState a1)
  have hf2 (i : Fin 896) (h840 : i≠840) (h843 : i≠843) : a2.stacks i=a1.stacks i :=
    restartState_frame a1 i h840 h843
  have hb2 : WordBound B a2 := restartState_bound a1 B hb1
  have hr2 : QueryReady q node H high E U P a2 := hr1.frame (replay_masterFrame a1)
  have hm2 : PairAccumulatorMeaning q value a2 := hm1.frame (hf2 851 (by decide) (by decide))
  have hreps2 : a2.stacks 837=[] := (hf2 837 (by decide) (by decide)).trans hreps1
  have hscratch2 : a2.stacks 841=[] := (hf2 841 (by decide) (by decide)).trans hi.scratch
  have hpass2 := QueryExecution.replay_nil evaluateHead a2 hreps2 hscratch2
  let a3 := tested (restartState a2)
  have hf3 (i : Fin 896) (h840 : i≠840) (h843 : i≠843) : a3.stacks i=a2.stacks i :=
    restartState_frame a2 i h840 h843
  have hb3 : WordBound B a3 := restartState_bound a2 B hb2
  have hr3 : QueryReady q node H high E U P a3 := hr2.frame (replay_masterFrame a2)
  have hm3 : PairAccumulatorMeaning q value a3 := hm2.frame (hf3 851 (by decide) (by decide))
  have he3 : a3.stacks 852=Product.bytes entries :=
    (hf3 852 (by decide) (by decide)).trans ((hf2 852 (by decide) (by decide)).trans he)
  obtain ⟨nf,b,hfinish,hrb,hmb,hbb,hmasters,hcurrent,hframe,hregs,hcostf⟩ :=
    QueryTupleState.finish hr3 hm3 entries hg he3 hb3 hcap
  have heval : Eval visitor (nt+(restartCost a1+2+(restartCost a2+2+nf))) a b :=
    ht.seq (hpass1.1.seq (hpass2.1.seq hfinish))
  have hcost2 := emptyReplayCost a1 B hb1
  have hcost3 := emptyReplayCost a2 B hb2
  have hcost : nt+(restartCost a1+2+(restartCost a2+2+nf))+1≤
      QueryTupleSum.budget n (baseWidth 3 q.p.t) d q.p.t q.J B+1600*(B+1) := by omega
  refine ⟨_,b,heval,hrb,?_,hbb,?_,?_,?_,hcurrent,?_,hcost,?_⟩
  · simpa only [hv] using hmb
  · exact (initialized_masterFrame hi).trans
      ((replay_masterFrame a1).trans ((replay_masterFrame a2).trans hmasters))
  · intro i hi'
    have hs : 128≤ i.val ∧ i∉SignatureTupleProgram.currentHeadPorts ∧ i≠851 ∧ i≠852 ∧
        i≠840 ∧ i≠843 ∧ i∉QueryTupleInit.changed := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi'
      rcases hi' with rfl|rfl|rfl|rfl
      all_goals decide
    exact (hframe i hs.1 hs.2.1 hs.2.2.1 hs.2.2.2.1).trans
      ((hf3 i hs.2.2.2.2.1 hs.2.2.2.2.2.1).trans
        ((hf2 i hs.2.2.2.2.1 hs.2.2.2.2.2.1).trans (hi.frame i hs.2.2.2.2.2.2)))
  · intro i hi'
    exact (hregs i hi').trans ((emptyReplay_registers a2 hscratch2 i hi').trans
      ((emptyReplay_registers a1 hi.scratch i hi').trans
        (QueryTupleInit.command_register_frame ht i hi')))
  · exact (hframe 649 (by decide) (by decide) (by decide) (by decide)).trans
      ((hf3 649 (by decide) (by decide)).trans
        ((hf2 649 (by decide) (by decide)).trans (hi.frame 649 (by decide))))
  · exact (QueryExecution.prefix_local visitor _ B a ha).mono (by omega)


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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleComplete
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete cursor invariants for the fixed attained-signature controller.
The integer head matrices come from native source words.  Each boundary uses
one retained cap; reload and predecessor-scan prefix bounds remain transient.
-/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete

open Classical
open OAI.Algorithms.SubexponentialSAT.SubexpLiftRing
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource

theorem Boundary.wordBound {s : ProducedSource} {F : ℕ}
    {cursor : Cursor s.key s.input.r} {a : State 40 896}
    (ha : Boundary s F cursor a) : WordBound F a := by
  cases ha with
  | scan hs => exact hs.bound
  | leaf hs => exact hs.bound
  | halt hs => exact hs.bound


theorem leave_zero (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels : ℕ)
    (hz : levels=0) (ancestors : Prefix (Representatives key) levels) :
    leave key levels levels le_rfl ancestors=Cursor.halt := by
  subst levels
  rfl

theorem queryMaster_persistent (i : Fin 896) (hi : i∈QueryTupleState.masterPorts) :
    PersistentPort i := by
  simp only [QueryTupleState.masterPorts,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals exact ⟨by decide,by decide,by decide⟩

theorem query_frame_of_persistent (a b : State 40 896)
    (hf : ∀ i,PersistentPort i → b.stacks i=a.stacks i) :
    QueryTupleState.QueryMasterFrame a b :=
  ⟨fun i hi => hf i (queryMaster_persistent i hi)⟩

theorem leafStorage_frame (h : ℕ → ℕ) {κ : ℕ → Type*}
    (key : (d : ℕ) → Fin (2^h d) → κ d) (levels base : ℕ)
    (ancestors : Prefix (Representatives key) levels) (a b : State 40 896)
    (ha : LeafStorage h key levels base ancestors a)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[]) :
    LeafStorage h key levels base ancestors b := by
  refine ⟨⟨ha.depth_le,?_,?_,?_,?_,?_⟩,?_,hc⟩
  · exact (hf 836 (by decide)).trans ha.cursors
  · exact (hf 837 (by decide)).trans ha.representatives
  · exact (hf 842 (by decide)).trans ha.heads
  · exact (hf 845 (by decide)).trans ha.address
  · exact (hr 36 (by decide)).trans ha.active
  · exact (hr 37 (by decide)).trans ha.leaf

theorem leafBoundary_frame (s : ProducedSource) (F : ℕ)
    (ancestors : Prefix (Representatives s.key) s.input.r) (a b : State 40 896)
    (ha : LeafBoundary s F ancestors a) (hb : WordBound F b)
    (hm : QueryTupleState.QueryMasterFrame a b)
    (hf : ∀ i∈([836,837,842,845] : List (Fin 896)),b.stacks i=a.stacks i)
    (hr : ∀ i : Fin 40,16 ≤ i.val → b.regs i=a.regs i)
    (hc : ∀ i∈currentHeadPorts,b.stacks i=[])
    (hz : s.input.r=0 → b.stacks 649=a.stacks 649) : LeafBoundary s F ancestors b := by
  exact ⟨leafStorage_frame s.headSize s.key s.input.r s.base ancestors a b
    ha.toLeafStorage hf hr hc,hb,source_frame_of_queryFrame s.masters a b ha.masters hm,
    fun hzero => (hz hzero).trans (ha.zero_address649 hzero)⟩

/-- At completed traversal, the actual root flag is false and low649 again
contains the original node base for the next finite-difference pair. -/
theorem Rel.halted {s : ProducedSource} {F r Q n d : ℕ}
    {q : LeafProgram.Factor.Spec r Q n d} {node : Fin Q}
    {H : Finset (Fin n)} {high : H → Bool} {E U : Finset (Fin n)} {P : ℕ}
    {acc : Truncated (q.p.model.O q.p.t) q.J} {a : State 40 896}
    (ha : Rel s F q node H high E U P .halt acc a) :
    a.regs controllerPorts.active=false ∧ a.stacks 649=unary s.base := by
  cases ha.boundary with
  | halt hb => exact ⟨hb.active,hb.address649⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleComplete
end
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_SignatureTupleRun
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Complete runs of the fixed attained-signature controller. The retained
boundary cap is separate from transient prefix storage and measured time. -/
noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun

open Classical
open OAI SubexpLiftRing BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage
open SignatureTupleDFS SignatureTupleTraversal SignatureTupleProgram
open SignatureTupleNative SignatureTupleRefinement SignatureTupleLoader SignatureTupleSource
open SignatureTupleComplete

/-- Source port selectors only choose external readback; they do not change
any instruction or stack in an internal command trace. -/
theorem prefix_ports (code : Cmd 40 896) (steps bound : ℕ) (a : State 40 896)
    (h : QueryExecution.PrefixBound code steps a bound) (input output : Fin 896) :
    ∀ p z,p ≤ steps → BitProgram.Trace (compiled code input output) p
      (a.withPC (some (compiled code input output).entry)) z →
      ∀ i,(z.stacks i).length ≤ bound := by
  intro p z hp hz i
  exact h.bound p z hp hz i

/-- The zero-head execution also preserves all84 immutable query words;
in particular the next pair can reuse850 and832..835 verbatim. -/
theorem zero_run_masterFrame (s : ProducedSource) (F : ℕ) (cap : RetainedCap s F)
    {r Q n d : ℕ} (q : LeafProgram.Factor.Spec r Q n d) (node : Fin Q)
    (H : Finset (Fin n)) (high : H → Bool) (E U : Finset (Fin n)) (P : ℕ)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hzero : s.input.r=0) (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q node H high E U P a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) (hPF : 4*P+6 ≤ F)
    (hout : q.p.t*q.J*(2*(q.p.t+q.J+n)+2*(d*baseWidth 3 q.p.t)+2) ≤ F)
    {steps : ℕ} {out : State 40 896} (he : Eval SignatureTupleComplete.command steps a out) :
    QueryTupleState.QueryMasterFrame a out := by
  obtain ⟨ns,b,hs,hb,_,_⟩ := setup_rel_run s F cap q node H high E U P acc a
    hbound hm hz hquery hacc
  have hsetup := setup_masterFrame s F cap a hbound hm hz hs
  rw [enter,dite_eq_left hzero.symm] at hb
  cases hboundary : hb.boundary with
  | leaf hl =>
    have hreps : b.stacks 837=[] := by
      change b.stacks (tupleStacks 1)=[]
      rw [hl.representatives]
      simp only [representativeFrames,representativeWords,hzero,List.ofFn_zero,
        List.reverse_nil,suspendedFrames,List.flatMap_nil]
    obtain ⟨nv,c,hvisit,_,_,hc,hmasters,hframes,hregs,hcurrent,h649,_,_⟩ :=
      QueryVisitorProgram.visitor_empty hb.query hb.accumulator hl.bound hPF hreps hout
    have hleaf := leafBoundary_frame s F _ b c hl hc hmasters hframes hregs hcurrent
      (fun _ => h649)
    obtain ⟨na,e,hasc,hhalt,_,_,hframe⟩ := ascend_leaf s F cap _ c hleaf
    have hterminal : Boundary s F Cursor.halt e := by
      simpa only [leave_zero s.headSize s.key s.input.r hzero] using hhalt
    have hflag : e.regs controllerPorts.active=false := by
      cases hterminal with
      | halt h => exact h.active
    have hit : Iteration controllerPorts routines (nv+na+1) b e :=
      .leaf hl.leaf hvisit hasc
    have ht : Traversal controllerPorts routines (nv+na+1+1+1) b e :=
      .step (n := nv+na+1) (m := 1) hl.active hit (.done hflag)
    have hall : Eval SignatureTupleComplete.command (ns+(nv+na+1+1+1)) a e :=
      .seq hs ht.eval
    have hfinal := he.final_unique (0 : Fin 896) hall
    subst e
    exact hsetup.trans (hmasters.trans (query_frame_of_persistent c out hframe))

theorem zero_total (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (hz : s.input.r=0) :
    tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)=
      Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J) := by
  let : IsEmpty (Fin s.input.r) := ⟨fun i => by have := i.isLt; omega⟩
  have hv (ancestors : Prefix (Representatives s.key) s.input.r) :
      emittedValue s q H E U high owner head facts ancestors=
        Dense.readout (1 : Dense (q.p.model.O q.p.t) q.p.t q.J) := by
    unfold emittedValue
    simp
  unfold tupleTotal
  simp only [hv]
  simp

theorem tupleCount_zero {N : ℕ → ℕ} {κ : ℕ → Type*}
    (key : (depth : ℕ) → Fin (N depth) → κ depth) : tupleCount key 0=1 := by
  simp only [tupleCount,prefixCount,Finset.range_zero,Finset.prod_empty]

/-- The common event budget specializes to exactly the paid empty-tuple
execution, including its return and terminal guard. -/
theorem zero_runTime (s : ProducedSource) {d : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d) (F S Z B height : ℕ)
    (hzero : s.input.r=0) :
    QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+
      1600*(F+1)+2*eventPolynomial s F+2=runTime s q F S Z B height := by
  have hk : tupleCount s.key s.input.r=1 :=
    (congrArg (tupleCount s.key) hzero).trans (tupleCount_zero s.key)
  have arithmetic (p r K power tail rest : ℕ) (hr : r=0) (hK : K=1) :
      tail+2*p+2=p+(2*p)*r*K*power+K*(tail+rest*r+p)+2 := by
    subst r
    subst K
    omega
  exact arithmetic (eventPolynomial s F) s.input.r (tupleCount s.key s.input.r) (4^height)
    (QueryTupleSum.budget s.input.n (baseWidth 3 q.p.t) d q.p.t q.J F+1600*(F+1))
    (QueryVisitorSemantics.baselineCost s F+QueryVisitorSemantics.evaluationCost s q F S Z B height+20)
    hzero hk

/-- Unified actual tuple execution, including the unique empty tuple.
The exact same851 meaning and retained cap support repeated finite-difference
pairs; all master words, including850 and832..835, are preserved. -/
theorem run_resources_oai (s : ProducedSource) {d M F S Z B width height : ℕ}
    (q : LeafProgram.Factor.Spec s.input.r s.input.Q s.input.n d)
    (H E U : Finset (Fin s.input.n)) (high : H → Bool)
    (owner : Fin q.ps.length → Fin s.input.n)
    (head : Fin s.input.Q → Fin s.input.n → Fin s.input.r)
    (facts : QueryVisitorHead.SourceFacts s.input q H owner s.owner head)
    (caps : QueryVisitorHead.HeadBounds s.input q M F S Z B s.bound width)
    (cap : RetainedCap s F) (hheads : ∀ depth < s.input.r,s.headSize depth ≤ height)
    (acc : Truncated (q.p.model.O q.p.t) q.J) (a : State 40 896)
    (hbound : WordBound F a)
    (hm : SignatureHeadLoader.MasterFrame s.masters
      (projectState SignatureHeadLoader.leafRegs SignatureHeadLoader.lowStacks a))
    (hz : a.stacks 649=unary s.base)
    (hquery : QueryTupleState.QueryReady q s.input.node H high E U M a)
    (hacc : QueryTupleState.PairAccumulatorMeaning q acc a) :
    ∃ steps b, Eval SignatureTupleComplete.command steps a b ∧
      BitProgram.Trace SignatureTupleComplete.program (steps+1)
        (a.withPC (some SignatureTupleComplete.program.entry)) (b.withPC none) ∧
      QueryTupleState.QueryReady q s.input.node H high E U M b ∧
      QueryTupleState.PairAccumulatorMeaning q
        (acc+tupleTotal s.key s.input.r (emittedValue s q H E U high owner head facts)) b ∧
      WordBound F b ∧ b.stacks 649=unary s.base ∧ QueryTupleState.QueryMasterFrame a b ∧
      steps+1 ≤ runTime s q F S Z B height ∧
      ∀ elapsed cfg,elapsed ≤ steps+1 → BitProgram.Trace SignatureTupleComplete.program elapsed
        (a.withPC (some SignatureTupleComplete.program.entry)) cfg →
        ∀ i,(cfg.stacks i).length ≤ completeSpace s q F B := by
  by_cases hzero : s.input.r=0
  · obtain ⟨steps,b,he,hb,ht,htrace,hspace⟩ :=
      zero_run s F cap q s.input.node H high E U M acc a hzero hbound hm hz hquery hacc
        caps.cache caps.multiply
    have hframe := zero_run_masterFrame s F cap q s.input.node H high E U M acc a hzero
      hbound hm hz hquery hacc caps.cache caps.multiply he
    have htotal := zero_total s q H E U high owner head facts hzero
    have htime := zero_runTime s q F S Z B height hzero
    refine ⟨steps,b,he,htrace,hb.query,?_,hb.boundary.wordBound,hb.halted.2,hframe,
      ht.trans htime.le,?_⟩
    · simpa only [htotal] using hb.accumulator
    · intro elapsed cfg helapsed htrace i
      apply (prefix_ports SignatureTupleComplete.command _ _ a hspace 837 851
        elapsed cfg helapsed htrace i).trans
      apply max_le
      · exact (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
      · exact Nat.le_max_right _ _
  · obtain ⟨steps,b,he,htrace,hqr,hacc,hb,h649,hframe,ht,hspace⟩ :=
      positive_run_resources s q H E U high owner head facts caps cap (Nat.pos_of_ne_zero hzero)
        hheads acc a hbound hm hz hquery hacc
    exact ⟨steps,b,he,htrace,hqr,hacc,hb,h649,hframe,ht,fun elapsed cfg helapsed htrace i =>
      (hspace elapsed cfg helapsed htrace i).trans (Nat.le_max_left _ _)⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.SignatureTupleRun.run_resources_oai
