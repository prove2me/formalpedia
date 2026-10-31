-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:36:16.367008+00:00
-- url     : https://prove2.me/submissions/b593ac4d-cb37-4c2a-a752-1c9c51789edb

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S165
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighCountSeed_initialize_trace_space

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

theorem clearBankStacks_frame {S : Type u} [DecidableEq S]
    (j : S) (ports : List S) (stk : Stacks S) (hj : j ∉ ports) :
    clearBankStacks ports stk j = stk j := by
  simp [clearBankStacks, hj]

theorem clearStacks_eq_self_of_empty {S : Type u} [DecidableEq S]
    (tmp : S) (stk : Stacks S) (htmp : stk tmp = []) :
    clearStacks tmp stk = stk := by
  funext j
  by_cases hj : j = tmp
  · subst j
    simp [htmp]
  · exact clearStacks_frame _ _ _ hj

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

/-- Exact clearing cost in terms of the original word lengths.  The temporary
may also occur in the bank: its initial emptiness makes the final clear cost
exactly three instructions in either case. -/
theorem clear_eval {r s : ℕ} (tmp : Fin s) (value present : Fin r)
    (ports : List (Fin s)) (hports : ports.Nodup)
    (regs : Fin r → Bool) (stk : Stacks (Fin s)) (htmpEmpty : stk tmp = []) :
    Eval (clearCmd tmp value present ports)
      (2 * (ports.map (fun j => (stk j).length)).sum + 3 * ports.length + 3)
      ⟨regs, stk⟩ ⟨readRegs regs value present none, clearBankStacks ports stk⟩ := by
  induction ports generalizing regs stk with
  | nil =>
      have run := clear_call_eval tmp value present regs stk
      simpa [clearCmd, htmpEmpty, clearStacks_eq_self_of_empty tmp stk htmpEmpty] using run
  | cons dst ports ih =>
      have hn := List.nodup_cons.mp hports
      have htemp : clearStacks dst stk tmp = [] := by
        by_cases h : tmp = dst
        · subst tmp
          simp
        · rw [clearStacks_frame dst tmp stk h, htmpEmpty]
      have hmap : ports.map (fun j => (clearStacks dst stk j).length) =
          ports.map (fun j => (stk j).length) := by
        apply List.map_congr_left
        intro j hj
        have hjd : j ≠ dst := by
          intro h
          subst j
          exact hn.1 hj
        rw [clearStacks_frame dst j stk hjd]
      have first := clear_call_eval dst value present regs stk
      have rest := ih hn.2 (readRegs regs value present none)
        (clearStacks dst stk) htemp
      have run := Eval.seq first rest
      simpa only [clearCmd, List.map_cons, List.sum_cons, List.length_cons,
        hmap, readRegs_reset, clearBankStacks_cons, Nat.mul_add,
        Nat.mul_one, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using run

end SubexponentialSAT.BankRoutines

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_ExecCNFTupleOdometer
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-!
# Fixed-control increment of framed binary tuples

Tuple components are little-endian Boolean words carried by
`Encoding.encodeList id`. The finite table below skips framing bits and
increments only payload bits, with carry continuing into the next component.
Neither the number of components nor their widths enters the control table.
-/

namespace SubexponentialSAT.ExecCNFTupleOdometer

open SubexponentialSAT.BitProgram SubexponentialSAT.CounterPrograms

theorem encoded_length (words : List (List Bool)) :
    (Encoding.encodeList id words).length =
      2 * words.flatten.length + 2 * words.length + 1 := by
  induction words with
  | nil => rfl
  | cons word words ih =>
    rw [Encoding.length_encodeList_cons]
    simp only [id_eq, List.flatten_cons, List.length_append, List.length_cons]
    omega

end SubexponentialSAT.ExecCNFTupleOdometer

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_StructuredSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Prefix resource preservation for the actual finite instruction linker.
The source bound concerns every intermediate configuration. Unassigned caller
stacks retain their original contents. Local runtime bounds may be used for
polynomial subroutines, but no accumulated outer-loop time appears here. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace

open BitProgram

/-- Every prefix of a relocated source execution is exactly the relocation of
the same-length source prefix, including a halt changed to a return jump. -/
theorem relocate_trace_prefix {r s l R S L : ℕ}
    (p : Program r s l) (q : Program R S L)
    (register : Fin r → Fin R) (stack : Fin s → Fin S)
    (label : Fin l → Fin L) (returnPc : Option (Fin L)) (frame : Cfg R S L)
    (hregister : Function.Injective register) (hstack : Function.Injective stack)
    (hcode : ProgramLinking.CodeEmbedding p q register stack label returnPc)
    {steps prefixSteps : ℕ} {a b : Cfg r s l}
    (tr : Trace p steps a b) {intermediate : Cfg R S L}
    (hle : prefixSteps ≤ steps)
    (hp : Trace q prefixSteps
      (ProgramLinking.embedCfg register stack label returnPc frame a) intermediate) :
    ∃ source, Trace p prefixSteps a source ∧
      intermediate = ProgramLinking.embedCfg register stack label returnPc frame source := by
  obtain ⟨source, hsource⟩ := trace_prefix_exists tr hle
  refine ⟨source, hsource, ?_⟩
  exact trace_same_length_unique hp
    (ProgramLinking.relocate_trace p q register stack label returnPc frame
      hregister hstack hcode hsource)

/-- A structured call retains its callee's every-prefix stack bound in the
actual caller table. The table premise is the same one used by eval_trace. -/
theorem call_stack_bound {r s l L : ℕ} (routine : Program r s l)
    (caller : Program r s L) (label : Fin l → Fin L) (exit : Fin L)
    (hcode : ∀ pc, caller.code (label pc) =
      StructuredCalls.code (.call routine) label exit pc)
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (tr : Trace routine steps (a.withPC (some routine.entry)) (b.withPC none))
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace routine prefixSteps (a.withPC (some routine.entry)) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace caller prefixSteps (a.withPC (some (label routine.entry))) intermediate →
      ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp i
  have hinitial : ProgramLinking.embedCfg id id label (some exit)
      (a.withPC (some (label routine.entry))) (a.withPC (some routine.entry)) =
      a.withPC (some (label routine.entry)) := by
    simp [ProgramLinking.embedCfg, ProgramLinking.relocatePc,
      StructuredProgram.State.withPC]
  rw [← hinitial] at hp
  obtain ⟨source, hs, rfl⟩ := relocate_trace_prefix routine caller id id label
    (some exit) (a.withPC (some (label routine.entry)))
    Function.injective_id Function.injective_id hcode tr hle hp
  simpa [ProgramLinking.embedCfg] using hsource prefixSteps source hle hs i

/-- The final concrete halt instruction changes no stack and preserves the
bound already established through the command's exit boundary. -/
theorem compiled_halt_stack_bound {r s : ℕ} {command : StructuredCalls.Cmd r s}
    {steps bound : ℕ} {a b : StructuredCalls.State r s}
    (heval : StructuredCalls.Eval command steps a b) (inputStack outputStack : Fin s)
    (hsource : ∀ prefixSteps intermediate, prefixSteps ≤ steps →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound) :
    ∀ prefixSteps intermediate, prefixSteps ≤ steps + 1 →
      Trace (StructuredCalls.compiled command inputStack outputStack) prefixSteps
        (a.withPC (some (StructuredCalls.compiled command inputStack outputStack).entry))
        intermediate → ∀ i, (intermediate.stacks i).length ≤ bound := by
  intro prefixSteps intermediate hle hp
  by_cases hbefore : prefixSteps ≤ steps
  · exact hsource prefixSteps intermediate hbefore hp
  · have hlast : prefixSteps = steps + 1 := by omega
    subst prefixSteps
    have heq := trace_same_length_unique hp
      (StructuredCalls.compiled_halt_trace heval inputStack outputStack)
    rw [heq]
    have hend := hsource steps (b.withPC (some (StructuredCalls.exitAddress command))) le_rfl
      (StructuredCalls.compiled_trace heval inputStack outputStack)
    exact hend

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.StructuredSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramBranches
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Runtime Boolean branch initialization and exhaustive odometer traces.
The only parameter in the enumeration command is its fixed real callback.
The high dimension is data, not finite control. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

theorem push_eval (b : Bool) (a : Data) : Eval (push b) 2 a (pushed b a) := by
  have h := (Eval.base (StructuredProgram.Eval.atom (.set (0 : Fin 2) b) a)).seq
    (Eval.base (StructuredProgram.Eval.atom (.push (1 : Fin 2) 0) _))
  simpa [push, pushed, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using h

theorem record_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    Eval record 8 (state regs mask out)
      (state (Function.update regs 0 true) mask (true :: true :: false :: false :: out)) := by
  let a := state regs mask out
  have h := (push_eval false a).seq ((push_eval false (pushed false a)).seq
    ((push_eval true (pushed false (pushed false a))).seq
      (push_eval true (pushed true (pushed false (pushed false a))))))
  simpa [record, pushed, a, state, Function.update_idem] using h

theorem pop_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    Eval pop 1 (state regs mask out) (popped regs mask out) := by
  simpa [pop, state, popped, StructuredProgram.Atom.eval, StructuredProgram.Atom.instr,
    StructuredProgram.State.ofCfg, StructuredProgram.State.withPC, execInstr] using
    (Eval.base (StructuredProgram.Eval.atom (.pop (0 : Fin 2) 0 1) (state regs mask out)))

theorem prepend_step (h : ℕ) (out : List Bool) :
    prepend h (true :: true :: false :: false :: out) = prepend (h+1) out := by
  induction h <;> simp [prepend, *]

theorem loop_eval (regs : Fin 2 → Bool) (mask out : List Bool) :
    ∃ rf, Eval loop (3 * mask.length + 8 * trueCount mask + 1)
      (popped regs mask out) (state rf [] (prepend (trueCount mask) out)) := by
  induction mask generalizing regs out with
  | nil => exact ⟨readRegs regs 0 1 none, Eval.while_false (by rfl)⟩
  | cons b mask ih =>
      cases b with
      | false =>
          let r := readRegs regs 0 1 (some false)
          obtain ⟨rf, hr⟩ := ih r out
          have hs : Eval (.ite (0 : Fin 2) record (.base .skip)) 1
              (state r mask out) (state r mask out) := .ite_false (by rfl) (.base (.skip _))
          have h := Eval.while_true (by rfl : (popped regs (false :: mask) out).regs 1 = true)
            (hs.seq (pop_eval r mask out)) hr
          refine ⟨rf, ?_⟩
          convert h using 1 <;> simp [loop, trueCount, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful, Nat.mul_add, Nat.add_assoc] ; omega
      | true =>
          let r := readRegs regs 0 1 (some true)
          let r' := Function.update r 0 true
          obtain ⟨rf, hr⟩ := ih r' (true :: true :: false :: false :: out)
          have hs : Eval (.ite (0 : Fin 2) record (.base .skip)) 9
              (state r mask out) (state r' mask (true :: true :: false :: false :: out)) :=
            .ite_true (by rfl) (record_eval r mask out)
          have h := Eval.while_true (by rfl : (popped regs (true :: mask) out).regs 1 = true)
            (hs.seq (pop_eval r' mask (true :: true :: false :: false :: out))) hr
          refine ⟨rf, ?_⟩
          convert h using 1 <;> simp [loop, trueCount, Subexp.PaddedCompletion.trueCount,
            Subexp.PaddedCompletion.successful, prepend_step, Nat.mul_add,
            Nat.add_assoc, Nat.add_comm ] ; omega

theorem prepend_encode (h : ℕ) :
    prepend h [false] = Encoding.encodeList id (List.replicate h [false]) := by
  induction h <;> simp [prepend, List.replicate_succ, Encoding.encodeList, Encoding.frame, *]

theorem command_eval (regs : Fin 2 → Bool) (mask : List Bool) :
    ∃ rf, Eval command (3 * mask.length + 8 * trueCount mask + 4)
      (state regs mask [])
      (state rf [] (Encoding.encodeList id (List.replicate (trueCount mask) [false]))) := by
  let r := Function.update regs 0 false
  have hp := push_eval false (state regs mask [])
  have hp' : Eval (push false) 2 (state regs mask []) (state r mask [false]) := by
    simpa [r, state, pushed] using hp
  obtain ⟨rf, hr⟩ := loop_eval r mask [false]
  refine ⟨rf, ?_⟩
  convert hp'.seq ((pop_eval r mask [false]).seq hr) using 1 <;>
    (try simp only [command, prepend_encode]) ; omega

end SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_HighIncidenceProgramSemantics
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The physical mask is exactly the finite incidence cutoff on original
variables. The theorem counts zero-degree variables in the ambient dimension. -/
namespace SubexponentialSAT.SqrtLog.HighIncidenceProgram
open scoped BigOperators

theorem highPrefix_trueCount (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      ∑ v ∈ Finset.range n, if cut < degree scopes v then 1 else 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Finset.sum_range_succ]
      by_cases h : cut < degree scopes n
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful, Nat.add_comm] using congrArg Nat.succ ih
      · simpa [highPrefix, h, Branches.trueCount, Subexp.PaddedCompletion.trueCount,
          Subexp.PaddedCompletion.successful] using ih

theorem highPrefix_count_eq_card (scopes : List (List ℕ)) (cut n : ℕ) :
    Branches.trueCount (highPrefix scopes cut n) =
      (HighIncidence.high (suppliedScope n scopes) cut).card := by
  rw [highPrefix_trueCount, Finset.sum_range]
  simp only [HighIncidence.high, Finset.card_eq_sum_ones, Finset.sum_filter,
    degree_suppliedScope]

end SubexponentialSAT.SqrtLog.HighIncidenceProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryAdapter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete per-high-assignment setup and compressed head overlays.
The routines read physical counter/mask words and preserve ambient coordinates. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem restoreHighGuard_eval (a : Data) : Eval restoreHighGuard 1 a
    ⟨Function.update a.regs 21 true,a.stacks⟩ :=
  .base (StructuredProgram.Eval.atom (.set 21 true) a)

open OAI.Algorithms.SubexponentialSAT.StackRoutines


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountInit
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid entry to one disjoint high-assignment count. Internal empty binary
words represent zero; the final CanonicalHigh routine emits canonical [false].
The high odometer is copied from the actual encoded seed, never reconstructed
from an assumed family of successful branch states. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit

open BitProgram StructuredCalls StackRoutines HighQueryAdapter

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (792 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 792 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (clearStacks 792 a.stacks)=
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i∈changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i≠792 := by intro h; subst i; exact hi (by simp [changed])
      simp [BankRoutines.clearBankStacks,clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=6 from rfl,
    hs,readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem reset_blank (a : Data) (i : Fin 896) (hi : i∈changed) :
    (resetState a).stacks i=[] := BankRoutines.clearBankStacks_mem i changed a.stacks hi

theorem copy_eval (a : Data) : Eval copy (7*(a.stacks 330).length+5) (resetState a) (copied a) := by
  unfold copy copied
  apply Eval.call
  simpa only [reset_frame a 330 (by decide)] using
    ListRegisterProgram.copy_run (330 : Fin 896) 789 792 (0 : Fin 40) 1
      (by decide) (by decide) (by decide) (by decide)
      (resetState a).regs (resetState a).stacks (reset_blank a 792 (by decide))

theorem command_eval (a : Data) : Eval command (cost a) a (result a) := by
  simpa only [command, cost, result, Nat.add_assoc] using
    (reset_eval a).seq ((copy_eval a).seq (restoreHighGuard_eval (copied a)))

@[simp] theorem counter (a : Data) : (result a).stacks 789=a.stacks 330 := by
  simp [result,copied,copyStacks,reset_frame a 330 (by decide),reset_blank a 789 (by decide)]

@[simp] theorem blank (a : Data) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) : (result a).stacks i=[] := by
  have hn : i≠789 := by intro h; subst i; simp at hi
  have hc : i∈changed := by simpa [changed,List.mem_cons,or_assoc,or_left_comm,or_comm] using
    (show i=789 ∨ i∈([788,790,323,791,792] : List (Fin 896)) from Or.inr hi)
  simp [result,copied,copyStacks,hn,reset_blank a i hc]

theorem frame (a : Data) (i : Fin 896) (hi : i∉changed) : (result a).stacks i=a.stacks i := by
  have hn : i≠789 := by intro h; subst i; exact hi (by decide)
  simp [result,copied,copyStacks,hn,reset_frame a i hi]

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountInit
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighCountSeed
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.FiniteField.fieldFintype _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Each marked count regenerates its own zero high-assignment odometer from
its current physical mask. No common high set or retained previous seed is
assumed. The original two-stack branch initializer is executed concretely. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed

open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter
open OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram

theorem reset_eval (a : Data) : Eval reset (resetCost a) a (resetState a) := by
  have h1 := BankRoutines.clear_call_eval (791 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_eval (791 : Fin 896) (0 : Fin 40) 1 changed (by decide)
    (readRegs a.regs 0 1 none) (clearStacks 791 a.stacks) (by simp)
  have hs : BankRoutines.clearBankStacks changed (clearStacks 791 a.stacks)=
      BankRoutines.clearBankStacks changed a.stacks := by
    funext i
    by_cases hi : i∈changed
    · simp [BankRoutines.clearBankStacks,hi]
    · have hn : i≠791 := by intro h; subst i; exact hi (by decide)
      simp [BankRoutines.clearBankStacks,clearStacks,hi,hn]
  simpa only [reset,resetCost,resetState,show changed.length=3 from rfl,
    hs,readRegs_reset] using h1.seq h2

theorem reset_frame (a : Data) (i : Fin 896) (hi : i∉changed) :
    (resetState a).stacks i=a.stacks i := BankRoutines.clearBankStacks_frame i changed a.stacks hi

theorem reset_blank (a : Data) (i : Fin 896) (hi : i∈changed) :
    (resetState a).stacks i=[] := BankRoutines.clearBankStacks_mem i changed a.stacks hi

theorem result_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896) (hi : i∉changed) :
    (result a rf).stacks i=a.stacks i := by
  have hn : ¬∃ j,stackMap j=i := by
    rintro ⟨j,rfl⟩
    fin_cases j <;> simp [stackMap,changed] at hi
  rw [show (result a rf).stacks i=(copied a).stacks i from
    embedState_stack_frame regMap stackMap (copied a) _ i hn]
  have h792 : i≠792 := by intro h; subst i; exact hi (by decide)
  simp [copied,copyStacks,h792,reset_frame a i hi]

@[simp] theorem result_scratch (a : Data) (rf : Fin 2 → Bool) : (result a rf).stacks 791=[] := by
  rw [show (result a rf).stacks 791=(copied a).stacks 791 from
    embedState_stack_frame regMap stackMap (copied a) _ 791 (by decide)]
  simp [copied,copyStacks,reset_blank a 791 (by decide)]

theorem copy_eval (a : Data) : Eval copy (7*(a.stacks 338).length+5) (resetState a) (copied a) := by
  unfold copy copied
  apply Eval.call
  simpa only [reset_frame a 338 (by decide)] using
    ListRegisterProgram.copy_run (338 : Fin 896) 792 791 (0 : Fin 40) 1
      (by decide) (by decide) (by decide) (by decide)
      (resetState a).regs (resetState a).stacks (reset_blank a 791 (by decide))

private theorem project_copied (a : Data) : projectState regMap stackMap (copied a)=
    Branches.state ((copied a).regs ∘ regMap) (a.stacks 338) [] := by
  apply congrArg₂ StructuredProgram.State.mk
  · rfl
  · funext i
    fin_cases i <;> simp [stackMap, copied, copyStacks,
      reset_blank a 792 (by decide),reset_blank a 330 (by decide),reset_frame a 338 (by decide)]

theorem branch_eval (a : Data) : ∃ rf, Eval branch
    (3*(a.stacks 338).length+8*Branches.trueCount (a.stacks 338)+5) (copied a) (result a rf) := by
  obtain ⟨rf,he⟩ := Branches.command_eval ((copied a).regs ∘ regMap) (a.stacks 338)
  have ht := compiled_halt_trace he 0 1
  rw [←project_copied a] at ht
  have h := eval_call_from_state Branches.program regMap stackMap (copied a)
    (Fin.castAdd_injective _ _) (by decide) ht
  refine ⟨rf,?_⟩
  exact h

theorem command_eval (a : Data) : ∃ rf, Eval command (cost a) a (result a rf) := by
  obtain ⟨rf,h⟩ := branch_eval a
  refine ⟨rf,?_⟩
  convert (reset_eval a).seq ((copy_eval a).seq h) using 1
  · rfl
  · dsimp [cost]
    omega

@[simp] theorem initialized_counter (a : Data) (rf : Fin 2 → Bool) :
    (initialized a rf).stacks 789=Encoding.encodeList id
      (List.replicate (Branches.trueCount (a.stacks 338)) [false]) := by
  rw [initialized,HighCountInit.counter,result_counter]

@[simp] theorem initialized_blank (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∈([788,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=[] := HighCountInit.blank (result a rf) i hi

theorem initialized_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : i∉([330,788,789,790,323,791,792] : List (Fin 896))) :
    (initialized a rf).stacks i=a.stacks i := by
  have hinit : i∉HighCountInit.changed := by simp only [HighCountInit.changed] ; simpa using
    (fun (h : i∈([788,789,790,323,791,792] : List (Fin 896))) => hi (List.mem_cons_of_mem _ h))
  have hseed : i∉changed := by
    simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
    tauto
  exact (HighCountInit.frame (result a rf) i hinit).trans (result_frame a rf i hseed)

/-- Seed WORD length is linear in the mask, including the empty-high singleton
terminator. Counter numerical value is zero regardless of ambient dimension. -/
theorem initialized_counter_length (a : Data) (rf : Fin 2 → Bool) :
    ((initialized a rf).stacks 789).length=4*Branches.trueCount (a.stacks 338)+1 := by
  rw [initialized_counter,ExecCNFTupleOdometer.encoded_length]
  simp
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighCountSeed
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendMask
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Exact current-query mask and attained counter semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend

open OAI BitProgram StructuredCalls
open OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafParametersProgram

theorem high_mask_count (q : LeafQueryFrontend.Query) :
    OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.Branches.trueCount
      (LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))=(highSet q).card := by
  exact OAI.Algorithms.SubexponentialSAT.SqrtLog.HighIncidenceProgram.highPrefix_count_eq_card _ _ _

theorem initialized_current_counter (q : LeafQueryFrontend.Query) (a : Data) (rf : Fin 2 → Bool)
    (hm : a.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) :
    (HighCountSeed.initialized a rf).stacks 789=
      Encoding.encodeList id (List.replicate (highSet q).card [false]) := by
  rw [HighCountSeed.initialized_counter,hm,high_mask_count]

/-- The attained odometer's retained word has polynomial length, even though
the number of high assignments it visits can be exponential. -/
theorem initialized_current_counter_length (q : LeafQueryFrontend.Query) (a : Data) (rf : Fin 2 → Bool)
    (hm : a.stacks 338=LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient)) :
    ((HighCountSeed.initialized a rf).stacks 789).length≤4*BinaryArithmetic.toNat q.ambient+1 := by
  rw [HighCountSeed.initialized_counter_length,hm,high_mask_count]
  have h := Finset.card_le_univ (highSet q)
  simp only [Fintype.card_fin] at h
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighMarkedFrontend
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLocalBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Source-only local costs for the physical high-count controller. Retained
caller words, including the outer marked accumulator322, do not enter them. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
open OAI BitProgram StructuredCalls StackRoutines HighQueryAdapter

private theorem seed_cost_le (a : Data) (L : ℕ)
    (h : ∀ i ∈ seedSources, (a.stacks i).length ≤ L) :
    HighCountSeed.cost a + 1 ≤ 26 * L + 26 := by
  have hs : (HighCountSeed.changed.map
      (fun i => ((clearStacks 791 a.stacks) i).length)).sum ≤ 3 * L := by
    have hb : ∀ i ∈ HighCountSeed.changed,
        ((clearStacks 791 a.stacks) i).length ≤ L := by
      intro i hi
      by_cases he : i = 791
      · subst i
        simp [clearStacks]
      · simp only [HighCountSeed.changed, List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl | rfl
        · simpa [clearStacks] using h 330 (by decide)
        · exact False.elim (he rfl)
        · simpa [clearStacks] using h 792 (by decide)
    have hp := List.sum_le_card_nsmul
      (HighCountSeed.changed.map (fun i => ((clearStacks 791 a.stacks) i).length)) L
      (by intro x hx; obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact hb i hi)
    simpa [HighCountSeed.changed] using hp
  have h791 := h 791 (by decide)
  have hm := h 338 (by decide)
  have hc : SqrtLog.HighIncidenceProgram.Branches.trueCount (a.stacks 338) ≤
      (a.stacks 338).length := List.length_filter_le _ _
  unfold HighCountSeed.cost HighCountSeed.resetCost
  omega

private theorem init_cost_le (a : Data) (L : ℕ)
    (h330 : (a.stacks 330).length ≤ L)
    (h : ∀ i ∈ HighCountInit.changed, (a.stacks i).length ≤ L) :
    HighCountInit.cost a + 1 ≤ 21 * L + 31 := by
  have hs : (HighCountInit.changed.map
      (fun i => ((clearStacks 792 a.stacks) i).length)).sum ≤ 6 * L := by
    have hp := List.sum_le_card_nsmul
      (HighCountInit.changed.map (fun i => ((clearStacks 792 a.stacks) i).length)) L
      (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        by_cases he : i = 792
        · subst i; simp [clearStacks]
        · simpa [clearStacks,he] using h i hi)
    simpa [HighCountInit.changed] using hp
  have h792 := h 792 (by decide)
  unfold HighCountInit.cost HighCountInit.resetCost
  omega

/-- This is the actual current-mask initialization, with no supplied zero
counter and no bound on unrelated retained stacks. -/
theorem seed_eval (a : Data) (L : ℕ)
    (h : ∀ i ∈ seedSources, (a.stacks i).length ≤ L) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval (.call HighCountSeed.initializeProgram) steps a (HighCountSeed.initialized a rf) := by
  obtain ⟨rf,he⟩ := HighCountSeed.command_eval a
  have hs := Eval.call HighCountSeed.program (compiled_halt_trace he 338 330)
  have hi := Eval.call HighCountInit.program
    (compiled_halt_trace (HighCountInit.command_eval (HighCountSeed.result a rf)) 330 788)
  have hcmd : Eval HighCountSeed.initializeCmd
      ((HighCountSeed.cost a + 1) + (HighCountInit.cost (HighCountSeed.result a rf) + 1))
      a (HighCountSeed.initialized a rf) := hs.seq hi
  have h330 : ((HighCountSeed.result a rf).stacks 330).length ≤ 4 * L + 1 := by
    rw [HighCountSeed.result_counter,ExecCNFTupleOdometer.encoded_length]
    simp only [List.flatten_replicate_singleton,List.length_replicate]
    have hm := h 338 (by decide)
    have hc : SqrtLog.HighIncidenceProgram.Branches.trueCount (a.stacks 338) ≤
        (a.stacks 338).length := List.length_filter_le _ _
    omega
  have hb : ∀ i ∈ HighCountInit.changed,
      ((HighCountSeed.result a rf).stacks i).length ≤ 4 * L + 1 := by
    intro i hi
    simp only [HighCountInit.changed, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [HighCountSeed.result_frame a rf 788 (by decide)]
      have := h 788 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 789 (by decide)]
      have := h 789 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 790 (by decide)]
      have := h 790 (by decide); omega
    · rw [HighCountSeed.result_frame a rf 323 (by decide)]
      have := h 323 (by decide); omega
    · rw [HighCountSeed.result_scratch]; simp
    · rw [HighCountSeed.result_maskcopy]; simp
  have ht1 := seed_cost_le a L h
  have ht2 := init_cost_le (HighCountSeed.result a rf) (4 * L + 1) h330 hb
  exact ⟨_,rf,by omega,Eval.call _ (compiled_halt_trace hcmd 338 789)⟩

open HashGreedyProgram.NativeRound

/-- Source-only seed time and all-prefix caller space are properties of the
same fixed actual run, identified by deterministic execution. -/
theorem seed_resources (a : Data) (L D : ℕ)
    (hL : ∀ i ∈ seedSources, (a.stacks i).length ≤ L)
    (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval (.call HighCountSeed.initializeProgram) steps a (HighCountSeed.initialized a rf) ∧
      StageSpace (.call HighCountSeed.initializeProgram) steps a D := by
  obtain ⟨ns,rs,hns,hes⟩ := seed_eval a L hL
  obtain ⟨nd,rd,ht,_,hp⟩ := HighCountSeed.initialize_trace_space a L D
    (hL 338 (by decide)) hlocal hD
  have hed : Eval (.call HighCountSeed.initializeProgram) nd a (HighCountSeed.initialized a rd) :=
    Eval.call _ ht
  have hsteps := StreamResources.eval_steps_eq 778 777 hes hed
  refine ⟨ns,rs,hns,hes,?_⟩
  rw [hsteps]
  exact ⟨StructuredSpace.call_stack_bound _ _ _ _
    (compiled_site (.call HighCountSeed.initializeProgram) 778 777) ht hp⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLocalBounds
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryStart
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual entry to each high-assignment count. The current frontend mask
survives concrete packing/arithmetic and drives the fixed zero-seed program.
The compact returned boundary is separate from the transient prefix bound. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart

open OAI BitProgram StructuredCalls SqrtLog LeafParametersProgram
open LeafProgram.Query HashGreedyProgram.NativeRound

/-- The reusable lower counter and durable high counter contain the same
fresh zero tuple immediately after the actual initializer. -/
theorem initialized_lower_counter (a : Data) (rf : Fin 2 → Bool) :
    (HighCountSeed.initialized a rf).stacks 330 = (HighCountSeed.initialized a rf).stacks 789 := by
  rw [HighCountSeed.initialized_counter]
  change (HighCountInit.result (HighCountSeed.result a rf)).stacks 330 = _
  rw [HighCountInit.frame _ 330 (by decide),HighCountSeed.result_counter]

theorem initialized_kept_frame (a : Data) (rf : Fin 2 → Bool) (i : Fin 896)
    (hi : HashMarkedReturn.kept i = true) :
    (HighCountSeed.initialized a rf).stacks i = a.stacks i := by
  apply HighCountSeed.initialized_frame
  intro hc
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [HashMarkedReturn.kept,Fin.ext_iff,Fin.coe_ofNat_eq_mod] at hi

/-- Only the retained zero tuple needs a new boundary-length estimate; the
initializer empties every other changed word and frames all remaining words. -/
theorem initialized_boundary (q : LeafQueryFrontend.Query) (a : Data)
    (rf : Fin 2 → Bool) (B : ℕ)
    (hm : a.stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
    (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
    (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
    ∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B := by
  have hc := (HighMarkedFrontend.initialized_current_counter_length q a rf hm).trans hn
  intro i
  by_cases hi : i = 330
  · subst i
    rw [initialized_lower_counter]
    exact hc
  · by_cases hj : i = 789
    · subst i
      exact hc
    · by_cases hz : i ∈ ([788,790,323,791,792] : List (Fin 896))
      · rw [HighCountSeed.initialized_blank a rf i hz]
        exact Nat.zero_le _
      · have hf : i ∉ changed := by
          simp only [changed,List.mem_cons,List.not_mem_nil,or_false] at *
          tauto
        rw [HighCountSeed.initialized_frame a rf i hf]
        exact hframe i hf

/-- Source-only time, full-prefix space and a separately restored compact
boundary all describe the same actual fixed seed call. The empty high set
still produces the singleton encoded zero tuple. -/
theorem resources_oai (q : LeafQueryFrontend.Query) (a : Data) (L B D : ℕ)
    (hm : a.stacks 338 =
      LeafQueryFrontend.highMask q.scopeRows (BinaryArithmetic.toNat q.ambient))
    (hL : ∀ i ∈ HighQueryLocalBounds.seedSources, (a.stacks i).length ≤ L)
    (hlocal : 12 * L + 5 ≤ D) (hD : ∀ i, (a.stacks i).length ≤ D)
    (hn : 4 * BinaryArithmetic.toNat q.ambient + 1 ≤ B)
    (hframe : ∀ i, i ∉ changed → (a.stacks i).length ≤ B) :
    ∃ steps rf, steps ≤ 110 * L + 80 ∧
      Eval command steps a (HighCountSeed.initialized a rf) ∧
      Trace (compiled command 778 777) (steps + 1)
        (a.withPC (some (compiled command 778 777).entry))
        ((HighCountSeed.initialized a rf).withPC none) ∧
      (∀ t z, t ≤ steps + 1 → Trace (compiled command 778 777) t
        (a.withPC (some (compiled command 778 777).entry)) z →
        ∀ i, (z.stacks i).length ≤ D) ∧
      (∀ i, ((HighCountSeed.initialized a rf).stacks i).length ≤ B) ∧
      (HighCountSeed.initialized a rf).stacks 789 =
        Encoding.encodeList id (List.replicate (HighMarkedFrontend.highSet q).card [false]) ∧
      (∀ i ∈ ([788,790,323,791,792] : List (Fin 896)),
        (HighCountSeed.initialized a rf).stacks i = []) ∧
      (HighCountSeed.initialized a rf).regs 21 = true ∧
      (∀ i, HashMarkedReturn.kept i = true →
        (HighCountSeed.initialized a rf).stacks i = a.stacks i) := by
  obtain ⟨steps,rf,ht,he,hprefix⟩ := HighQueryLocalBounds.seed_resources a L D hL hlocal hD
  refine ⟨steps,rf,ht,he,compiled_halt_trace he 778 777,?_,
    initialized_boundary q a rf B hm hn hframe,
    HighMarkedFrontend.initialized_current_counter q a rf hm,
    HighCountSeed.initialized_blank a rf,HighCountSeed.initialized_guard a rf,
    initialized_kept_frame a rf⟩
  exact StructuredSpace.compiled_halt_stack_bound he 778 777 hprefix.bound

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryStart.resources_oai
