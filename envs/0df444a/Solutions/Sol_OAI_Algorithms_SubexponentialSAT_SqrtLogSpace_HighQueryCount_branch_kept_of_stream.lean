-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T12:09:43.777751+00:00
-- url     : https://prove2.me/submissions/90d74893-4c18-479f-af92-aa8c36af08ac

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S193
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames_pairs_avoids

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayFootprint
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Compositional certificates for the tape footprint of compiled finite programs. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s l R S L : ℕ}

theorem avoids_transferProgram (H : Fin s → Prop) (src dst : Fin s) (value present : Fin r)
    (hs : ¬ H src) (hd : ¬ H dst) :
    AvoidsProgram H (StackRoutines.transferProgram src dst value present) := by
  intro q
  fin_cases q <;> simp [AvoidsInstr,hs,hd]

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_CommandStackTransport
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! All-prefix resource transport for the existing exact-time tape replay.
The imported avoidance certificate excludes reads as well as writes, including
`peek`. Erasing hidden caller data is a proof construction only: the actual
instruction table and its measured number of steps remain unchanged. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

variable {r s l : ℕ}

/-- Hidden caller words are preserved at every prefix of this same replayed
execution, including prefixes within called finite instruction tables. -/
theorem eval_shadow_prefix_frame (H : Fin s → Prop) [DecidablePred H]
    {command : Cmd r s} (hc : AvoidsCmd H command) (input output : Fin s)
    {steps : ℕ} {a b : State r s}
    (he : Eval command steps (rebaseState H (fun _ => []) a) b)
    {prefixSteps : ℕ} {intermediate : Cfg r s (size command + 1)}
    (hle : prefixSteps ≤ steps + 1)
    (hprefix : Trace (compiled command input output) prefixSteps
      (a.withPC (some (compiled command input output).entry)) intermediate)
    (i : Fin s) (hi : H i) : intermediate.stacks i = a.stacks i := by
  have hstart : rebaseCfg H a.stacks
      ((rebaseState H (fun _ => []) a).withPC
        (some (compiled command input output).entry)) =
      a.withPC (some (compiled command input output).entry) := by
    rw [rebaseCfg_withPC, rebaseState_restore]
  rw [← hstart] at hprefix
  obtain ⟨source, _, rfl⟩ := trace_prefix_rebase H
    (avoids_compiled H command hc input output) a.stacks
    (compiled_halt_trace he input output) hle hprefix
  exact rebaseStacks_of_mem H a.stacks source.stacks i hi

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.CommandStackTransport
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramMass
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The primitive integer accumulator used after each marked-clause count.
Both operands have runtime lengths. The fixed instruction table adds them
exactly and restores little-endian orientation; no arithmetic instruction or
precomputed mass is admitted into the machine model. -/

namespace SubexponentialSAT.SqrtLog.LeafProgram.Mass

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls

/-- This adds two binary words with an actual execution of the fixed adder. -/
theorem command_eval (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 1, ∃ regs',
      Eval command n (data regs acc next) (data regs' (BinaryArithmetic.add acc next) []) := by
  let reset := Function.update regs 0 false
  obtain ⟨regs', n, hn, ht⟩ := BinaryPrograms.Add.littleEndian_run reset acc next
  have hs : (StructuredProgram.Atom.set 0 false).eval (data regs acc next) =
      data reset acc next := by
    rfl
  refine ⟨1 + n, by omega, regs', ?_⟩
  apply Eval.seq (Eval.base (StructuredProgram.Eval.atom (.set 0 false) _))
  rw [hs]
  apply Eval.call
  have hentry : BinaryPrograms.Add.littleEndianProgram.entry = 0 := rfl
  simpa [data, reset, BinaryArithmetic.add, StructuredProgram.State.withPC, hentry] using ht

theorem program_trace (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 2, ∃ regs',
      Trace program n ((data regs acc next).withPC (some program.entry))
        ((data regs' (BinaryArithmetic.add acc next) []).withPC none) := by
  obtain ⟨n, hn, regs', ht⟩ := command_eval regs acc next
  exact ⟨n + 1, by omega, regs', compiled_halt_trace ht 1 0⟩

variable {r s : ℕ}

theorem invoke_eval (p : Ports r s) (frame : State r s)
    (regs : Fin 8 → Bool) (acc next : List Bool) :
    ∃ n ≤ 16 * (max acc.length next.length + 1) + 3, ∃ regs',
      Eval (invoke p) n (state p frame regs acc next)
        (state p frame regs' (BinaryArithmetic.add acc next) []) := by
  obtain ⟨n, hn, regs', ht⟩ := program_trace regs acc next
  exact ⟨n, by omega, regs', eval_call_lifted program p.register p.stack frame
    p.register_injective p.stack_injective ht⟩

end SubexponentialSAT.SqrtLog.LeafProgram.Mass

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafBranchProgram
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The branch callback is a real residual-count program followed by the native
binary adder. Semantic branch counts occur only in its verification contract. -/
namespace SubexponentialSAT.SqrtLog.LeafBranchProgram
open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls
open SubexponentialSAT.ExecCNFTupleEnumeration

variable {R S : ℕ}

theorem mass_self (p : Ports R S) (a : State R S)
    (hs : a.stacks (p.mass.stack 2) = []) :
    LeafProgram.Mass.state p.mass a (fun i => a.regs (p.mass.register i))
      (read p a) (a.stacks (p.mass.stack 1)) = a := by
  apply congrArg₂ StructuredProgram.State.mk
  · funext i
    by_cases h : ∃ j, p.mass.register j = i
    · obtain ⟨j, rfl⟩ := h
      exact embedState_register p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) p.mass.register_injective j
    · exact embedState_register_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h
  · funext i
    by_cases h : ∃ j, p.mass.stack j = i
    · obtain ⟨j, rfl⟩ := h
      calc
        _ = (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))).stacks j :=
            embedState_stack p.mass.register p.mass.stack a _ p.mass.stack_injective j
        _ = _ := by
          fin_cases j <;> simp [LeafProgram.Mass.data, BinaryPrograms.Add.stackState, read, hs]
    · exact embedState_stack_frame p.mass.register p.mass.stack a
        (LeafProgram.Mass.data (fun i => a.regs (p.mass.register i))
          (read p a) (a.stacks (p.mass.stack 1))) i h

theorem mass_frame (p : Ports R S) (a : State R S) regs acc next (j : Fin S)
    (hj : ∀ i, p.mass.stack i ≠ j) :
    (LeafProgram.Mass.state p.mass a regs acc next).stacks j = a.stacks j := by
  apply embedState_stack_frame
  rintro ⟨i, hi⟩
  exact hj i hi

end SubexponentialSAT.SqrtLog.LeafBranchProgram

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

theorem copyHighCounter_eval (a : Data) :
    Eval copyHighCounter (copyHighCost a) a (copiedHighCounter a) := by
  have h1 := BankRoutines.clear_call_eval (330 : Fin 896) (0 : Fin 40) 1 a.regs a.stacks
  have h2 := BankRoutines.clear_call_eval (792 : Fin 896) (0 : Fin 40) 1
    (readRegs a.regs 0 1 none) (clearStacks 330 a.stacks)
  have h3 : Eval (.call (copyProgram (789 : Fin 896) 330 792 (0 : Fin 40) 1))
      (7*(a.stacks 789).length+5)
      ⟨readRegs (readRegs a.regs 0 1 none) 0 1 none,
        clearStacks 792 (clearStacks 330 a.stacks)⟩
      ⟨readRegs (readRegs (readRegs a.regs 0 1 none) 0 1 none) 0 1 none,
        copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks))⟩ := by
    apply Eval.call
    simpa only [clearStacks_frame 330 789 a.stacks (by decide),
      clearStacks_frame 792 789 (clearStacks 330 a.stacks) (by decide)] using
      ListRegisterProgram.copy_run (789 : Fin 896) 330 792 (0 : Fin 40) 1
        (by decide) (by decide) (by decide) (by decide)
        (readRegs (readRegs a.regs 0 1 none) 0 1 none)
        (clearStacks 792 (clearStacks 330 a.stacks)) (by simp)
  have hs : copyStacks 789 330 (clearStacks 792 (clearStacks 330 a.stacks)) =
      Function.update (Function.update a.stacks 330 (a.stacks 789)) 792 [] := by
    funext i
    by_cases h330 : i=330
    · subst i
      simp [copyStacks,clearStacks]
    · by_cases h792 : i=792
      · subst i
        simp [copyStacks,clearStacks]
      · simp [copyStacks,clearStacks,h330,h792]
  have hx := h1.seq (h2.seq h3)
  simp only [clearStacks_frame 330 792 a.stacks (by decide),hs,readRegs_reset] at hx
  convert hx using 1
  · rfl
  · dsimp [copyHighCost]
    omega
  · rfl

theorem copiedHighCounter_frame (a : Data) (i : Fin 896) (h330 : i≠330) (h792 : i≠792) :
    (copiedHighCounter a).stacks i=a.stacks i := by simp [copiedHighCounter,h330,h792]


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryAdapter
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ProgramTapeReplayMacros
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Footprints of the fixed storage and scan controllers used by the leaf. -/
namespace SubexponentialSAT.SqrtLog.ProgramTapeReplay
open SubexponentialSAT BitProgram StructuredCalls
variable {r s : ℕ}

theorem avoids_resetMany (H : Fin s → Prop) (ps : List (Fin 16)) :
    AvoidsCmd H (SubexpSetupStorage.resetMany ps) := by
  induction ps with
  | nil => trivial
  | cons p ps ih => exact ⟨trivial,ih⟩

end SubexponentialSAT.SqrtLog.ProgramTapeReplay

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeReadoutSpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual node-array readout after all finite-difference pairs. The fixed
cleanup pays for transient lower words and clears the old output. Preserved
masters supply the coefficient zero vector and both truncation bounds. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace

open OAI BitProgram StructuredCalls SqrtLog SubexpLiftRing SubexpQuarticRing
open MomentsProgram TruncatedRingProgram

theorem mem_scratchIndices (i : Fin 40) : i ∈ scratchIndices ↔
    i ≠ 0 ∧ i ≠ 5 ∧ i ≠ 12 ∧ i ≠ 15 ∧ i ≠ 24 ∧ i ≠ 27 ∧
      i ≠ 28 ∧ i ≠ 29 ∧ i ≠ 36 := by
  simp only [scratchIndices, List.mem_filter, List.mem_ofFn, exists_eq,
    decide_eq_true_eq, true_and]

theorem scratchPorts_low {i : Fin 896} (hi : i ∈ scratchPorts) :
    88 ≤ i.val ∧ i.val < 128 := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
  obtain ⟨h0,h5,h12,h15,h24,h27,h28,h29,h36⟩ := (mem_scratchIndices j).mp hj
  simp only [ports, h0, h5, h12, h15, h24, h27, h28, h29, h36, ite_false]
  omega

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeReadoutSpace
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NodeFinishReplay
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete no-read/no-write certificates for the emitted-node tail.
These check the actual finite port maps and calls, including every peek;
the pending caller and accumulated count on320/322 are never inspected. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay

open BitProgram StructuredCalls SqrtLog.ProgramTapeReplay

theorem clearMany_avoids (H : Fin 896 → Prop) (ports : List (Fin 896))
    (hp : ∀ i ∈ ports, ¬ H i) : AvoidsCmd H (NodeReadoutSpace.clearMany ports) := by
  induction ports with
  | nil => exact True.intro
  | cons i ports ih =>
      exact ⟨avoids_clearProgram H i 0 1 (hp i (by simp)),
        ih (fun j hj => hp j (by simp [hj]))⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.NodeFinishReplay
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorControlFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Actual query control commands exclude every read, peek and write in the
retained selector bank768..831. Calls into the original768-stack bank are
covered by their genuine port ranges, independently of their internal code. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames

open OAI BitProgram StructuredCalls SubexpSetupStorage SqrtLog
open ProgramTapeReplay

/-- Every actual instruction of a lifted lower-bank program is disjoint from
the persistent selector interval. -/
theorem lowProgram_avoids {r l : ℕ} (p : Program r 768 l)
    (register : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (ProgramLinking.liftProgram p register (Fin.castAdd 128)) := by
  apply avoids_liftProgram_of_range
  intro i hi
  change 768 ≤ i.val ∧ i.val < 832 at hi
  omega

theorem lowCommand_avoids {r : ℕ} (c : Cmd r 768) (input output : Fin 768)
    (register : Fin r → Fin 40) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (liftCommand c input output register (Fin.castAdd 128)) :=
  lowProgram_avoids (compiled c input output) register

private theorem isolated_avoids {r s l : ℕ}
    (p : Program r s l) (register : Fin r → Fin 16) (stack : Fin s → Fin 896)
    (tmp : Fin 896) (ports : List (Fin 896)) (inputs outputs : List (Fin 896 × Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832))
    (hi : ∀ q ∈ inputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (ho : ∀ q ∈ outputs, ¬ (768 ≤ q.1.val ∧ q.1.val < 832) ∧
      ¬ (768 ≤ q.2.val ∧ q.2.val < 832))
    (hs : ∀ i, ¬ (768 ≤ (stack i).val ∧ (stack i).val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (isolated p register stack tmp ports inputs outputs) := by
  refine ⟨?_, avoids_liftProgram_of_range _ p register stack hs, ?_⟩
  · exact ⟨avoids_clearMany _ [tmp] (by simpa using ht),
      avoids_clearMany _ ports hp, avoids_resetMany _ workRegisters,
      avoids_copyMany _ tmp inputs ht hi⟩
  · refine ⟨avoids_clearMany _ (outputs.map Prod.snd) ?_,
      avoids_copyMany _ tmp outputs ht ho, avoids_clearMany _ ports hp,
      avoids_resetMany _ workRegisters⟩
    intro i h
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp h
    exact (ho q hq).2

private theorem bankClear_avoids {r : ℕ} (tmp : Fin 896)
    (value present : Fin r) (ports : List (Fin 896))
    (ht : ¬ (768 ≤ tmp.val ∧ tmp.val < 832))
    (hp : ∀ i ∈ ports, ¬ (768 ≤ i.val ∧ i.val < 832)) :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      (BankRoutines.clearCmd tmp value present ports) := by
  induction ports with
  | nil => exact avoids_clearProgram _ tmp value present ht
  | cons i ports ih =>
    exact ⟨avoids_clearProgram _ i value present (hp i (by simp)),
      ih (fun j hj => hp j (by simp [hj]))⟩

theorem countCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.countCommand := by
  apply isolated_avoids
  · decide
  · norm_num [PairNativeSetup.scratch, Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · norm_num [Fin.coe_ofNat_eq_mod]
  · intro i
    fin_cases i <;> decide

theorem setupCommand_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCommand :=
  ⟨countCommand_avoids, avoids_clearMany _ _ (by norm_num [Fin.coe_ofNat_eq_mod]),
    avoids_copyCmd _ _ _ _ (by decide) (by decide) (by decide)⟩

theorem setupCaller_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      PairNativeSetup.setupCaller :=
  avoids_liftProgram _ _ _ _ (avoids_compiled _ _ setupCommand_avoids _ _)

theorem prepareHigh_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      HighQueryAdapter.prepareHigh := by
  refine ⟨⟨avoids_clearProgram _ _ _ _ (by decide),
    bankClear_avoids _ _ _ _ (by decide)
      (by norm_num [HighQueryAdapter.highChanged, Fin.coe_ofNat_eq_mod])⟩, ?_⟩
  apply avoids_liftProgram_of_range
  intro i
  fin_cases i <;> decide

theorem nativeLayoutLoad_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NativeLayoutLoad.command := by
  constructor
  · apply avoids_liftProgram
    apply avoids_compiled
    apply avoids_clearMany
    intro i hi
    rcases List.mem_append.mp hi with hi | hi
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
      rcases hi with rfl | rfl | rfl <;> decide
    · obtain ⟨j, _, rfl⟩ := List.mem_map.mp hi
      change ¬ (768 ≤ j.val ∧ j.val < 832)
      omega
  · exact lowCommand_avoids _ _ _ _

theorem initializeNodes_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.initializeNodes := by
  refine ⟨lowCommand_avoids _ _ _ _, NodeFinishReplay.clearMany_avoids _ _ ?_⟩
  intro i hi
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl <;> decide

theorem beginNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryAssembler.Nodes.beginNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, lowCommand_avoids _ _ _ _⟩
  intro i hi
  simp only [QueryAssembler.Nodes.nodeResetPorts, List.mem_cons, List.mem_nil_iff,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem readout_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeReadoutSpace.command := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    rcases List.mem_cons.mp hi with hi | hi
    · subst i
      decide
    · have hs := NodeReadoutSpace.scratchPorts_low hi
      omega
  · apply avoids_call_lift_of_range
    intro i
    fin_cases i <;> decide

/-- The exact paid scalar-cache copies are also used by the tuple-sum visitor. -/
theorem nodeAppendPrepare_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.prepare := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  · exact ⟨avoids_copyProgram _ 194 5 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 202 12 89 0 1 (by decide) (by decide) (by decide),
      avoids_copyProgram _ 204 39 89 0 1 (by decide) (by decide) (by decide)⟩

theorem append_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.append :=
  ⟨avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 862 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 863 0 1 (by decide) (by decide)⟩

theorem nodeAppend_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.command :=
  ⟨nodeAppendPrepare_avoids, readout_avoids, append_avoids⟩

theorem finishNode_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.finishNode := by
  refine ⟨NodeFinishReplay.clearMany_avoids _ _ ?_, ⟨⟨True.intro, ?_⟩, ?_⟩⟩
  · intro i hi
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hi
    rcases hi with rfl | rfl <;> decide
  · change ¬ (768 ≤ (307 : Fin 896).val ∧ (307 : Fin 896).val < 832)
    decide
  · change ¬ (768 ≤ (301 : Fin 896).val ∧ (301 : Fin 896).val < 832)
    decide

theorem nodeFinish_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryNodeFinish.command := ⟨nodeAppend_avoids, finishNode_avoids⟩

theorem handoff_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      NodeAppendSpace.handoff :=
  ⟨avoids_clearProgram _ 265 0 1 (by decide),
    avoids_transferProgram _ 863 89 0 1 (by decide) (by decide),
    avoids_transferProgram _ 89 265 0 1 (by decide) (by decide)⟩

theorem reconstruction_avoids :
    AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832)
      QueryReconstruction.command := ⟨handoff_avoids, lowCommand_avoids _ _ _ _⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorControlFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QuerySelectorFrames
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The conditioned query also excludes the entire retained selector bank.
This accounts for arbitrary incumbent and remaining-round words in the
actual greedy callback's time quantifiers. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames

open OAI BitProgram StructuredCalls SqrtLog.ProgramTapeReplay
open SignatureTupleProgram SignatureTupleNative

local notation "H" => (fun i : Fin 896 => 768 ≤ Fin.val i ∧ Fin.val i ≤ 831)

open OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

theorem lower_avoids {r l : ℕ} (p : Program r 768 l) (reg : Fin r → Fin 40) :
    AvoidsProgram (fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831)
      (ProgramLinking.liftProgram p reg SignatureHeadLoader.lowStacks) := by
  apply avoids_liftProgram_of_range
  intro i hi
  have hv := i.isLt
  change 768 ≤ i.val ∧ i.val ≤ 831 at hi
  omega


private theorem interval_convert {c : Cmd 40 896}
    (h : AvoidsCmd (fun i : Fin 896 => 768 ≤ i.val ∧ i.val < 832) c) :
    AvoidsCmd H c := by simpa only [Nat.lt_succ_iff] using h


theorem bootstrap_avoids : AvoidsCmd H QueryStreamProgram.bootstrapNode :=
  lower_avoids SignatureHeadLoader.bootstrapProgram SignatureHeadLoader.leafRegs

theorem node_body_avoids : AvoidsCmd H QueryStreamProgram.nodeBody :=
  ⟨interval_convert QuerySelectorControlFrames.beginNode_avoids,
    interval_convert QuerySelectorControlFrames.nativeLayoutLoad_avoids, bootstrap_avoids,
    interval_convert QuerySelectorControlFrames.setupCaller_avoids, pairs_avoids,
    interval_convert QuerySelectorControlFrames.nodeFinish_avoids⟩

theorem nodes_avoids : AvoidsCmd H QueryStreamProgram.nodes := by
  refine ⟨interval_convert QuerySelectorControlFrames.initializeNodes_avoids, ?_, node_body_avoids⟩
  change ¬ H 301
  decide

/-- The actual fixed conditioned query excludes the whole retained selector
bank, including every invoked table and every peek. -/
theorem command_avoids : AvoidsCmd H QueryStreamProgram.command :=
  ⟨interval_convert QuerySelectorControlFrames.prepareHigh_avoids, nodes_avoids,
    interval_convert QuerySelectorControlFrames.reconstruction_avoids⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QuerySelectorFrames
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryProgram
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Fixed finite syntax for both marked and final accepted queries. The only
program parameter is the fixed clause width. Every mark regenerates its own
physical high mask and zero counter. The semantic proof must establish that
the actual frontend guard holds on every reachable input. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram

open OAI BitProgram StructuredCalls HighQueryAdapter
noncomputable section

/-- This measured physical composition is the branch syntax used by highLoop.
The supplied evaluation is specifically the fixed stream command, not a query
oracle or a callback chosen by the caller. -/
theorem conditioned_eval (a b : Data) (n : ℕ)
    (he : Eval QueryStreamProgram.command n (copiedHighCounter a) b) :
    Eval conditioned (copyHighCost a + (n + 1)) a
      ⟨Function.update b.regs 21 true,b.stacks⟩ :=
  (copyHighCounter_eval a).seq (he.seq (restoreHighGuard_eval b))

open HashGreedyProgram.NativeRound

end
end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryProgram
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryLoop
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Concrete high-loop interfaces: the original ternary source count, exact
physical rank order, the fixed stream's durable frame, and its actual native
accumulator. The full loop still requires the actual stream semantics. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop

open OAI BitProgram StructuredCalls SqrtLog LeafProgram LeafBranchProgram
open HighQueryAdapter PreparedBranchCount ProgramTapeReplay
open scoped BigOperators

/-- Every instruction and compiled prefix of the fixed stream leaves the
whole durable selector/high-counter interval unchanged. -/
theorem stream_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps a b)
    (i : Fin 896) (hi : 768 ≤ i.val ∧ i.val ≤ 831) : b.stacks i = a.stacks i := by
  let H := fun i : Fin 896 => 768 ≤ i.val ∧ i.val ≤ 831
  have hs := eval_rebase H QuerySelectorFrames.command_avoids he (fun _ => [])
  exact CommandStackTransport.eval_shadow_prefix_frame H QuerySelectorFrames.command_avoids
    330 323 hs (by omega) (compiled_halt_trace he 330 323) i hi

/-- The paid counter copy and real guard restoration preserve the live
accumulator, durable odometer, and both adder/counter scratch words. -/
theorem conditioned_durable_frame {a b : Data} {steps : ℕ}
    (he : Eval QueryStreamProgram.command steps (copiedHighCounter a) b)
    (i : Fin 896) (hi : i ∈ ([788,789,790,791] : List (Fin 896))) :
    (⟨Function.update b.regs 21 true,b.stacks⟩ : Data).stacks i = a.stacks i := by
  change b.stacks i = a.stacks i
  have hr : 768 ≤ i.val ∧ i.val ≤ 831 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  rw [stream_durable_frame he i hr]
  apply copiedHighCounter_frame
  · intro h
    subst i
    simp at hi
  · intro h
    subst i
    simp at hi

open HashGreedyProgram.NativeRound


end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryLoop
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighQueryCount
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The persistent physical boundary for the actual high-assignment loop.
The ring, source and parked layout words are produced once for this query and
retained across each rank. No execution or evaluator is part of this invariant. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount

open OAI BitProgram StructuredCalls SqrtLog LeafProgram
open HighQueryAdapter

/-- Kept caller words are disjoint from the concrete high controller's
reusable counter and mass-adder words. This includes the parked blank767. -/
theorem kept_disjoint (i : Fin 896) (hi : HashMarkedReturn.kept i=true) :
    i≠323 ∧ i≠330 ∧ i≠788 ∧ i≠789 ∧ i≠790 ∧ i≠791 ∧ i≠792 := by
  simp only [HashMarkedReturn.kept,decide_eq_true_eq,Fin.ext_iff,
    Fin.coe_ofNat_eq_mod] at hi ⊢
  omega

/-- Actual native addition preserves the full caller frame, not only the
arithmetic words required by the next conditioned query. -/
theorem mass_eval_kept {a b : Data} {steps : ℕ}
    (he : Eval (Mass.invoke highPorts.mass) steps a b) (hs : a.stacks 791=[])
    (i : Fin 896) (hi : HashMarkedReturn.kept i=true) : b.stacks i=a.stacks i := by
  obtain ⟨ticks,_,rf,ht⟩ := Mass.invoke_eval highPorts.mass a
    (fun j => a.regs (highPorts.mass.register j)) (a.stacks 788) (a.stacks 323)
  have hself : Mass.state highPorts.mass a (fun j => a.regs (highPorts.mass.register j))
      (a.stacks 788) (a.stacks 323)=a := LeafBranchProgram.mass_self highPorts a hs
  rw [hself] at ht
  rw [Eval.final_unique 788 he ht]
  have hd := kept_disjoint i hi
  apply LeafBranchProgram.mass_frame highPorts a rf _ [] i
  intro j
  fin_cases j
  · exact Ne.symm hd.2.2.1
  · exact Ne.symm hd.1
  · exact Ne.symm hd.2.2.2.2.2.1

/-- The real copy, fixed query, guard restoration and native adder retain the
same caller words as the actual stream; no global space cap proves this frame. -/
theorem branch_kept_of_stream_oai {a middle b : Data} {querySteps branchSteps : ℕ}
    (he : Eval QueryStreamProgram.command querySteps (copiedHighCounter a) middle)
    (hb : Eval HighQueryProgram.branch branchSteps a b)
    (hs : a.stacks 791=[])
    (hf : ∀ i,HashMarkedReturn.kept i=true →
      middle.stacks i=(copiedHighCounter a).stacks i) :
    ∀ i,HashMarkedReturn.kept i=true → b.stacks i=a.stacks i := by
  change Eval (.seq HighQueryProgram.conditioned (Mass.invoke highPorts.mass)) branchSteps a b at hb
  cases hb with
  | seq hc hm =>
    have hout := Eval.final_unique 789 hc (HighQueryProgram.conditioned_eval a middle querySteps he)
    subst_vars
    have htmp : (⟨Function.update middle.regs 21 true,middle.stacks⟩ : Data).stacks 791=[] :=
      (HighQueryLoop.conditioned_durable_frame he 791 (by simp)).trans hs
    intro i hi
    have hd := kept_disjoint i hi
    exact (mass_eval_kept hm htmp i hi).trans
      ((hf i hi).trans (copiedHighCounter_frame a i hd.2.1 hd.2.2.2.2.2.2))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighQueryCount.branch_kept_of_stream_oai
