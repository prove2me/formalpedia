-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T07:49:29.005125+00:00
-- url     : https://prove2.me/submissions/a10bcdb8-e73c-4203-a4c2-f36be9e96242

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_SubexponentialSAT
import Definitions.Def_OAIQ081S152
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_CompileSpace_compile_word_answer_space

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
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeEntrySpace
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Every-prefix space composition for the actual canonical frontend and
fixed-cutoff dispatcher. The large evaluation is a concrete subsequent run;
this module only composes its existing bound with the paid entry instructions. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse.DFSVisit

/-- The terminal halt and the selected Boolean output metadata preserve the
same entry bound. The primitive compiler can consume this exact source trace. -/
theorem entry_bounded_trace_space {cutoff steps bound : ℕ} (large : Cmd 80 1220)
    (input : List Bool) (b : State 80 1220)
    (he : BoundedEval (entryCommand cutoff large) steps
      (StructuredProgram.ioState ABI.countStack input) b bound) :
    Trace (entryProgram cutoff large) (steps + 1)
      (initial (entryProgram cutoff large) input) (b.withPC none) ∧
    ∀ prefixSteps c, prefixSteps ≤ steps + 1 →
      Trace (entryProgram cutoff large) prefixSteps
        (initial (entryProgram cutoff large) input) c →
      ∀ i, (c.stacks i).length ≤ bound := by
  refine ⟨compiled_halt_trace he.eval ABI.countStack ABI.answerStack, ?_⟩
  exact StructuredSpace.compiled_halt_stack_bound he.eval ABI.countStack ABI.answerStack he.space

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_NativeOuter
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingModel.Data.fieldFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The fixed outer instruction sequence composes actual parameter setup,
disjoint counting DFS, and full-word positivity. The existing concrete-leaf
contract remains an explicit development obligation, not a final endpoint. -/

namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native

open BitProgram StructuredCalls DisjointReuse

/-- Compile an actual bounded execution of the fixed outer sequence after the
canonical entry. Both physical outputs and all primitive prefixes use this run. -/
theorem counting_primitive_from_entry_oai {cutoff k n steps bound : ℕ}
    (leaf : Cmd 80 1220) (F : SAT.CNF (Fin n)) (b : State 80 1220)
    (he : DFSVisit.BoundedEval (entryCommand cutoff (outerCommand k leaf)) steps
      (StructuredProgram.ioState ABI.countStack (Encoding.encodeCNF F)) b bound)
    (hc : b.stacks ABI.countStack = countWord (SAT.count F))
    (ha : b.stacks ABI.answerStack = [decide (0 < SAT.count F)]) :
    ∃ time : ℕ, ∃ final : LocatedCfg (GuardedCompiler.primitive (countingProgram cutoff k leaf)),
      Computation.Trace
        (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) time
        (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
          (Encoding.encodeCNF F)) final ∧
      final.config.state = .inl (decide (0 < SAT.count F)) ∧
      final.config.tapes ABI.countStack =
        Turing.Tape.mk₁ ((countWord (SAT.count F)).map some) ∧
      final.config.tapes ABI.answerStack =
        Turing.Tape.mk₁ [some (decide (0 < SAT.count F))] ∧
      time ≤ 7 * (steps + 1) ∧
      ∀ prefixSteps intermediate, prefixSteps ≤ time →
        Computation.Trace
          (locatedStep (GuardedCompiler.primitive (countingProgram cutoff k leaf))) prefixSteps
          (locatedInit (GuardedCompiler.primitive (countingProgram cutoff k leaf))
            (Encoding.encodeCNF F)) intermediate →
        visitedSpace intermediate ≤ 1220 * (bound + Encoding.formulaBitLength F + 15) := by
  obtain ⟨ht, hs⟩ := entry_bounded_trace_space (outerCommand k leaf) (Encoding.encodeCNF F) b he
  obtain ⟨time, htime, final, hrun, hhalt, hcount, hanswer, hspace⟩ :=
    CompileSpace.compile_word_answer_space (countingProgram cutoff k leaf) ABI.countStack
      ht rfl hc ha hs
  exact ⟨time, final, hrun, hhalt, hcount, hanswer, htime, hspace⟩

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.Native.counting_primitive_from_entry_oai
