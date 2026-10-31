-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepare_run
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T06:09:40.64898+00:00
-- url     : https://prove2.me/submissions/0435edbc-ceea-46cd-ac10-d9a8e242e2f9

import Mathlib
import Definitions.Def_OAIQ081S127

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SubexpCRTOuterControl
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Concrete tape operations and traversal assertions for the outer CRT.
All operations in this module are fixed finite programs. Arithmetic is supplied
by the separately defined concrete CRT service commands. -/

namespace SubexponentialSAT.SubexpCRTOuterProgram

open BitProgram StructuredCalls SubexpScanPrimitives

theorem copy_run (d : Data) (src dst : Fin 320)
    (hsd : src ≠ dst) (hs : src ≠ 318) (hd : (318 : Fin 320) ≠ dst)
    (ht : d.stacks 318 = []) :
    Eval (copy src dst) (7 * (d.stacks src).length + 5) d
      (afterCopy d src dst 0 1) :=
  SubexpScanPrimitives.copy_eval d src dst 318 0 1 hsd hs hd (by decide) ht

end SubexponentialSAT.SubexpCRTOuterProgram

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_ReconstructionProgramEntry
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Physical preparation of the low scalar caches used by dense polynomial
addition. The high copies remain available to all native ring services. -/
namespace SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives SubexpCRTOuterProgram

theorem prepare_run_oai (d : Data) (h5 : d.stacks 5 = []) (h10 : d.stacks 10 = [])
    (h318 : d.stacks 318 = []) :
    ∃ rf, Eval prepare (budget (d.stacks 194).length (d.stacks 202).length)
      d ⟨rf, prepared d.stacks⟩ := by
  have h1 := copy_run d 194 5 (by decide) (by decide) (by decide) h318
  let d1 := afterCopy d 194 5 0 1
  have h2 := copy_run d1 202 10 (by decide) (by decide) (by decide)
    (by simpa [d1, afterCopy, StackRoutines.copyStacks] using h318)
  have h := h1.seq h2
  have he : (afterCopy d1 202 10 0 1).stacks = prepared d.stacks := by
    funext i
    simp [d1, afterCopy, StackRoutines.copyStacks, prepared, h5, h10]
  have hstate : afterCopy d1 202 10 0 1 =
      (⟨(afterCopy d1 202 10 0 1).regs, prepared d.stacks⟩ : Data) := state_ext rfl he
  rw [hstate] at h
  refine ⟨(afterCopy d1 202 10 0 1).regs, ?_⟩
  convert h using 1 <;> simp [prepare, budget, d1, afterCopy, StackRoutines.copyStacks] ; omega

end SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepare_run_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.ReconstructionProgram.Entry.prepare_run_oai
