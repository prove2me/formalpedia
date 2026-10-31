-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.marked_denominator_empty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:15:26.808813+00:00
-- url     : https://prove2.me/submissions/fd7796a7-320e-4772-876a-56897989b471

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_command_front_state

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LeafProgramQueryReference
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.RingCore.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! The marked collector supplies a reversed reference payload on321. The
query itself pays to copy and reverse that reference into the frontend's
forward index slot705. The original payload survives until the branch exit. -/
namespace SubexponentialSAT.SqrtLog.LeafProgram.Query
open SubexponentialSAT BitProgram StructuredCalls SubexpScanPrimitives

theorem markedInput_frame (a : Data) (i : Fin 768)
    (hi : i≠699) (h705 : i≠705) (h706 : i≠706) :
    (markedInput a).stacks i=a.stacks i := by
  simp [markedInput,flagged,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,afterTransfer,afterCopy,
    StackRoutines.transferStacks,StackRoutines.copyStacks,hi,h705,h706]

end SubexponentialSAT.SqrtLog.LeafProgram.Query

end OAI.Algorithms
end

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_HighFrontendShadow
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! The actual frontend has a query-only polynomial step budget. Selected
stack growth therefore bounds every visible output and every prefix without
charging any suspended caller word. This uses the original execution directly;
no new query evaluator or replacement run is introduced. -/
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow

open BitProgram StructuredCalls SqrtLog HighMarkedFrontend

/-- The real marked frontend preserves the spare denominator word required
by preparation; its entry emptiness follows from the actual clean workspace. -/
theorem marked_denominator_empty_oai (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : Data) (steps : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark.isSome = true)
    (href : a.stacks 321 = q.index.reverse) (he : Eval (command k) steps a b) :
    b.stacks 728 = [] := by
  obtain ⟨l,w,hf⟩ := command_front_state q k a b steps hv hc hs hm href he
  change (project b).stacks 728 = []
  have hframe := hf.frame 728 (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide)
  exact hframe.trans ((LeafProgram.Query.markedInput_frame (project a) 728
    (by decide) (by decide) (by decide)).trans (hc 728 (by decide) (by decide)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.marked_denominator_empty_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.marked_denominator_empty_oai
