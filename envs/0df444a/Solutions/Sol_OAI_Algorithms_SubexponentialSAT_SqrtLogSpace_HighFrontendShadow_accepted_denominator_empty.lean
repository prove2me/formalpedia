-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:14:38.088647+00:00
-- url     : https://prove2.me/submissions/d956f536-e590-4869-9db0-459601ac1c55

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ081S183
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_HighMarkedFrontend_accepted_command_front_state

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

theorem unmarkedInput_frame (a : Data) (i : Fin 768) (h705 : i≠705) (h706 : i≠706) :
    (unmarkedInput a).stacks i=a.stacks i := by
  simp [unmarkedInput,SubexpParameterProgram.runAtoms,StructuredProgram.Atom.eval,
    StructuredProgram.Atom.instr,BitProgram.execInstr,
    StructuredProgram.State.ofCfg,h705,h706]

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

/-- The history-only frontend leaves the same actual preparation scratch empty. -/
theorem accepted_denominator_empty_oai (q : LeafQueryFrontend.Query) (k : ℕ)
    (a b : Data) (steps : ℕ) (hv : q.Valid)
    (hc : LeafProgram.Query.CleanWork (project a))
    (hs : LeafProgram.Query.Sources q (project a)) (hm : q.mark = none)
    (hindex : q.index = [false]) (he : Eval (acceptedCommand k) steps a b) :
    b.stacks 728 = [] := by
  obtain ⟨l,w,hf⟩ := accepted_command_front_state q k a b steps hv hc hs hm hindex he
  change (project b).stacks 728 = []
  have hframe := hf.frame 728 (Or.inr (by decide))
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro j; fin_cases j <;> decide)
  exact hframe.trans ((LeafProgram.Query.unmarkedInput_frame (project a) 728
    (by decide) (by decide)).trans (hc 728 (by decide) (by decide)))

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.HighFrontendShadow.accepted_denominator_empty_oai
