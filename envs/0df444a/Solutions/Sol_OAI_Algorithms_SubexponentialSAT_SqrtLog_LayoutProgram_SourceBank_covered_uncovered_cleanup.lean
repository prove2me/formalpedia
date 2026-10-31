-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T10:37:40.685442+00:00
-- url     : https://prove2.me/submissions/30f8320f-a0b7-4789-a3f2-86ebe9b369a2

import Mathlib
import Definitions.Def_OAIQ081S186
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLog_LayoutProgram_SourceBank_literal_cleanup_eval

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutProgramSourceDispatch
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Native control branches for source-polynomial lookup. Every literal and
conditional is executed; the universal-branch premise is an actual trace of
that fixed command and is supplied by the native table/emitter composition. -/
namespace SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

open SubexponentialSAT.BitProgram SubexponentialSAT.StructuredCalls SubexponentialSAT.Subexp

theorem covered_uncovered_cleanup_oai (a : Data) (h : LiteralReady a)
    (h5 : a.regs 5=false) (B : ℕ) (hB : ∀ j,(a.stacks j).length ≤ B) :
    ∃ n ≤ 134*B+200, ∃ b : Data,
      Eval (.seq covered cleanup) n a b ∧
      b.stacks=Function.update (clearedStacks a) 287
        (SubexpKernelControl.pushWord (a.stacks 313)) := by
  obtain ⟨n,hn,b,he,hbs⟩ := literal_cleanup_eval 313 (Or.inl rfl) a h.1 h.2.1 h.2.2.1 h.2.2.2 B hB
  cases he with
  | seq hl hc =>
    refine ⟨_,?_,b,(Eval.ite_false (yes:=.seq compareBlocks (.ite 7 universal zero)) h5 hl).seq hc,hbs⟩
    have hh := hB 313
    omega

end SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutProgram.SourceBank.covered_uncovered_cleanup_oai
