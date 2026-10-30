-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T03:40:20.144574+00:00
-- url     : https://prove2.me/submissions/0b690c1f-e4da-44c2-81fd-1123546a271e

import Mathlib
import Definitions.Def_OAIQ081S011

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_RowSelectionProgramStream
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! Arithmetic callbacks on a fixed stream ABI. The remaining record stream is
preserved byte-for-byte across each real signed-arithmetic call. -/
namespace SubexponentialSAT.SqrtLog.RowSelectionProgram

theorem streamPorts_injective_oai : Function.Injective streamPorts := by
  intro i j h
  apply Fin.ext
  exact congrArg (fun k : Fin 16 => k.val) h

end SubexponentialSAT.SqrtLog.RowSelectionProgram

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.RowSelectionProgram.streamPorts_injective_oai
