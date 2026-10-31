-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_length
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T09:56:22.960582+00:00
-- url     : https://prove2.me/submissions/a2d5fbfa-4a94-4fa1-98a6-60445ee6b9e8

import Mathlib
import Definitions.Def_OAIQ081S179
import Theorems.Thm_OAI_Algorithms_SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad_result_mask_word

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLogSpace_QueryVisitorLoad
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

/-! Paid reverse-head reload for the two-pass query visitor. The same native
run returns every integer row, preserves the suspended query data, and restores
a fixed retained word cap before the next head. -/

noncomputable section
namespace OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
open OAI BitProgram StructuredCalls OAI.Algorithms.SubexponentialSAT.SqrtLog
open LeafHeadSetupProgram OAI.Algorithms.SubexponentialSAT.SubexpSetupStorage

section Outputs
variable (s : Native.Inputs) (z : ℕ) (frame : State 40 896)
    (rp : Fin 8 → Bool) (rm : Fin 16 → Bool) (rs : Fin 8 → Bool)
    (raw : List (List LayoutMatrixProgram.Pair)) (shifted : List (List (List Bool)))

theorem result_mask_length_oai :
    ((result s z frame rp rm rs raw shifted).stacks 670).length=s.n := by
  rw [result_mask_word,List.length_ofFn]

end Outputs

end OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad
end
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_length_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLogSpace.QueryVisitorLoad.result_mask_length_oai
