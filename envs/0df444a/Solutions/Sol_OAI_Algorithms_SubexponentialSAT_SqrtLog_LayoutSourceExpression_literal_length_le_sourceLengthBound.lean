-- Prove2me | solution 1 for OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T08:50:09.937977+00:00
-- url     : https://prove2.me/submissions/2c63278c-893c-4eab-8fcc-c630b1ce5882

import Mathlib
import Definitions.Def_OAIQ081S173

section
-- module Solutions.OAIQ081_SAT.SubexponentialSAT_SqrtLog_LayoutSourceExpressionBounds
attribute [-instance] _root_.OAI.Algorithms.SubexponentialSAT.SqrtLog.IrreducibleSearch.primeThree
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI.Algorithms

/-! A shared source-byte budget for literal and universal-row branches. -/
namespace SubexponentialSAT.SqrtLog.LayoutSourceExpression

open SubexponentialSAT.Subexp UniversalRowSourceBound PolynomialExecutorProgram

theorem literal_length {B d : ℕ} (c : Coeff B d) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length = 2 * (d * B) + 2 := by
  simp

theorem literal_length_le {B d S : ℕ} (c : Coeff B d) (hwidth : d * B ≤ S) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ 2 * S + 2 := by
  rw [literal_length]
  omega

theorem linear_le_sourceLengthBound (S : ℕ) :
    2 * S + 2 ≤ sourceLengthBound S := by
  have hi : 2 * S + 2 ≤ inputBound S := by
    unfold inputBound rowBytes
    omega
  have hp : 0 < inputBound S := by omega
  unfold sourceLengthBound
  nlinarith

theorem literal_length_le_sourceLengthBound_oai {B d S : ℕ}
    (c : Coeff B d) (hwidth : d * B ≤ S) :
    (SubexpKernelControl.pushWord (RingProgram.flat c)).length ≤ sourceLengthBound S :=
  (literal_length_le c hwidth).trans (linear_le_sourceLengthBound S)

end SubexponentialSAT.SqrtLog.LayoutSourceExpression

end OAI.Algorithms
end

theorem solution : type_of% @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound_oai := @OAI.Algorithms.SubexponentialSAT.SqrtLog.LayoutSourceExpression.literal_length_le_sourceLengthBound_oai
