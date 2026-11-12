-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.totalLogBall_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T07:12:27.764104+00:00
-- url     : https://prove2.me/submissions/9e3cb02b-b2a8-4e3f-9b77-24af2c8cb793

import Mathlib
import Definitions.Def_OAIQ254M002
import Definitions.Def_OAIQ254M003
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_totalMarginalBall_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_Certificates_SparseContraction
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MatrixAllFields

open scoped BigOperators Topology Polynomial

section
noncomputable section

namespace MatrixMultiplication.AllFieldInitialEntropyCertificate
open AllFieldParameters AllFieldCertificates AllFieldCertificates.Replay
open scoped BigOperators

lemma totalLogBall_sound_oai :
    totalLogBall.Encloses (Real.log (∑ k, AllFieldInitialEntropy.nativeInitialMarginal k)) := by
  exact checkLog_sound logTwoBall_sound totalMarginalBall_sound
    (w := totalLogWitness) (by decide +kernel)

end MatrixMultiplication.AllFieldInitialEntropyCertificate

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.totalLogBall_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.AllFieldInitialEntropyCertificate.totalLogBall_sound_oai
