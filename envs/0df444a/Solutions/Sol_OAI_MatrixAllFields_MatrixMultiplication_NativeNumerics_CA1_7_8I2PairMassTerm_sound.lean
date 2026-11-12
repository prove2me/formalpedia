-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairMassTerm_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T12:11:30.023873+00:00
-- url     : https://prove2.me/submissions/e4672d82-f942-4f86-a5b1-6a2d70507ad0

import Mathlib
import Definitions.Def_OAIQ254M008
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I2PairMassTermLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_7_8I2PairMass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_7_8I2Pair
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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators
lemma CA1_7_8I2PairMassTerm_sound_oai : CA1_7_8I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA1_7_8I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA1_7_8I2PairMass_sound) CA1_7_8I2PairMassTermLog_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairMassTerm_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_7_8I2PairMassTerm_sound_oai
