-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairEntropy_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:21:26.738217+00:00
-- url     : https://prove2.me/submissions/75a155b0-43cf-45fa-8526-468fd2c3300f

import Mathlib
import Definitions.Def_OAIQ254M008
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_6_8I2PairTerms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_6_8I2Pair
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
lemma CA2_6_8I2PairEntropy_sound_oai : CA2_6_8I2PairEntropy.Encloses (Foundation.finiteEntropy CA2_6_8I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_6_8I2PairValue CA2_6_8I2PairTerms CA2_6_8I2PairTerms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairEntropy_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_6_8I2PairEntropy_sound_oai
