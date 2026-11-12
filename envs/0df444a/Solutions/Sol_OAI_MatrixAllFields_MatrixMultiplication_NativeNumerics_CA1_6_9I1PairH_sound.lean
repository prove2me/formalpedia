-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:20:53.739216+00:00
-- url     : https://prove2.me/submissions/7b08b44c-34ed-49ee-abb9-073140af6622

import Mathlib
import Definitions.Def_OAIQ254M007
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1PairMassTerm_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA1_6_9I1PairTerms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA1_6_9I1Pair
attribute [-instance] _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldConstructionData.tagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldFinalState.wordsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.ambientTagsFintype _root_.OAI.MatrixAllFields.MatrixMultiplication.AllFieldHistoryTick.tagsFintype
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
lemma CA1_6_9I1PairEntropy_sound : CA1_6_9I1PairEntropy.Encloses (Foundation.finiteEntropy CA1_6_9I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA1_6_9I1PairValue CA1_6_9I1PairTerms CA1_6_9I1PairTerms_sound) (by decide +kernel)
lemma CA1_6_9I1PairH_sound_oai : CA1_6_9I1PairH.Encloses (homogeneousEntropy CA1_6_9I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA1_6_9I1PairValue CA1_6_9I1PairMassTerm_sound CA1_6_9I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA1_6_9I1PairH_sound_oai
