-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:24:13.091579+00:00
-- url     : https://prove2.me/submissions/53354a59-ae5a-4071-bde0-3860f73c8a92

import Mathlib
import Definitions.Def_OAIQ254M008
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I1PairMass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_5_9I1PairTerms_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_5_9I1
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
lemma CA2_5_9I1PairEntropy_sound : CA2_5_9I1PairEntropy.Encloses (Foundation.finiteEntropy CA2_5_9I1PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_5_9I1PairValue CA2_5_9I1PairTerms CA2_5_9I1PairTerms_sound) (by decide +kernel)
lemma CA2_5_9I1PairMassTermLog_sound : CA2_5_9I1PairMassTermLog.Encloses (Real.log ((∑ a, CA2_5_9I1PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_5_9I1PairMass_sound) (w := CA2_5_9I1PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_5_9I1PairMassTerm_sound : CA2_5_9I1PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_5_9I1PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_5_9I1PairMass_sound) CA2_5_9I1PairMassTermLog_sound) (by decide +kernel)
lemma CA2_5_9I1PairH_sound_oai : CA2_5_9I1PairH.Encloses (homogeneousEntropy CA2_5_9I1PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_5_9I1PairValue CA2_5_9I1PairMassTerm_sound CA2_5_9I1PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_5_9I1PairH_sound_oai
