-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2PairH_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T15:24:07.672899+00:00
-- url     : https://prove2.me/submissions/1d6228ac-a984-4234-8c8d-108f4bd20027

import Mathlib
import Definitions.Def_OAIQ254M008
import Definitions.Def_OAIQ254M011
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_checkLog_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_3_11I2PairMass_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CA2_3_11I2PairP_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyDoublePair_enclosed
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_entropyTerm_ball
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_homogeneous_enclosed

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityA_CapA2_3_11I2
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
lemma CA2_3_11I2PairCertificates_valid :
    CA2_3_11I2PairCertificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CA2_3_11I2PairTerms_sound (a : PairSlot × PairSlot) :
    (CA2_3_11I2PairTerms a).Encloses (Foundation.entropyTerm (CA2_3_11I2PairValue a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CA2_3_11I2PairCertificates_valid
    (CA2_3_11I2PairCertificateIndex a) (CA2_3_11I2PairP_sound a)
lemma CA2_3_11I2PairEntropy_sound : CA2_3_11I2PairEntropy.Encloses (Foundation.finiteEntropy CA2_3_11I2PairValue) := by
  exact contains_sound (entropyDoublePair_enclosed CA2_3_11I2PairValue CA2_3_11I2PairTerms CA2_3_11I2PairTerms_sound) (by decide +kernel)
lemma CA2_3_11I2PairMassTermLog_sound : CA2_3_11I2PairMassTermLog.Encloses (Real.log ((∑ a, CA2_3_11I2PairValue a))) := by
  exact checkLog_sound logTwoBall_sound (CA2_3_11I2PairMass_sound) (w := CA2_3_11I2PairMassTermLogWitness) (by
    simp only [checkLog, Bool.and_eq_true]
    exact ⟨by decide +kernel, by decide +kernel⟩)
lemma CA2_3_11I2PairMassTerm_sound : CA2_3_11I2PairMassTerm.Encloses (Foundation.entropyTerm ((∑ a, CA2_3_11I2PairValue a))) := by
  exact contains_sound (entropyTerm_ball (CA2_3_11I2PairMass_sound) CA2_3_11I2PairMassTermLog_sound) (by decide +kernel)
lemma CA2_3_11I2PairH_sound_oai : CA2_3_11I2PairH.Encloses (homogeneousEntropy CA2_3_11I2PairValue) := by
  exact contains_sound (homogeneous_enclosed CA2_3_11I2PairValue CA2_3_11I2PairMassTerm_sound CA2_3_11I2PairEntropy_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2PairH_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CA2_3_11I2PairH_sound_oai
