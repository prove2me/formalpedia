-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R4Entropy_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:23:23.492939+00:00
-- url     : https://prove2.me/submissions/f6f6322d-1ed0-4d78-b863-d0733e4a5742

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_finSumBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB1_2_5I2R4Raw_sound

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
namespace MatrixMultiplication.NativeNumerics
open AllFieldParameters AllFieldHistory AllFieldCertificates AllFieldCertificates.Replay
open AllFieldInitialEntropyCertificate AllFieldNativeCapacity
open scoped BigOperators

lemma entropyFin_enclosed (n : ℕ) (p : Fin n → ℝ) (bs : Fin n → Ball)
    (h : ∀ i, (bs i).Encloses (Foundation.entropyTerm (p i))) :
    (finSumBall n bs).Encloses (Foundation.finiteEntropy p) :=
  finSumBall_sound n _ _ h

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB1_2_5I2
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
lemma CB1_2_5I2R4Certificates_valid :
    CB1_2_5I2R4Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB1_2_5I2R4P_check : ∀ a : Fin 6, contains (CB1_2_5I2R4Raw a) (CB1_2_5I2R4P a) = true := by
  decide +kernel
lemma CB1_2_5I2R4P_sound (a : Fin 6) :
    (CB1_2_5I2R4P a).Encloses (CB1_2_5I2R4Value a) :=
  contains_sound (CB1_2_5I2R4Raw_sound a) (CB1_2_5I2R4P_check a)
lemma CB1_2_5I2R4Terms_sound (a : Fin 6) :
    (CB1_2_5I2R4Terms a).Encloses (Foundation.entropyTerm (CB1_2_5I2R4Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB1_2_5I2R4Certificates_valid
    (CB1_2_5I2R4CertificateIndex a) (CB1_2_5I2R4P_sound a)
lemma CB1_2_5I2R4Entropy_sound_oai : CB1_2_5I2R4Entropy.Encloses (Foundation.finiteEntropy CB1_2_5I2R4Value) := by
  exact contains_sound (entropyFin_enclosed 6 CB1_2_5I2R4Value CB1_2_5I2R4Terms CB1_2_5I2R4Terms_sound) (by decide +kernel)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R4Entropy_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB1_2_5I2R4Entropy_sound_oai
