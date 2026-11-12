-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R8Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:42:29.114557+00:00
-- url     : https://prove2.me/submissions/7f6df39b-33b9-40a8-befd-5f7f4f1f8270

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB4_1_3I2R8P_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB4_1_3I2
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
lemma CB4_1_3I2R8Certificates_valid :
    CB4_1_3I2R8Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB4_1_3I2R8Terms_sound_oai (a : Fin 6) :
    (CB4_1_3I2R8Terms a).Encloses (Foundation.entropyTerm (CB4_1_3I2R8Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB4_1_3I2R8Certificates_valid
    (CB4_1_3I2R8CertificateIndex a) (CB4_1_3I2R8P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R8Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB4_1_3I2R8Terms_sound_oai
