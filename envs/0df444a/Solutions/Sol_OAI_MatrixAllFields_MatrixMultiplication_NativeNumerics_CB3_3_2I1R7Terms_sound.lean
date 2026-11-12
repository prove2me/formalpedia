-- Prove2me | solution 1 for OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R7Terms_sound
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T14:28:25.315544+00:00
-- url     : https://prove2.me/submissions/7537e4b6-18e8-4a2b-9e86-f57eb9f4ebab

import Mathlib
import Definitions.Def_OAIQ254M010
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldCertificates_Replay_contains_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_AllFieldInitialEntropyCertificate_logTwoBall_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_CompactCertificate_entropyLookup_sound
import Theorems.Thm_OAI_MatrixAllFields_MatrixMultiplication_NativeNumerics_CB3_3_2I1R7Raw_sound

section
-- module Solutions.OAIQ254_MF.MatrixFields_CapacityB_CapB3_3_2I1
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
lemma CB3_3_2I1R7Certificates_valid :
    CB3_3_2I1R7Certificates.all (fun c => c.check logTwoBall) = true := by decide +kernel
lemma CB3_3_2I1R7P_check : ∀ a : Fin 6, contains (CB3_3_2I1R7Raw a) (CB3_3_2I1R7P a) = true := by
  decide +kernel
lemma CB3_3_2I1R7P_sound (a : Fin 6) :
    (CB3_3_2I1R7P a).Encloses (CB3_3_2I1R7Value a) :=
  contains_sound (CB3_3_2I1R7Raw_sound a) (CB3_3_2I1R7P_check a)
lemma CB3_3_2I1R7Terms_sound_oai (a : Fin 6) :
    (CB3_3_2I1R7Terms a).Encloses (Foundation.entropyTerm (CB3_3_2I1R7Value a)) :=
  CompactCertificate.entropyLookup_sound logTwoBall_sound CB3_3_2I1R7Certificates_valid
    (CB3_3_2I1R7CertificateIndex a) (CB3_3_2I1R7P_sound a)

end MatrixMultiplication.NativeNumerics

end
end

end MatrixAllFields

end OAI
end

theorem solution : type_of% @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R7Terms_sound_oai := @OAI.MatrixAllFields.MatrixMultiplication.NativeNumerics.CB3_3_2I1R7Terms_sound_oai
